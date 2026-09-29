package main

import (
	"context"
	cryptorand "crypto/rand"
	"crypto/sha256"
	"database/sql"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"html"
	"math"
	"math/rand"
	"mime"
	"net/http"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"unicode"
	"unicode/utf8"

	"github.com/mdp/qrterminal"
	goqr "github.com/skip2/go-qrcode"
	"golang.org/x/text/unicode/norm"

	"bytes"

	"go.mau.fi/whatsmeow"
	"go.mau.fi/whatsmeow/appstate"
	waProto "go.mau.fi/whatsmeow/binary/proto"
	"go.mau.fi/whatsmeow/proto/waCommon"
	"go.mau.fi/whatsmeow/proto/waCompanionReg"
	"go.mau.fi/whatsmeow/proto/waHistorySync"
	"go.mau.fi/whatsmeow/proto/waMmsRetry"
	"go.mau.fi/whatsmeow/proto/waWeb"
	"go.mau.fi/whatsmeow/store"
	"go.mau.fi/whatsmeow/store/sqlstore"
	"go.mau.fi/whatsmeow/types"
	"go.mau.fi/whatsmeow/types/events"
	waLog "go.mau.fi/whatsmeow/util/log"
	"google.golang.org/protobuf/proto"
)

// qrState holds the latest QR code PNG in memory so /qr can serve it.
var qrState struct {
	sync.RWMutex
	png       []byte // nil = not waiting for QR (already authenticated or not yet started)
	connected bool
}

// watchdogDecision represents the decision the watchdog makes about reconnection.
type watchdogDecision string

const (
	watchdogNone      watchdogDecision = "none"
	watchdogReconnect watchdogDecision = "reconnect"
	watchdogLoggedOut watchdogDecision = "logged-out"
)

// watchdogState holds the watchdog's runtime state (protected by mutex).
var watchdogState struct {
	sync.RWMutex
	lastActionAt          time.Time        // RFC3339 formatted in JSON
	lastAction            watchdogDecision // "none", "reconnect", or "logged-out"
	reconnects            int              // count of reconnection attempts
	disconnectedTicks     int              // consecutive ticks with no connection
	loggedOutWarnTick     int              // tick counter for logged-out warning rate-limiting
	upstartTime           time.Time        // when the bridge started
	lastSuccessfulConnect time.Time        // last time client.IsConnected() returned true
	// lastTickAt and effectiveInterval make the watchdog itself observable. A
	// healthy watchdog only logs when it acts, so a running one and a dead one
	// look identical from outside — the same blindness this endpoint exists to
	// remove, one level up. effectiveInterval is the value the loop actually
	// resolved at startup, not a re-read of the environment: reporting a number
	// the loop is not using would be worse than reporting none.
	lastTickAt        time.Time
	effectiveInterval int
}

// lastEventAtNanos stores the unix nanoseconds of the last event (any type).
// Written by the event handler (callback), read by the HTTP status handler.
var lastEventAtNanos atomic.Int64

// handleStatus returns the handler for GET /api/status.
//
// Named factory, not an inline closure, for one reason: a closure registered
// straight into the mux is unreachable from a test, and the first version of
// this endpoint had a "test" that re-implemented the handler inside itself and
// asserted against its own copy — it passed with the real handler returning 503.
//
// Always answers 200 while the process is up, even disconnected or logged out.
// The HTTP status separates "process reachable" from "WhatsApp usable"; folding
// them together would make connection-refused indistinguishable from a live but
// logged-out bridge, which are different problems with different fixes.
func handleStatus(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		w.Header().Set("Content-Type", "application/json")

		connected := false
		loggedIn := false
		jid := ""
		lastSuccessfulConnect := time.Time{}
		autoReconnectErrors := 0

		if client != nil {
			connected = client.IsConnected()
			if client.Store != nil && client.Store.ID != nil {
				loggedIn = true
				jid = client.Store.ID.String()
			}
			lastSuccessfulConnect = client.LastSuccessfulConnect
			autoReconnectErrors = client.AutoReconnectErrors
		}

		healthy, reason := evaluateHealth(connected, loggedIn)

		// Get watchdog state
		watchdogState.RLock()
		// Reports what the loop resolved at startup. Zero means the loop has not
		// started yet, and 60 is the same default it would have picked.
		watchdogInterval := watchdogState.effectiveInterval
		if watchdogInterval == 0 {
			watchdogInterval = 60
		}
		watchdogStatus := WatchdogStatus{
			IntervalSeconds: watchdogInterval,
			Reconnects:      watchdogState.reconnects,
		}
		if watchdogState.lastAction != watchdogNone && !watchdogState.lastActionAt.IsZero() {
			watchdogStatus.LastAction = string(watchdogState.lastAction)
			watchdogStatus.LastActionAt = watchdogState.lastActionAt.Format(time.RFC3339)
		}
		if !watchdogState.lastTickAt.IsZero() {
			watchdogStatus.LastTickAt = watchdogState.lastTickAt.Format(time.RFC3339)
		}
		upstartTime := watchdogState.upstartTime
		watchdogState.RUnlock()

		// Calculate uptime
		uptime := int64(0)
		if !upstartTime.IsZero() {
			uptime = int64(time.Since(upstartTime).Seconds())
		}

		// Format optional fields only if they have meaningful values
		resp := StatusResponse{
			Success:             true,
			Healthy:             healthy,
			Reason:              reason,
			Connected:           connected,
			LoggedIn:            loggedIn,
			JID:                 jid,
			AutoReconnectErrors: autoReconnectErrors,
			UptimeSeconds:       uptime,
			Watchdog:            watchdogStatus,
		}

		// Only include LastSuccessfulConnect if non-zero
		if !lastSuccessfulConnect.IsZero() {
			resp.LastSuccessfulConnect = lastSuccessfulConnect.Format(time.RFC3339)
		}

		// Only include LastEventAt if non-zero
		nanos := lastEventAtNanos.Load()
		if nanos > 0 {
			resp.LastEventAt = time.Unix(0, nanos).Format(time.RFC3339)
		}

		json.NewEncoder(w).Encode(resp)
	}
}

// evaluateHealth decides the single boolean a monitor reads, plus the reason.
// Pure function so the decision is testable without a client.
func evaluateHealth(connected, loggedIn bool) (healthy bool, reason string) {
	// Table from contracts.md:
	// connected | loggedIn | healthy | reason
	// true      | true     | true    | ""
	// false     | true     | false   | "disconnected from WhatsApp"
	// true      | false    | false   | "not logged in — scan the QR code at /qr"
	// false     | false    | false   | "not logged in — scan the QR code at /qr"

	if connected && loggedIn {
		return true, ""
	}
	// Deslogado (not logged in) takes priority over desconectado (disconnected)
	// because it's the actionable state.
	if !loggedIn {
		return false, "not logged in — scan the QR code at /qr"
	}
	// connected=false, loggedIn=true
	return false, "disconnected from WhatsApp"
}

// decideWatchdogAction is the whole policy of what to do on each tick.
// Pure function so it can be tested without a live client.
func decideWatchdogAction(connected, loggedIn bool) watchdogDecision {
	// Table from contracts.md:
	// connected | loggedIn | decisão | por quê
	// true      | true     | none    | nada a fazer
	// true      | false    | logged-out  | conectado sem sessão: só QR resolve
	// false     | false    | logged-out  | autoReconnect da lib nem tenta com Store.ID == nil
	// false     | true     | reconnect   | é o único caso em que reconectar tem chance

	if connected && loggedIn {
		return watchdogNone
	}
	if !loggedIn {
		return watchdogLoggedOut
	}
	// connected=false, loggedIn=true
	return watchdogReconnect
}

// Message represents a chat message for our client
type Message struct {
	Time      time.Time
	Sender    string
	Content   string
	IsFromMe  bool
	MediaType string
	Filename  string
}

// Database handler for storing message history
type MessageStore struct {
	db *sql.DB
}

// Initialize message store
func NewMessageStore() (*MessageStore, error) {
	// Create directory for database if it doesn't exist
	if err := os.MkdirAll("store", 0755); err != nil {
		return nil, fmt.Errorf("failed to create store directory: %v", err)
	}

	// Open SQLite database for messages
	db, err := openMessagesDB()
	if err != nil {
		return nil, fmt.Errorf("failed to open message database: %v", err)
	}

	// Create tables if they don't exist
	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS chats (
			jid TEXT PRIMARY KEY,
			name TEXT,
			last_message_time TIMESTAMP
		);
		
		CREATE TABLE IF NOT EXISTS messages (
			id TEXT,
			chat_jid TEXT,
			sender TEXT,
			content TEXT,
			timestamp TIMESTAMP,
			is_from_me BOOLEAN,
			media_type TEXT,
			filename TEXT,
			url TEXT,
			media_key BLOB,
			file_sha256 BLOB,
			file_enc_sha256 BLOB,
			file_length INTEGER,
			sender_jid TEXT,
			quoted_message_id TEXT,
			quoted_sender TEXT,
			quoted_content TEXT,
			mentions TEXT,
			revoked_at TIMESTAMP,
			edited_at TIMESTAMP,
			previous_content TEXT,
			PRIMARY KEY (id, chat_jid),
			FOREIGN KEY (chat_jid) REFERENCES chats(jid)
		);

		CREATE TABLE IF NOT EXISTS senders (
			jid TEXT PRIMARY KEY,
			push_name TEXT,
			full_name TEXT,
			first_name TEXT,
			business_name TEXT,
			updated_at TIMESTAMP
		);
		CREATE INDEX IF NOT EXISTS idx_senders_names ON senders(full_name, push_name);

		-- The primary key is (id, chat_jid): perfect for fetching one message by
		-- id, useless for what the product actually does, which is filter by
		-- conversation and order by time. Without this index every read of a chat
		-- scans the whole table and sorts in a temp B-tree.
		-- Measured on 113k messages: last 20 of a chat 28.3ms -> 0.1ms, text
		-- search scoped to one chat 29.4ms -> 2.9ms (the unaccent() callback stops
		-- running over every row in the database), and the last-message-per-chat
		-- aggregation 78.8ms -> 19.2ms via a covering index.
		CREATE INDEX IF NOT EXISTS idx_messages_chat_time ON messages(chat_jid, timestamp);

		-- Partial on purpose: this is exactly the question the transcription sweep
		-- asks every run, and indexing only the pending rows keeps it tiny
		-- (26.8ms -> 0.2ms on the same database) instead of covering 113k rows to
		-- answer for a few thousand.
		CREATE INDEX IF NOT EXISTS idx_messages_audio_pending ON messages(chat_jid)
			WHERE media_type = 'audio' AND (content IS NULL OR content = '');

		-- Gap #11: polls and votes (T001)
		CREATE TABLE IF NOT EXISTS polls (
			id TEXT,
			chat_jid TEXT,
			sender TEXT,
			name TEXT,
			options TEXT,
			selectable_count INTEGER,
			timestamp TIMESTAMP,
			PRIMARY KEY (id, chat_jid),
			FOREIGN KEY (chat_jid) REFERENCES chats(jid)
		);

		CREATE TABLE IF NOT EXISTS poll_votes (
			poll_id TEXT,
			chat_jid TEXT,
			voter_jid TEXT,
			selected TEXT,
			resolved INTEGER NOT NULL DEFAULT 1,
			timestamp TIMESTAMP,
			PRIMARY KEY (poll_id, chat_jid, voter_jid)
		);

		CREATE INDEX IF NOT EXISTS idx_poll_votes_poll ON poll_votes(poll_id, chat_jid);
	`)
	if err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to create tables: %v", err)
	}

	// D8/D15: CREATE TABLE IF NOT EXISTS above does not add a column to a
	// messages table that already exists — and the store in use predates
	// sender_jid/quoted_*/mentions (128k+ rows). Without this, the bridge
	// starts against that database and breaks on the first query touching a
	// column that was never added.
	if err := ensureMessagesSchema(db); err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to migrate messages schema: %v", err)
	}

	return &MessageStore{db: db}, nil
}

// ensureMessagesSchema adds to an existing messages table the columns
// introduced after the CREATE TABLE block above (sender_jid, quoted_message_id,
// quoted_sender, quoted_content, mentions, revoked_at, edited_at, previous_content),
// for databases that were created before those columns existed. Idempotent: reads the table's current columns
// via PRAGMA table_info and only emits ALTER TABLE ADD COLUMN for the ones
// still missing, so running it again (or against a brand-new database that
// already has them from CREATE TABLE) is a no-op.
func ensureMessagesSchema(db *sql.DB) error {
	rows, err := db.Query("PRAGMA table_info(messages)")
	if err != nil {
		return fmt.Errorf("failed to read messages table info: %v", err)
	}
	existing := make(map[string]bool)
	for rows.Next() {
		var cid int
		var name, colType string
		var notNull int
		var dfltValue sql.NullString
		var pk int
		if err := rows.Scan(&cid, &name, &colType, &notNull, &dfltValue, &pk); err != nil {
			rows.Close()
			return fmt.Errorf("failed to scan messages table info: %v", err)
		}
		existing[name] = true
	}
	if err := rows.Err(); err != nil {
		rows.Close()
		return fmt.Errorf("failed to read messages table info: %v", err)
	}
	rows.Close()

	for _, col := range []string{"sender_jid", "quoted_message_id", "quoted_sender", "quoted_content", "mentions", "revoked_at", "edited_at", "previous_content"} {
		if existing[col] {
			continue
		}
		if _, err := db.Exec(fmt.Sprintf("ALTER TABLE messages ADD COLUMN %s TEXT", col)); err != nil {
			return fmt.Errorf("failed to add column %s to messages: %v", col, err)
		}
	}
	return nil
}

// Close the database connection
func (store *MessageStore) Close() error {
	return store.db.Close()
}

// TouchChatLastMessageTime updates only last_message_time on an existing chat row.
func (store *MessageStore) TouchChatLastMessageTime(jid string, lastMessageTime time.Time) error {
	_, err := store.db.Exec(
		"UPDATE chats SET last_message_time = ? WHERE jid = ?",
		lastMessageTime, jid,
	)
	return err
}

// EnsureChat creates a chat row if none exists, leaving any existing row untouched.
// Required before StoreMessage in the outbound path to satisfy the FOREIGN KEY constraint.
func (store *MessageStore) EnsureChat(jid string, lastMessageTime time.Time) error {
	_, err := store.db.Exec(
		"INSERT OR IGNORE INTO chats (jid, name, last_message_time) VALUES (?, '', ?)",
		jid, lastMessageTime,
	)
	return err
}

// StoreSender upserts a sender row, preserving existing non-empty fields.
func (store *MessageStore) StoreSender(jid, pushName, fullName, firstName, businessName string) error {
	if jid == "" {
		return nil
	}
	_, err := store.db.Exec(`
		INSERT INTO senders (jid, push_name, full_name, first_name, business_name, updated_at)
		VALUES (?, ?, ?, ?, ?, ?)
		ON CONFLICT(jid) DO UPDATE SET
			push_name     = COALESCE(NULLIF(excluded.push_name, ''),     senders.push_name),
			full_name     = COALESCE(NULLIF(excluded.full_name, ''),     senders.full_name),
			first_name    = COALESCE(NULLIF(excluded.first_name, ''),    senders.first_name),
			business_name = COALESCE(NULLIF(excluded.business_name, ''), senders.business_name),
			updated_at    = excluded.updated_at
	`, jid, pushName, fullName, firstName, businessName, time.Now())
	return err
}

// ResolveName returns the best human-readable name for a JID from the senders table.
func (store *MessageStore) ResolveName(jid string) string {
	var fullName, businessName, pushName sql.NullString
	err := store.db.QueryRow(
		"SELECT full_name, business_name, push_name FROM senders WHERE jid = ?", jid,
	).Scan(&fullName, &businessName, &pushName)
	if err != nil {
		return ""
	}
	if fullName.Valid && fullName.String != "" {
		return fullName.String
	}
	if businessName.Valid && businessName.String != "" {
		return businessName.String
	}
	if pushName.Valid && pushName.String != "" {
		return pushName.String
	}
	return ""
}

// SyncAllContacts pulls the full whatsmeow contact store into the senders table.
func SyncAllContacts(client *whatsmeow.Client, store *MessageStore, logger waLog.Logger) {
	if client == nil || client.Store == nil || client.Store.Contacts == nil {
		return
	}
	contacts, err := client.Store.Contacts.GetAllContacts(context.Background())
	if err != nil {
		logger.Warnf("Failed to sync contacts: %v", err)
		return
	}
	count := 0
	for jid, info := range contacts {
		if err := store.StoreSender(jid.String(), info.PushName, info.FullName, info.FirstName, info.BusinessName); err == nil {
			count++
		}
	}
	logger.Infof("Synced %d contacts into senders table", count)
}

// Store a chat in the database
func (store *MessageStore) StoreChat(jid, name string, lastMessageTime time.Time) error {
	_, err := store.db.Exec(
		"INSERT OR REPLACE INTO chats (jid, name, last_message_time) VALUES (?, ?, ?)",
		jid, name, lastMessageTime,
	)
	return err
}

// Store a message in the database
func (store *MessageStore) StoreMessage(id, chatJID, sender, content string, timestamp time.Time, isFromMe bool,
	mediaType, filename, url string, mediaKey, fileSHA256, fileEncSHA256 []byte, fileLength uint64) error {
	// Only store if there's actual content or media
	if content == "" && mediaType == "" {
		return nil
	}

	// Incoming content is empty (the common re-sync-of-audio case the
	// COALESCE below exists for) — check if we're about to preserve a
	// non-empty value someone already wrote (typically a transcription), so
	// it's not a completely silent transition if this protection ever
	// actually fires. Single extra SELECT, only on this narrow path (not
	// every write) since it only matters when there's something to protect.
	if content == "" {
		var existing sql.NullString
		if err := store.db.QueryRow("SELECT content FROM messages WHERE id = ? AND chat_jid = ?", id, chatJID).Scan(&existing); err == nil && existing.Valid && existing.String != "" {
			fmt.Printf("StoreMessage: preserving existing content for %s in %s against incoming empty value\n", id, chatJID)
		}
	}

	// ON CONFLICT + COALESCE(NULLIF(...)) instead of INSERT OR REPLACE: a
	// re-sync (re-pairing, on-demand history sync) re-delivers messages with
	// their original raw content — for audio that's '', since transcription
	// is a local enrichment the server doesn't know about. A blind REPLACE
	// would blow away an existing transcription with that empty string. This
	// keeps whichever content is already there when the incoming value is
	// empty, same pattern as StoreSender below.
	//
	// The WHERE on the DO UPDATE keeps a revoked row revoked (issue #21): a
	// re-delivery of the original must not bring back what the sender deleted.
	//
	// media_key/file_sha256/file_enc_sha256 need the same treatment, but as
	// BLOB columns NULLIF(x, '') does NOT catch an empty []byte the way it
	// catches an empty TEXT — '' there is compared as TEXT and never equals a
	// zero-length BLOB, so the NULLIF guard would silently no-op and always
	// take the incoming (possibly empty) value. Verified empirically before
	// writing this. Use length(...) instead, which works for BLOB.
	_, err := store.db.Exec(
		`INSERT INTO messages
		(id, chat_jid, sender, content, timestamp, is_from_me, media_type, filename, url, media_key, file_sha256, file_enc_sha256, file_length)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
		ON CONFLICT(id, chat_jid) DO UPDATE SET
			sender          = excluded.sender,
			content         = COALESCE(NULLIF(excluded.content, ''), messages.content),
			timestamp       = excluded.timestamp,
			is_from_me      = excluded.is_from_me,
			media_type      = excluded.media_type,
			filename        = excluded.filename,
			url             = excluded.url,
			media_key       = CASE WHEN length(excluded.media_key)       > 0 THEN excluded.media_key       ELSE messages.media_key       END,
			file_sha256     = CASE WHEN length(excluded.file_sha256)     > 0 THEN excluded.file_sha256     ELSE messages.file_sha256     END,
			file_enc_sha256 = CASE WHEN length(excluded.file_enc_sha256) > 0 THEN excluded.file_enc_sha256 ELSE messages.file_enc_sha256 END,
			file_length     = excluded.file_length
		WHERE messages.revoked_at IS NULL`,
		id, chatJID, sender, content, timestamp, isFromMe, mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength,
	)
	return err
}

// StoreMessageSenderJID persists the full JID of the message author (D8) in
// its own dedicated column, by a path separate from StoreMessage: that
// function's signature and its COALESCE(NULLIF(...)) content-preservation
// semantics (the guard against a re-sync blowing away a transcription) are
// not touched. An empty senderJID is a no-op — nothing new to record, and the
// row's existing sender_jid (if any) is left as it is.
func (store *MessageStore) StoreMessageSenderJID(id, chatJID, senderJID string) error {
	if senderJID == "" {
		return nil
	}
	_, err := store.db.Exec(
		"UPDATE messages SET sender_jid = ? WHERE id = ? AND chat_jid = ?",
		senderJID, id, chatJID,
	)
	return err
}

// StoreMessageContext persists the ContextInfo a received message carries
// (D1, D13): the id/author/content it quotes, and who it mentions. Own write
// path, same reasoning as StoreMessageSenderJID — StoreMessage's signature and
// COALESCE(NULLIF(...)) semantics are not touched. ci == nil is a no-op: no
// UPDATE is issued, so a plain message (Conversation, no ContextInfo) never
// pays for this write. mentions is stored as NULL (not "[]" or "") when the
// message mentions no one, per contract.
func (store *MessageStore) StoreMessageContext(id, chatJID string, ci *waProto.ContextInfo) error {
	if ci == nil {
		return nil
	}
	quotedMessageID := ci.GetStanzaID()
	quotedSender := ci.GetParticipant()
	quotedContent := extractTextContent(ci.GetQuotedMessage())

	var mentionsJSON interface{}
	if mentioned := ci.GetMentionedJID(); len(mentioned) > 0 {
		b, err := json.Marshal(mentioned)
		if err != nil {
			return err
		}
		mentionsJSON = string(b)
	}

	_, err := store.db.Exec(
		"UPDATE messages SET quoted_message_id = ?, quoted_sender = ?, quoted_content = ?, mentions = ? WHERE id = ? AND chat_jid = ?",
		nullIfEmpty(quotedMessageID), nullIfEmpty(quotedSender), nullIfEmpty(quotedContent), mentionsJSON, id, chatJID,
	)
	return err
}

// nullIfEmpty maps an empty string to a SQL NULL parameter, so an absent value
// is stored as NULL instead of as an empty TEXT — used by StoreMessageContext.
func nullIfEmpty(s string) interface{} {
	if s == "" {
		return nil
	}
	return s
}

// MarkMessageRevoked records that the message (id, chat_jid) was deleted for
// everyone (issue #21). Soft delete (2026-09-24, D1): what the sender took
// back is no longer erased — content, media reference and keys, and the
// quoted/mentions context all stay in the row, and the cached file on disk is
// left alone too. Only revoked_at is stamped; every normal read path hides
// what's behind it (applyMessageFlags, the search filter, the last_message
// CASE), and D3's explicit get_deleted_message tool is the one place that
// still reads it. Returns whether a row that was not already revoked
// matched — a revoke for a message this store never saw is a no-op, not an
// error.
func (store *MessageStore) MarkMessageRevoked(id, chatJID string, revokedAt time.Time) (found bool, err error) {
	res, err := store.db.Exec(
		"UPDATE messages SET revoked_at = ? WHERE id = ? AND chat_jid = ? AND revoked_at IS NULL",
		revokedAt, id, chatJID,
	)
	if err != nil {
		return false, err
	}
	n, err := res.RowsAffected()
	if err != nil {
		return false, err
	}
	return n > 0, nil
}

// StoreRevokedTombstone leaves a placeholder row for a history-sync REVOKE
// stub whose target this store never saw (D2, issue #23) — a fresh database,
// or the message simply never having reached this store. Same shape a live
// revoke leaves behind (empty content, revoked_at set), so the conversation
// keeps the gap instead of silently missing the message. ON CONFLICT DO
// NOTHING makes this a no-op when the row already exists — that case is
// handled by MarkMessageRevoked (via applyProtocolMessage) instead.
func (store *MessageStore) StoreRevokedTombstone(id, chatJID, sender string, revokedAt time.Time, isFromMe bool) error {
	_, err := store.db.Exec(
		`INSERT INTO messages (id, chat_jid, sender, content, timestamp, is_from_me, revoked_at)
		VALUES (?, ?, ?, '', ?, ?, ?)
		ON CONFLICT(id, chat_jid) DO NOTHING`,
		id, chatJID, sender, revokedAt, isFromMe, revokedAt,
	)
	return err
}

// ApplyMessageEdit replaces the content of (id, chat_jid) with the edited
// text and stamps edited_at (issue #21). A revoked row is not touched, and an
// empty newContent is a no-op — an edit never blanks a message. D4 (soft
// delete, 2026-09-24): before the swap, previous_content is set to the
// content this row already had — but only the first time (COALESCE), so a
// second and later edit does not overwrite the original with an
// intermediate edit; get_deleted_message (D3) is the only place that reads it.
func (store *MessageStore) ApplyMessageEdit(id, chatJID, newContent string, editedAt time.Time) (bool, error) {
	if newContent == "" {
		return false, nil
	}
	res, err := store.db.Exec(
		"UPDATE messages SET previous_content = COALESCE(previous_content, content), content = ?, edited_at = ? WHERE id = ? AND chat_jid = ? AND revoked_at IS NULL",
		newContent, editedAt, id, chatJID,
	)
	if err != nil {
		return false, err
	}
	n, err := res.RowsAffected()
	return n > 0, err
}

// IsMessageRevoked reports whether (id, chat_jid) was deleted for everyone.
func (store *MessageStore) IsMessageRevoked(id, chatJID string) (bool, error) {
	var revoked bool
	err := store.db.QueryRow(
		"SELECT revoked_at IS NOT NULL FROM messages WHERE id = ? AND chat_jid = ?",
		id, chatJID,
	).Scan(&revoked)
	if err == sql.ErrNoRows {
		return false, nil
	}
	return revoked, err
}

// applyProtocolMessage handles the ProtocolMessage types that change a message
// already in the store (issue #21): REVOKE (deleted for everyone) and
// MESSAGE_EDIT. The target is Key.ID scoped to the chat the event arrived in,
// so a protocol message can only touch a message of its own conversation.
// Returns true when pm was one of those types — the caller then stops, since
// the event carries no message of its own to store.
func applyProtocolMessage(messageStore *MessageStore, chatJID string, pm *waProto.ProtocolMessage, at time.Time, logger waLog.Logger) bool {
	if pm == nil {
		return false
	}
	targetID := pm.GetKey().GetID()
	switch pm.GetType() {
	case waProto.ProtocolMessage_REVOKE:
		if targetID == "" {
			return true
		}
		found, err := messageStore.MarkMessageRevoked(targetID, chatJID, at)
		if err != nil {
			logger.Warnf("Failed to mark message %s as revoked: %v", targetID, err)
			return true
		}
		// D1 (soft delete, 2026-09-24): the cached file on disk is left alone —
		// no os.Remove here anymore. It's what get_deleted_message's
		// download=true (task 3) serves back.
		if found {
			fmt.Printf("[%s] message %s in %s was deleted by the sender\n", at.Format("2006-01-02 15:04:05"), targetID, chatJID)
		}
		return true
	case waProto.ProtocolMessage_MESSAGE_EDIT:
		if targetID == "" {
			return true
		}
		if _, err := messageStore.ApplyMessageEdit(targetID, chatJID, extractTextContent(pm.GetEditedMessage()), at); err != nil {
			logger.Warnf("Failed to apply edit to message %s: %v", targetID, err)
		}
		return true
	}
	return false
}

// GetMessageForQuote looks up a message to quote by (id, chat_jid), scoped to
// the destination chat exactly as the sender will resolve it. Scoping by
// chat_jid does double duty: an id that exists only in a different chat comes
// back as sql.ErrNoRows too, same as an id that doesn't exist anywhere — both
// are "not found for this chat", which is the refusal in effect either way
// (D12, and the mismatched-chat refusal). senderJID/sender are returned as
// stored (possibly empty), for the caller to apply the D9 unknown-author check.
// revoked reports whether the row is soft-deleted (D2): this method also
// backs resolveActionParticipant (task 6), which must keep resolving the
// author of a since-revoked message for react/revoke — the refusal on a
// revoked target belongs only to the citation caller (buildQuoteContextInfo),
// which checks this return itself.
func (store *MessageStore) GetMessageForQuote(id, chatJID string) (senderJID, sender, content string, revoked bool, err error) {
	var senderJIDNull, senderNull, contentNull sql.NullString
	err = store.db.QueryRow(
		"SELECT sender_jid, sender, content, revoked_at IS NOT NULL FROM messages WHERE id = ? AND chat_jid = ?",
		id, chatJID,
	).Scan(&senderJIDNull, &senderNull, &contentNull, &revoked)
	if err != nil {
		return "", "", "", false, err
	}
	return senderJIDNull.String, senderNull.String, contentNull.String, revoked, nil
}

// Get messages from a chat
func (store *MessageStore) GetMessages(chatJID string, limit int) ([]Message, error) {
	rows, err := store.db.Query(
		"SELECT sender, content, timestamp, is_from_me, media_type, filename FROM messages WHERE chat_jid = ? ORDER BY timestamp DESC LIMIT ?",
		chatJID, limit,
	)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	var messages []Message
	for rows.Next() {
		var msg Message
		var timestamp time.Time
		err := rows.Scan(&msg.Sender, &msg.Content, &timestamp, &msg.IsFromMe, &msg.MediaType, &msg.Filename)
		if err != nil {
			return nil, err
		}
		msg.Time = timestamp
		messages = append(messages, msg)
	}

	return messages, nil
}

// Get all chats
func (store *MessageStore) GetChats() (map[string]time.Time, error) {
	rows, err := store.db.Query("SELECT jid, last_message_time FROM chats ORDER BY last_message_time DESC")
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	chats := make(map[string]time.Time)
	for rows.Next() {
		var jid string
		var lastMessageTime time.Time
		err := rows.Scan(&jid, &lastMessageTime)
		if err != nil {
			return nil, err
		}
		chats[jid] = lastMessageTime
	}

	return chats, nil
}

// Extract text content from a message
func extractTextContent(msg *waProto.Message) string {
	if msg == nil {
		return ""
	}

	// Try to get text content
	if text := msg.GetConversation(); text != "" {
		return text
	} else if extendedText := msg.GetExtendedTextMessage(); extendedText != nil {
		return extendedText.GetText()
	}

	// Media messages can carry a text caption that should be searchable
	if img := msg.GetImageMessage(); img != nil {
		return img.GetCaption()
	} else if video := msg.GetVideoMessage(); video != nil {
		return video.GetCaption()
	} else if doc := msg.GetDocumentMessage(); doc != nil {
		return doc.GetCaption()
	}

	return ""
}

// extractContextInfo returns the first non-nil ContextInfo carried by msg,
// checked in this order: ExtendedTextMessage, ImageMessage, VideoMessage,
// AudioMessage, DocumentMessage, StickerMessage, ContactMessage,
// LocationMessage, PollCreationMessage. Plain text arrives as Conversation,
// which is a bare string and never has a ContextInfo — that absence is what
// tells a reply apart from a regular message (D1, D13, D14). Nil-safe: every
// generated Get* is itself nil-safe, so a nil msg or a message of a type not
// in this list returns nil without a type check.
func extractContextInfo(msg *waProto.Message) *waProto.ContextInfo {
	if msg == nil {
		return nil
	}
	if ci := msg.GetExtendedTextMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetImageMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetVideoMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetAudioMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetDocumentMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetStickerMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetContactMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetLocationMessage().GetContextInfo(); ci != nil {
		return ci
	}
	if ci := msg.GetPollCreationMessage().GetContextInfo(); ci != nil {
		return ci
	}
	return nil
}

// WatchdogStatus represents the state of the automatic reconnection watchdog.
type WatchdogStatus struct {
	IntervalSeconds int    `json:"interval_seconds"`
	Reconnects      int    `json:"reconnects"`
	LastAction      string `json:"last_action,omitempty"`    // "none" | "reconnect" | "logged-out"
	LastActionAt    string `json:"last_action_at,omitempty"` // RFC3339
	// LastTickAt is how a caller tells a live watchdog from a dead one: it must
	// keep advancing by roughly IntervalSeconds. Empty means it has not ticked
	// yet — expected right after startup, suspicious any later.
	LastTickAt string `json:"last_tick_at,omitempty"` // RFC3339
}

// StatusResponse represents the response for GET /api/status.
type StatusResponse struct {
	Success               bool           `json:"success"`
	Healthy               bool           `json:"healthy"`
	Reason                string         `json:"reason,omitempty"`
	Connected             bool           `json:"connected"`
	LoggedIn              bool           `json:"logged_in"`
	JID                   string         `json:"jid,omitempty"`
	LastSuccessfulConnect string         `json:"last_successful_connect,omitempty"` // RFC3339
	AutoReconnectErrors   int            `json:"auto_reconnect_errors"`
	LastEventAt           string         `json:"last_event_at,omitempty"` // RFC3339
	UptimeSeconds         int64          `json:"uptime_seconds"`
	Watchdog              WatchdogStatus `json:"watchdog"`
}

// SendMessageResponse represents the response for the send message API
type SendMessageResponse struct {
	Success bool   `json:"success"`
	Message string `json:"message"`
	// Candidates carries the ambiguous-mention refusal body (D6): populated
	// only when Success is false because a name in the request's mentions
	// matched more than one chat participant. Never a number or JID.
	Candidates []MentionCandidateResponse `json:"candidates,omitempty"`
}

// SendMessageRequest represents the request body for the send message API
type SendMessageRequest struct {
	Recipient       string `json:"recipient"`
	Message         string `json:"message"`
	MediaPath       string `json:"media_path,omitempty"`
	QuotedMessageID string `json:"quoted_message_id,omitempty"`
	// Mentions are NAMES, never a number or JID (D3) — matched against the
	// destination chat's participants (D5) and substituted into the text as
	// "@<number>" (D4). "ref:<opaque>" resolves a prior ambiguous-mention
	// refusal's candidate (D6).
	Mentions []string `json:"mentions,omitempty"`
}

// unknownAuthorMessage is the D9 refusal text: a message's author isn't
// resolvable — sender_jid was never recorded, or sender is the chat's own
// user part (the D8 group-JID-as-author gap: 9,433 messages where the group
// JID got written as the author instead of a real participant). Shared,
// verbatim, by buildQuoteContextInfo's citation refusal and
// resolveActionParticipant's react/revoke third-party-in-group refusal
// (task 6) — same judgment, same words.
const unknownAuthorMessage = "message's author is unknown for that part of the history (recorded before this was tracked) — messages from now on keep it"

// isUnknownAuthor is the D9 judgment, shared by buildQuoteContextInfo (task 4)
// and resolveActionParticipant (task 6): true when a message's stored author
// can't be trusted as a real participant — sender_jid empty, or sender equal
// to the chat's own user part (D8).
func isUnknownAuthor(senderJID, sender, chatJID string) bool {
	// No full JID recorded: there is no Participant to quote as, in any chat.
	if senderJID == "" {
		return true
	}
	// Only in a GROUP does `sender == chat` mean the author was lost: those are
	// the 9,433 rows (D8) where the group's own JID got written as the author.
	// In a 1:1 the two are equal for EVERY message — the chat IS the person —
	// so applying the heuristic there refused every legitimate quote in a
	// direct conversation. Found in production on 2026-09-09.
	if !strings.HasSuffix(chatJID, "@g.us") {
		return false
	}
	chatUser := chatJID
	if idx := strings.Index(chatJID, "@"); idx >= 0 {
		chatUser = chatJID[:idx]
	}
	return sender == chatUser
}

// Function to send a WhatsApp message
// buildQuoteContextInfo resolves quotedMessageID against the message store
// and builds the ContextInfo to attach to an outbound message (D9, D10, D11,
// D12). It runs before any media upload or SendMessage call, so a refusal
// (non-empty errMsg, with the 4xx to answer with) leaves nothing sent.
func buildQuoteContextInfo(messageStore *MessageStore, quotedMessageID, chatJID string) (ctxInfo *waProto.ContextInfo, errMsg string, statusCode int) {
	if messageStore == nil {
		return nil, "quoted_message_id given but no message store is available", http.StatusInternalServerError
	}
	senderJID, sender, content, revoked, err := messageStore.GetMessageForQuote(quotedMessageID, chatJID)
	if err == sql.ErrNoRows {
		// D12 (id doesn't exist) and the mismatched-chat refusal share this
		// path: GetMessageForQuote scopes the lookup by chat_jid, so a
		// quoted_message_id that belongs to a different chat also misses here.
		return nil, "quoted_message_id not found for the destination chat", http.StatusNotFound
	}
	if err != nil {
		return nil, fmt.Sprintf("Error looking up quoted_message_id: %v", err), http.StatusInternalServerError
	}
	// D2 (soft delete): citing a revoked message would fill QuotedMessage with
	// content the sender took back — refused here, the one place this lookup
	// is used to build an outbound quote. resolveActionParticipant (task 6)
	// reuses GetMessageForQuote for react/revoke and does not apply this
	// check, on purpose.
	if revoked {
		return nil, "quoted_message_id refers to a message that was deleted by the sender", http.StatusBadRequest
	}
	if isUnknownAuthor(senderJID, sender, chatJID) {
		return nil, "quoted " + unknownAuthorMessage, http.StatusBadRequest
	}
	return &waProto.ContextInfo{
		StanzaID:    proto.String(quotedMessageID),
		Participant: proto.String(senderJID),
		// D10: always fill QuotedMessage — the library doesn't document
		// whether the recipient app needs it or StanzaID+Participant suffice,
		// and filling it costs nothing.
		QuotedMessage: &waProto.Message{Conversation: proto.String(content)},
	}, "", 0
}

// ---------------------------------------------------------------------------
// Mention resolution (task 5, D3-D7): the ponte resolves a requested @Name to
// a chat participant, substitutes "@Name" for "@<number>" in the text so
// WhatsApp actually highlights it, and never lets a phone number or JID leak
// into a request, a response, or an error message.
// ---------------------------------------------------------------------------

// mentionParticipant is one candidate for a mention target inside a chat
// (D5): the list resolveMentions matches requested names against.
//
// In a GROUP, jid is the phone-number JID (@s.whatsapp.net) whenever the server
// gives one — it keys the senders table and goes straight into
// ContextInfo.MentionedJID. Quem vem sem telefone entra com phoneUser vazio:
// presente na lista, nao mencionavel (rodada 9). In a 1:1 it is whatever
// addresses the chat, which can be an @lid when no PN mapping exists yet; mentioning
// in that case is refused rather than sent, because WhatsApp will not highlight an
// @lid and the text would carry a stranger-looking identifier (achado da rodada 5).
type mentionParticipant struct {
	jid string
	// outrasChaves sao as OUTRAS formas de endereco da mesma pessoa (@lid, e a
	// forma que o grupo devolveu), porque a tabela senders pode ter a linha sob
	// qualquer uma delas. Era um campo so, preenchido com gp.JID — que e a
	// forma PN sempre que o grupo e endereçado por telefone, ou seja, igual ao
	// jid: a busca consultava a MESMA linha duas vezes e a linha @lid nunca era
	// alcancada (achado 3 da rodada 9). gp.LID existe e e quem resolve.
	outrasChaves []string
	// phoneUser e o numero com que "@" e escrito no texto (D4). VAZIO significa
	// que esta pessoa nao pode ser mencionada — o grupo nao devolveu telefone
	// para ela. Ela continua na lista mesmo assim: o nome dela ainda precisa
	// proteger o prefixo de um nome mais curto, e ainda precisa contar na
	// ambiguidade da D6 (achado 2 da rodada 9).
	phoneUser    string
	pushName     string
	fullName     string
	firstName    string
	businessName string
}

// mentionMatch is one name match found by matchMentionName: enough to build
// either a resolvedMention (single match) or a MentionCandidateResponse
// (ambiguous match, D6) — never a phone number or JID in the latter.
type mentionMatch struct {
	jid string
	// phoneUser vazio: casou por nome, mas nao da para mencionar — o grupo nao
	// devolveu telefone para esta pessoa. Vale para a pergunta da D6, nao para
	// o envio.
	phoneUser string
	name      string
	origem    string // "agenda" (full_name/first_name) | "whatsapp" (push_name) | "negocio" (business_name)
}

// resolvedMention is one mention ready to apply to the outbound text (D4):
// every "@name" occurrence in the message is replaced with "@phoneUser", and
// jid goes into ContextInfo.MentionedJID.
type resolvedMention struct {
	name      string
	phoneUser string
	jid       string
	viaRef    bool // veio de "ref:<id>", ou seja, o usuario ja desambiguou
}

// MentionCandidateResponse is one entry of the ambiguous-mention refusal body
// (D6): an opaque ref plus the matched name and where it came from — no
// number, no JID, ever.
type MentionCandidateResponse struct {
	Ref    string `json:"ref"`
	Nome   string `json:"nome"`
	Origem string `json:"origem"`
}

// fillSenderNames looks up the participant in the senders table and fills the
// name fields mention matching (D5, D6) checks against. No row for either key
// leaves every field empty — the participant is simply unmatchable by name,
// not an error.
//
// Two keys, not one, and that is the point: senders rows are written with
// resolveToPN(msg.Info.Sender), which returns the @lid UNCHANGED when no
// PN mapping exists yet. Measured on the live personal store on 2026-09-09,
// 637 of 2518 sender rows are keyed by @lid, 587 of them carrying a name.
// Looking up only the phone form makes those people invisible to matching —
// which is worse than "cannot mention them": D6's ambiguity check counts
// candidates, so a group with two people of the same first name, one of them
// only known under @lid, would see a SINGLE match, skip the question, and
// mention the other one. Silently mentioning the wrong person is exactly
// what D6 exists to prevent.
func (store *MessageStore) fillSenderNames(p *mentionParticipant) {
	vistas := make(map[string]bool, 3)
	for _, key := range append([]string{p.jid}, p.outrasChaves...) {
		if key == "" || vistas[key] {
			continue
		}
		vistas[key] = true
		var pushName, fullName, firstName, businessName sql.NullString
		err := store.db.QueryRow(
			"SELECT push_name, full_name, first_name, business_name FROM senders WHERE jid = ?", key,
		).Scan(&pushName, &fullName, &firstName, &businessName)
		if err != nil {
			continue
		}
		// Junta campo a campo em vez de parar na primeira linha que tenha
		// QUALQUER nome. A linha PN pode ter so push_name e a linha @lid o
		// full_name; parando na primeira, o nome longo se perdia e deixava de
		// proteger o prefixo — e ai saia a pessoa errada grifada, sem recusa
		// (achado 2 da rodada 9).
		for _, campo := range []struct {
			destino *string
			veio    sql.NullString
		}{
			{&p.pushName, pushName}, {&p.fullName, fullName},
			{&p.firstName, firstName}, {&p.businessName, businessName},
		} {
			if *campo.destino == "" {
				*campo.destino = campo.veio.String
			}
		}
	}
}

// chatParticipants lists who can be mentioned in chatJID (D5): a group's
// members, or the other side of a 1:1 conversation. Names come from the
// senders table (push_name/full_name/first_name/business_name) — never from
// GetGroupInfo's DisplayName, measured empty for every participant in this
// environment (its JID comes back @lid, not a phone number, so the name has
// to be looked up separately).
//
// A participant with no resolvable phone number comes back with an empty
// phoneUser — present, but not mentionable. Skipping them outright is what the
// first version did, and it was wrong twice over (achado 2 da rodada 9): the
// name still has to protect the prefix of a shorter name, and it still has to
// count in D6's ambiguity. Dropping it turned both into a silent mention of
// the wrong person.
func chatParticipants(client *whatsmeow.Client, messageStore *MessageStore, chatJID types.JID) ([]mentionParticipant, error) {
	if chatJID.Server != types.GroupServer {
		return participantesDaConversa(messageStore, chatJID, mapaDeLIDDoCliente(client)), nil
	}
	groupInfo, err := client.GetGroupInfo(context.Background(), chatJID)
	if err != nil {
		return nil, err
	}
	return participantesDeGrupo(messageStore, groupInfo), nil
}

// participantesDeGrupo e o corpo do ramo de grupo, fora do handler para poder
// ser exercitado: o achado 2 da rodada 10 foi que reverter a correcao da rodada
// 9 AQUI DENTRO — voltar a descartar quem nao tem telefone — deixava a bateria
// inteira verde, porque nenhum teste chamava chatParticipants.
func participantesDeGrupo(store *MessageStore, groupInfo *types.GroupInfo) []mentionParticipant {
	participants := make([]mentionParticipant, 0, len(groupInfo.Participants))
	for _, gp := range groupInfo.Participants {
		p := participanteDoGrupo(gp)
		store.fillSenderNames(&p)
		participants = append(participants, p)
	}
	return participants
}

// mapaDeLID e o pedaco de store.LIDStore que a ponte usa. A interface e nossa,
// e pequena, para que o teste possa passar um duble sem implementar as cinco
// funcoes da lib — sem isso o unico jeito de exercitar a busca seria com um
// cliente whatsmeow conectado, e a correcao ficaria sem guarda.
type mapaDeLID interface {
	GetPNForLID(ctx context.Context, lid types.JID) (types.JID, error)
	GetLIDForPN(ctx context.Context, pn types.JID) (types.JID, error)
}

// mapaDeLIDDoCliente devolve nil de verdade quando nao ha mapa, e nao uma
// interface com ponteiro nulo dentro.
func mapaDeLIDDoCliente(client *whatsmeow.Client) mapaDeLID {
	if client == nil || client.Store == nil || client.Store.LIDs == nil {
		return nil
	}
	return client.Store.LIDs
}

// participantesDaConversa monta o outro lado de uma conversa 1:1. As outras
// formas do JID vem junto pelo mesmo motivo do grupo: a linha da tabela senders
// pode estar sob o @lid. O ramo 1:1 nao as tinha, entao a correcao do achado 3
// da rodada 9 valia so em grupo, e uma pessoa mencionavel no grupo era recusada
// na conversa particular (achado 1 da rodada 10).
func participantesDaConversa(store *MessageStore, chatJID types.JID, lids mapaDeLID) []mentionParticipant {
	p := mentionParticipant{
		jid:          chatJID.String(),
		phoneUser:    chatJID.User,
		outrasChaves: outrasFormasDoJID(lids, chatJID),
	}
	store.fillSenderNames(&p)
	return []mentionParticipant{p}
}

// outrasFormasDoJID devolve o mesmo endereco na OUTRA forma — o @lid de um
// telefone, o telefone de um @lid — pelo mapa que a propria lib mantem. Lista
// vazia quando nao ha mapeamento, que e o caso comum de contato novo.
func outrasFormasDoJID(lids mapaDeLID, jid types.JID) []string {
	if lids == nil {
		return nil
	}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	var outra types.JID
	var err error
	switch jid.Server {
	case types.DefaultUserServer:
		outra, err = lids.GetLIDForPN(ctx, jid)
	case types.HiddenUserServer:
		outra, err = lids.GetPNForLID(ctx, jid)
	default:
		return nil
	}
	if err != nil || outra.IsEmpty() || outra.String() == jid.String() {
		return nil
	}
	return []string{outra.String()}
}

// participanteDoGrupo traduz o que GetGroupInfo devolve para o participante que
// a resolucao de mencao usa. Esta fora do laco de proposito: e AQUI que morava
// o achado 3 da rodada 9 — a chave alternativa vinha de gp.JID, que e a forma
// PN sempre que o grupo e endereçado por telefone, ou seja igual ao jid, e a
// linha @lid da tabela senders nunca era alcancada. Um teste que monta o
// participante na mao prova que a busca LE o campo; so um teste que passa por
// esta funcao prova que a producao o PREENCHE.
func participanteDoGrupo(gp types.GroupParticipant) mentionParticipant {
	p := mentionParticipant{jid: gp.PhoneNumber.String(), phoneUser: gp.PhoneNumber.User}
	if gp.PhoneNumber.IsEmpty() {
		// Sem telefone nao da para mencionar, mas a pessoa continua na lista:
		// o nome dela protege o prefixo e conta na ambiguidade da D6.
		p = mentionParticipant{jid: gp.JID.String()}
	}
	for _, chave := range []types.JID{gp.LID, gp.JID} {
		if !chave.IsEmpty() && chave.String() != p.jid {
			p.outrasChaves = append(p.outrasChaves, chave.String())
		}
	}
	return p
}

// digitosDe devolve so os digitos de s — o teste de "isto tem cara de
// telefone?" que a D3 usa nas duas pontas: aqui, para nao casar nome por
// numero; e no servidor MCP, para nao imprimir numero no lugar de nome.
func digitosDe(s string) string {
	var b strings.Builder
	for _, r := range s {
		if unicode.IsDigit(r) {
			b.WriteRune(r)
		}
	}
	return b.String()
}

// rotuloDoParticipante escolhe COMO chamar esta pessoa na pergunta da D6. O
// campo que casou nao serve: dois homonimos de primeiro nome saem com rotulo
// identico, e a pergunta "qual dos dois?" fica impossivel de responder —
// exatamente o contrario do que a D6 existe para fazer (achado da rodada 7).
// Vai o nome mais especifico que se conhece, e nunca o numero (D3).
func rotuloDoParticipante(p mentionParticipant, casou string) string {
	for _, n := range []string{p.fullName, p.businessName, p.pushName, p.firstName} {
		if n != "" && len(digitosDe(n)) < 8 {
			return n
		}
	}
	return casou
}

// rotulosDistintos garante que a pergunta da D6 seja RESPONDIVEL. A rodada 7
// trocou "o campo que casou" pelo nome mais especifico conhecido, mas dois
// participantes podem ter o mesmo nome especifico — dois "Ana Paula" na agenda,
// com push_name diferente — e ai os dois candidatos saem com rotulo identico e
// o usuario escolhe no escuro de novo. Quando o rotulo colide, junta-se o outro
// nome que a pessoa tem e o homonimo nao; nao havendo nenhum, entra a ordem
// ("1 de 2"). Nunca o numero (D3).
func rotulosDistintos(participants []mentionParticipant, matches []mentionMatch) []string {
	rotulos := make([]string, len(matches))
	for i, m := range matches {
		rotulos[i] = m.name
	}
	colide := func(i int) bool {
		for j := range rotulos {
			if j != i && rotulos[j] == rotulos[i] {
				return true
			}
		}
		return false
	}
	for i, m := range matches {
		if !colide(i) {
			continue
		}
		for _, p := range participants {
			if p.jid != m.jid {
				continue
			}
			for _, n := range []string{p.fullName, p.businessName, p.pushName, p.firstName} {
				if n == "" || n == rotulos[i] || len(digitosDe(n)) >= 8 {
					continue
				}
				rotulos[i] = rotulos[i] + " (" + n + ")"
				break
			}
			break
		}
	}
	// O que ainda colide depois disso — homonimos sem nenhum nome que os separe
	// — ganha a ordem em que apareceu. Feio, mas responder "o segundo" e
	// possivel; responder "o Ana Paula" nao era.
	ainda := make([]bool, len(rotulos))
	for i := range rotulos {
		ainda[i] = colide(i)
	}
	for i := range rotulos {
		if ainda[i] {
			rotulos[i] = fmt.Sprintf("%s (%d de %d)", rotulos[i], i+1, len(rotulos))
		}
	}
	return rotulos
}

// matchMentionName finds every participant whose full_name, first_name,
// push_name or business_name matches name exactly (case/accent-insensitive,
// via stripAccents) — never a substring or prefix match, so requesting
// "Rodrigo" doesn't also catch a "Rodrigo Silva" whose first_name isn't
// exactly "Rodrigo". D6's ambiguity is exactly two participants resolving the
// same requested name through different fields (e.g. two whose first_name is
// "Rodrigo").
func matchMentionName(participants []mentionParticipant, name string) []mentionMatch {
	target := nomeNormalizado(name)
	if target == "" {
		return nil
	}
	// Mencao se faz por NOME, nunca por numero (D3, palavra do Luis). Hoje um
	// numero pedido nao casaria nome nenhum — mas isso e acidente, nao defesa:
	// basta o push_name de alguem SER o proprio telefone (medido: 1 em 2.547
	// remetentes do store real) para a borda abrir. Restricao dura merece
	// guarda explicita.
	if len(digitosDe(target)) >= 8 {
		return nil
	}
	var matches []mentionMatch
	for _, p := range participants {
		switch {
		case p.fullName != "" && nomeNormalizado(p.fullName) == target:
			matches = append(matches, mentionMatch{jid: p.jid, phoneUser: p.phoneUser, name: rotuloDoParticipante(p, p.fullName), origem: "agenda"})
		case p.firstName != "" && nomeNormalizado(p.firstName) == target:
			matches = append(matches, mentionMatch{jid: p.jid, phoneUser: p.phoneUser, name: rotuloDoParticipante(p, p.firstName), origem: "agenda"})
		case p.pushName != "" && nomeNormalizado(p.pushName) == target:
			matches = append(matches, mentionMatch{jid: p.jid, phoneUser: p.phoneUser, name: rotuloDoParticipante(p, p.pushName), origem: "whatsapp"})
		case p.businessName != "" && nomeNormalizado(p.businessName) == target:
			matches = append(matches, mentionMatch{jid: p.jid, phoneUser: p.phoneUser, name: rotuloDoParticipante(p, p.businessName), origem: "negocio"})
		}
	}
	return matches
}

// mentionRefEntry is what an opaque ref (D6) resolves to: the candidate's
// JID, the name that was being disambiguated (needed to redo the same
// "@name" text substitution on resend), and when it expires.
type mentionRefEntry struct {
	jid  string
	name string
	// chatJID pins the ref to the conversation whose ambiguity minted it.
	// Without it a ref from chat A resolves in chat B, and the substitution
	// writes the number of someone who was never in B into a message sent to
	// B — D6 restricts a mention to the participants of the destination chat,
	// and the ref path bypassed that check entirely.
	chatJID   string
	expiresAt time.Time
}

// mentionRefTTL is how long an ambiguous-mention ref (D6) stays valid.
const mentionRefTTL = 10 * time.Minute

// mentionRefs holds every outstanding ambiguous-mention ref, in-process only
// (D6: "o mapa é do processo: reinício da ponte perde os tokens, e isso é
// aceitável").
var mentionRefs = struct {
	sync.Mutex
	byRef map[string]mentionRefEntry
}{byRef: make(map[string]mentionRefEntry)}

// storeMentionRef mints an opaque 8-hex-char identifier for one ambiguous
// candidate (D6) and remembers it for mentionRefTTL. One that happens to
// come out all-digits is rerolled — [0-9]{8,} is exactly what D6 forbids from
// appearing in the response body, and an 8-digit id would trip that check by
// accident roughly 1 in 40 times.
func storeMentionRef(jid, name, chatJID string) string {
	mentionRefs.Lock()
	defer mentionRefs.Unlock()
	// Sweep on insert. The only other removal happens when someone looks up an
	// already-expired ref — and a ref that is minted and never resent (the
	// caller picked the other candidate, or gave up) is never looked up again,
	// so without this the map grows for the life of the process.
	agora := time.Now()
	for id, entry := range mentionRefs.byRef {
		if agora.After(entry.expiresAt) {
			delete(mentionRefs.byRef, id)
		}
	}
	var refID string
	for {
		refID = randomHexID(8)
		if isAllDigits(refID) {
			continue
		}
		if _, exists := mentionRefs.byRef[refID]; exists {
			continue
		}
		break
	}
	mentionRefs.byRef[refID] = mentionRefEntry{jid: jid, name: name, chatJID: chatJID, expiresAt: agora.Add(mentionRefTTL)}
	return refID
}

// resolveMentionRef looks up a "ref:<id>" mention. An expired or unknown id
// is dropped (if present) and reported as not found.
func resolveMentionRef(refID, chatJID string) (jid, name string, ok bool) {
	mentionRefs.Lock()
	defer mentionRefs.Unlock()
	entry, exists := mentionRefs.byRef[refID]
	if !exists || time.Now().After(entry.expiresAt) {
		delete(mentionRefs.byRef, refID)
		return "", "", false
	}
	// A ref only resolves in the conversation that minted it. Resolving it
	// elsewhere would mention someone who is not in the destination chat, and
	// write their number into the text sent there.
	if entry.chatJID != chatJID {
		return "", "", false
	}
	return entry.jid, entry.name, true
}

// randomHexID returns n random lowercase hex characters.
func randomHexID(n int) string {
	b := make([]byte, (n+1)/2)
	if _, err := cryptorand.Read(b); err != nil {
		// cryptorand.Read doesn't fail on any supported platform; if it ever
		// does, a timestamp-derived id beats panicking mid-request.
		return strconv.FormatInt(time.Now().UnixNano(), 16)[:n]
	}
	return hex.EncodeToString(b)[:n]
}

// isAllDigits is defined once, further down (used by both the check-phones
// path and storeMentionRef's reroll-on-all-digits guard).

// isChatParticipant says whether jid is in the destination chat's participant
// list, comparing without the device suffix — a participant list and a stored
// JID do not always carry the same addressing.
func isChatParticipant(participants []mentionParticipant, jid string) bool {
	_, ok := participantePorJID(participants, jid)
	return ok
}

// participantePorJID acha quem, nesta conversa, e o dono deste JID — e devolve
// o participante inteiro, nao um sim/nao: quem resolve uma mencao precisa do
// phoneUser dele, que e a unica fonte do numero escrito no texto.
func participantePorJID(participants []mentionParticipant, jid string) (mentionParticipant, bool) {
	alvo := semDispositivo(jid)
	for _, p := range participants {
		if semDispositivo(p.jid) == alvo {
			return p, true
		}
	}
	return mentionParticipant{}, false
}

// semDispositivo drops the ":<device>" part of an addressed JID.
func semDispositivo(jid string) string {
	at := strings.Index(jid, "@")
	if at < 0 {
		return jid
	}
	user := jid[:at]
	if colon := strings.Index(user, ":"); colon >= 0 {
		user = user[:colon]
	}
	return user + jid[at:]
}

// resolveMentions resolves mentions (D3-D7) against chatJID's participants:
// each entry is either a bare name (matched against the chat's participants)
// or "ref:<id>" from a previous ambiguous refusal. Returns either the
// resolved mentions ready to apply to the text, or a refusal — 4xx, nothing
// sent — carrying candidates only for the ambiguous case (D6).
func resolveMentions(client *whatsmeow.Client, messageStore *MessageStore, chatJID types.JID, mentions []string) ([]resolvedMention, []nomeDeParticipante, []MentionCandidateResponse, string, int) {
	if len(mentions) == 0 {
		return nil, nil, nil, "", 0
	}
	// Mencao so renderiza contra endereco de telefone: num 1:1 endereçado por
	// @lid o texto sairia com um identificador estranho e o WhatsApp nao
	// grifaria nada. Recusa, e recusa 4xx — a ponte nao errou, o pedido e que
	// nao cabe naquela conversa (observacao 2 da rodada 6: isto saia 500).
	if chatJID.Server != types.GroupServer && chatJID.Server != types.DefaultUserServer {
		return nil, nil, nil, fmt.Sprintf(
			"this conversation is addressed as %s, and a mention only renders against a phone-number address",
			chatJID.Server,
		), http.StatusBadRequest
	}
	participants, err := chatParticipants(client, messageStore, chatJID)
	if err != nil {
		return nil, nil, nil, fmt.Sprintf("could not resolve chat participants: %v", err), http.StatusInternalServerError
	}
	return resolveMentionsAgainstParticipants(participants, mentions, chatJID.String())
}

// resolveMentionsAgainstParticipants is resolveMentions' matching core, split
// out so it's testable (TestResolveMentionAmbigua) without a live whatsmeow
// client — it only touches the participants list and the in-process ref map,
// never the network.
func resolveMentionsAgainstParticipants(participants []mentionParticipant, mentions []string, chatJID string) ([]resolvedMention, []nomeDeParticipante, []MentionCandidateResponse, string, int) {
	resolved := make([]resolvedMention, 0, len(mentions))
	for _, raw := range mentions {
		if refID, isRef := strings.CutPrefix(raw, "ref:"); isRef {
			jid, name, ok := resolveMentionRef(refID, chatJID)
			if !ok {
				return nil, nil, nil, fmt.Sprintf("mention ref %q expired or unknown — redo the mention by name", refID), http.StatusBadRequest
			}
			// Belt and braces: the ref is already pinned to this chat, but the
			// participant list is the authority on who can be mentioned here
			// (D6), and membership can change between the refusal and the
			// resend.
			p, ok := participantePorJID(participants, jid)
			if !ok {
				return nil, nil, nil, fmt.Sprintf("mention ref %q is not a participant of this chat — redo the mention by name", refID), http.StatusBadRequest
			}
			if p.phoneUser == "" {
				return nil, nil, nil, fmt.Sprintf("%q is in this chat but has no phone number the bridge can mention them with — nothing was sent", name), http.StatusBadRequest
			}
			phoneUser := p.phoneUser
			resolved = append(resolved, resolvedMention{name: name, phoneUser: phoneUser, jid: jid, viaRef: true})
			continue
		}
		matches := matchMentionName(participants, raw)
		if len(matches) == 0 {
			return nil, nil, nil, fmt.Sprintf("no participant named %q found in this chat", raw), http.StatusBadRequest
		}
		if len(matches) > 1 {
			candidates := make([]MentionCandidateResponse, 0, len(matches))
			rotulos := rotulosDistintos(participants, matches)
			for i, m := range matches {
				candidates = append(candidates, MentionCandidateResponse{
					Ref: storeMentionRef(m.jid, raw, chatJID), Nome: rotulos[i], Origem: m.origem,
				})
			}
			return nil, nil, candidates, fmt.Sprintf("%q matches more than one participant in this chat — resend with one of the refs below", raw), http.StatusBadRequest
		}
		if matches[0].phoneUser == "" {
			return nil, nil, nil, fmt.Sprintf("%q is in this chat but has no phone number the bridge can mention them with — nothing was sent", matches[0].name), http.StatusBadRequest
		}
		resolved = append(resolved, resolvedMention{name: raw, phoneUser: matches[0].phoneUser, jid: matches[0].jid})
	}
	return resolved, nomesDeParticipantes(participants), nil, "", 0
}

// nomeDeParticipante e um nome pelo qual alguem desta conversa pode ser escrito
// depois de um "@", junto do JID de quem o usa. O JID importa: o mesmo nome
// longo pode ser de um participante que NAO foi pedido (e ai o texto fica
// intacto) ou da PROPRIA pessoa pedida, escrita pelo nome completo em vez do
// nome que veio em `mentions` — e ai tem de substituir, nao deixar intacto.
type nomeDeParticipante struct {
	nome string
	jid  string
}

// nomesDeParticipantes junta todo nome pelo qual alguem desta conversa pode ser
// escrito depois de um "@". applyMentions usa a lista para NAO substituir um
// nome pedido dentro do nome mais longo de outro participante.
func nomesDeParticipantes(participants []mentionParticipant) []nomeDeParticipante {
	nomes := make([]nomeDeParticipante, 0, len(participants)*4)
	for _, p := range participants {
		for _, n := range []string{p.fullName, p.pushName, p.businessName, p.firstName} {
			if n != "" {
				nomes = append(nomes, nomeDeParticipante{nome: n, jid: p.jid})
			}
		}
	}
	return nomes
}

// fronteiraDeNome diz se o que vem DEPOIS de um "@nome" encerra o nome. Sem
// isso, "@RodrigoPG" com `mentions: ["Rodrigo"]` virava "@<número>PG": texto
// corrompido e menção sem âncora válida, contra a D5 ("@" não pedido passa
// intacto — que passava a valer só para o que não COMEÇA com um nome pedido).
// Letra ou dígito logo depois significa que o "@" era outra palavra.
func fronteiraDeNome(resto string) bool {
	if resto == "" {
		return true
	}
	r, _ := utf8.DecodeRuneInString(resto)
	return !unicode.IsLetter(r) && !unicode.IsDigit(r)
}

// textoNormalizado poe o texto sob a MESMA regua que matchMentionName usa para
// casar nome (stripAccents: NFD, sem marca, minusculas) e devolve junto as duas
// traducoes de posicao entre os dois textos: paraOriginal[p] e o deslocamento
// no texto ORIGINAL de onde veio o byte p do normalizado, e paraNormalizado[o]
// o caminho inverso.
//
// As duas traducoes existem porque normalizar muda o comprimento em bytes:
// applyMentions precisa casar na regua da resolucao e ainda recortar o texto
// original byte a byte. Sem isso a comparacao no texto era byte a byte
// enquanto a da resolucao era normalizada, e o nome longo do OUTRO
// participante — o candidato que existe so para proteger o prefixo — deixava
// de casar quando a agenda guardava caixa ou acento diferentes do que o autor
// escreveu (achado da rodada 8).
func textoNormalizado(s string) (string, []int, []int) {
	var b strings.Builder
	b.Grow(len(s))
	paraOriginal := make([]int, 0, len(s)+1)
	paraNormalizado := make([]int, len(s)+1)
	for k := range paraNormalizado {
		paraNormalizado[k] = -1
	}
	for o, r := range s {
		paraNormalizado[o] = b.Len()
		if ehSeparadorDeNome(r) {
			// Corrida de separadores vale por UM espaco. O primeiro da corrida
			// e quem carrega a posicao original; os demais nao emitem byte, e
			// e por isso que o recorte continua exato.
			if b.Len() == 0 || b.String()[b.Len()-1] != ' ' {
				b.WriteByte(' ')
				paraOriginal = append(paraOriginal, o)
			}
			continue
		}
		for _, d := range norm.NFD.String(string(r)) {
			if unicode.Is(unicode.Mn, d) {
				continue
			}
			antes := b.Len()
			b.WriteRune(unicode.ToLower(d))
			for k := antes; k < b.Len(); k++ {
				paraOriginal = append(paraOriginal, o)
			}
		}
	}
	paraOriginal = append(paraOriginal, len(s))
	paraNormalizado[len(s)] = b.Len()
	// Deslocamento no meio de um rune herda o inicio dele. Nao se indexa por
	// ali no caminho normal, mas -1 vazando viraria panico silencioso.
	for k := 1; k < len(paraNormalizado); k++ {
		if paraNormalizado[k] < 0 {
			paraNormalizado[k] = paraNormalizado[k-1]
		}
	}
	return b.String(), paraOriginal, paraNormalizado
}

// applyMentions substitutes every "@name" occurrence for each resolved
// mention with "@phoneUser" (D4 — the WhatsApp app only highlights a mention
// when the text contains "@<number>" matching a MentionedJID entry) and
// collects the JIDs for ContextInfo.MentionedJID. Only names present in
// resolved are touched (D5) — a bare "@" elsewhere in the text, or a name
// never requested, is never scanned for.
//
// The scan is a single left-to-right pass with the LONGEST name tried first,
// and it never re-reads what it already wrote. Both properties are the fix
// for a defect found in review: a per-name strings.ReplaceAll rewrote
// "@Ana e @Ana Paula" into "@<número da Ana> e @<número da Ana> Paula" —
// Ana highlighted where the author wrote Ana Paula, and Ana Paula carrying a
// MentionedJID with no anchor in the body. Mentioning the wrong person in a
// group has no undo, which is the whole reason D6 stops to ask.
//
// A mention whose "@name" never appears in the body is refused rather than
// sent: WhatsApp only highlights what the text actually writes, so a
// MentionedJID without its anchor notifies someone with nothing on screen
// explaining why.
func applyMentions(text string, resolved []resolvedMention, outrosNomes []nomeDeParticipante) (string, []string, string, int) {
	if len(resolved) == 0 {
		return text, nil, "", 0
	}

	// Todos os nomes que podem aparecer depois de um "@" nesta conversa, não só
	// os pedidos: o nome de participante que NÃO foi pedido entra como
	// candidato justamente para vencer o pedido mais curto e ser deixado
	// intacto. Sem ele, "@Ana Paula" num pedido de `mentions: ["Ana"]` virava
	// "@<número da Ana> Paula" — a Ana grifada onde o autor escreveu Ana Paula,
	// e a D6 não tem como segurar, porque "Ana Paula" nunca casou "Ana" e
	// portanto não houve ambiguidade a perguntar.
	type candidato struct {
		nome string
		// norm e o nome sob a regua de matchMentionName. O casamento no texto
		// se faz por ele, nunca pelos bytes crus: as duas pontas tem de usar a
		// mesma regua (rodada 8).
		norm string
		idx  int // índice em resolved, ou -1 para nome que não foi pedido
	}
	cands := make([]candidato, 0, len(resolved)+len(outrosNomes))
	for i, r := range resolved {
		if n := nomeNormalizado(r.name); n != "" {
			cands = append(cands, candidato{nome: r.name, norm: n, idx: i})
		}
	}
	for _, n := range outrosNomes {
		if n.nome == "" {
			continue
		}
		// Nome longo da PROPRIA pessoa pedida nao pode comer a ancora dela.
		// Achado da rodada 4: com `mentions: ["Ana Paula"]` e o autor
		// escrevendo "@Ana Paula Souza", o nome completo vencia por ser mais
		// longo, ficava intacto, e a mencao saia sem uso — recusa 400 dizendo
		// que "@Ana Paula" nao esta no texto, com "@Ana Paula" no texto.
		//
		// Mas ligar por JID sozinho reintroduz o defeito que a D6 existe para
		// impedir (achado da rodada 5): se o mesmo NOME pertence a mais de um
		// participante, substituir e escolher por conta propria qual dos dois
		// o autor quis — so que reescrevendo o texto dele, nao a notificacao.
		// Entao nome compartilhado so liga quando o usuario JA desambiguou,
		// isto e, quando a mencao veio por "ref:". Fora disso fica intacto, e
		// no maximo se paga uma recusa — que e a falha segura.
		donos := 0
		for _, outro := range outrosNomes {
			if nomeNormalizado(outro.nome) == nomeNormalizado(n.nome) && outro.jid != n.jid {
				donos++
			}
		}
		idx := -1
		for i, r := range resolved {
			if r.jid == "" || r.jid != n.jid {
				continue
			}
			if donos > 0 && !r.viaRef {
				break
			}
			idx = i
			break
		}
		norma := nomeNormalizado(n.nome)
		if norma == "" {
			continue
		}
		cands = append(cands, candidato{nome: n.nome, norm: norma, idx: idx})
	}
	sort.SliceStable(cands, func(a, b int) bool {
		if len(cands[a].norm) != len(cands[b].norm) {
			return len(cands[a].norm) > len(cands[b].norm)
		}
		// Mesmo nome, duas pessoas: quem esta ligado a uma mencao pedida vem
		// primeiro. Sem este desempate, o homonimo que NAO foi pedido casava
		// antes, ficava intacto, e a mencao morria sem ancora — a recusa
		// contraditoria da observacao 1 da rodada 5, no caminho que o README
		// ensina (recusa ambigua -> reenvio por ref).
		return cands[a].idx >= 0 && cands[b].idx < 0
	})

	usados := make([]bool, len(resolved))
	comidoPor := make(map[int]string, len(resolved))
	normText, paraOriginal, paraNormalizado := textoNormalizado(text)
	var b strings.Builder
	for i := 0; i < len(text); {
		if text[i] != '@' {
			b.WriteByte(text[i])
			i++
			continue
		}
		// Nesta posicao, o nome MAIS LONGO que casa vence — sempre. Essa regra
		// e o que segura os achados das rodadas 4 e 5 (nome curto comendo o
		// prefixo do longo), e nao pode ser negociada.
		//
		// A preferencia por "ainda nao usado" vale SO entre candidatos desse
		// mesmo comprimento. A rodada 6 a aplicou entre comprimentos
		// diferentes, e com isso "@Luis Montes" — cujo casamento longo ja
		// estava usado — caia num "Luis" de OUTRA pessoa: o texto saia com o
		// numero do B onde o autor escreveu o nome do A, e sem recusa. Era
		// trocar uma recusa segura por um envio errado, que e exatamente o
		// dano que a D6 existe para impedir (achado da rodada 7).
		//
		// Se o unico casamento mais longo ja foi usado, repete-se ele: a
		// mencao que sobrar sem ancora vira recusa 400 — falha segura.
		//
		// O casamento se faz no texto NORMALIZADO, e o que se consome e medido
		// no texto ORIGINAL: e a mesma regua da resolucao, e o recorte continua
		// exato (rodada 8).
		np := paraNormalizado[i+1]
		casa := func(c candidato) (int, bool) {
			if !strings.HasPrefix(normText[np:], c.norm) {
				return 0, false
			}
			fim := paraOriginal[np+len(c.norm)]
			if !fronteiraDeNome(text[fim:]) {
				return 0, false
			}
			return fim, true
		}
		maiorCasamento := -1
		for _, c := range cands {
			if _, ok := casa(c); !ok {
				continue
			}
			maiorCasamento = len(c.norm)
			break // cands esta ordenado por comprimento decrescente
		}
		escolhido, fimEscolhido := -1, 0
		for passada := 0; passada < 2 && escolhido < 0; passada++ {
			for ci, c := range cands {
				if len(c.norm) != maiorCasamento {
					continue
				}
				fim, ok := casa(c)
				if !ok {
					continue
				}
				if passada == 0 && c.idx >= 0 && usados[c.idx] {
					continue
				}
				escolhido, fimEscolhido = ci, fim
				break
			}
		}
		if escolhido < 0 {
			// Nada casou nesta posição: nem nome pedido, nem nome de
			// participante. Copia o "@" e segue.
			b.WriteByte(text[i])
			i++
			continue
		}
		c := cands[escolhido]
		if c.idx < 0 {
			// Este "@" nomeia OUTRO participante, e por isso fica intacto. Se
			// alguma mencao pedida ainda sem ancora cabe dentro deste nome, e
			// ele que vai explicar a recusa: sem isso o erro dizia que "@Ana"
			// nao esta no texto, com "@Ana" no texto (achado 4 da rodada 10).
			for i, r := range resolved {
				if !usados[i] && strings.HasPrefix(c.norm, nomeNormalizado(r.name)) {
					comidoPor[i] = c.nome
				}
			}
		}
		b.WriteString("@")
		if c.idx >= 0 {
			b.WriteString(resolved[c.idx].phoneUser)
			usados[c.idx] = true
		} else {
			// Nome de participante que ninguém pediu: fica como está
			// (D5 — "@" não listado passa intacto). Vai o trecho do texto do
			// AUTOR, nunca o nome da agenda: o casamento e normalizado, entao
			// os dois podem diferir em caixa e acento, e reescrever a grafia
			// de quem escreveu seria mexer no texto sem ter sido pedido.
			b.WriteString(text[i+1 : fimEscolhido])
		}
		i = fimEscolhido
	}

	mentionedJIDs := make([]string, 0, len(resolved))
	for i, r := range resolved {
		if !usados[i] {
			if outro := comidoPor[i]; outro != "" {
				return text, nil, fmt.Sprintf(
					"mention %q was not applied: where %q appears the text names %q, another participant of this chat, and the longer name wins — rewrite the sentence or mention %q instead; nothing was sent",
					r.name, "@"+r.name, outro, outro,
				), http.StatusBadRequest
			}
			return text, nil, fmt.Sprintf(
				"mention %q has no %q anchor in the message text — WhatsApp only highlights a mention the body writes, so nothing was sent",
				r.name, "@"+r.name,
			), http.StatusBadRequest
		}
		mentionedJIDs = append(mentionedJIDs, r.jid)
	}
	return b.String(), mentionedJIDs, "", 0
}

func sendWhatsAppMessage(client *whatsmeow.Client, messageStore *MessageStore, recipient string, message string, mediaPath string, quotedMessageID string, mentions []string) (bool, string, int, []MentionCandidateResponse) {
	// Create JID for recipient
	var recipientJID types.JID
	var err error

	// Check if recipient is a JID
	isJID := strings.Contains(recipient, "@")

	if isJID {
		// Parse the JID string
		recipientJID, err = types.ParseJID(recipient)
		if err != nil {
			return false, fmt.Sprintf("Error parsing JID: %v", err), http.StatusInternalServerError, nil
		}
	} else {
		// Create JID from phone number
		recipientJID = types.JID{
			User:   recipient,
			Server: "s.whatsapp.net", // For personal chats
		}
	}

	// D9/D12: resolve the citation before touching the client at all, so the
	// three refusals reject with nothing sent regardless of connection state.
	var contextInfo *waProto.ContextInfo
	if quotedMessageID != "" {
		ctxInfo, errMsg, statusCode := buildQuoteContextInfo(messageStore, quotedMessageID, recipientJID.String())
		if errMsg != "" {
			return false, errMsg, statusCode, nil
		}
		contextInfo = ctxInfo
	}

	if !client.IsConnected() {
		return false, "Not connected to WhatsApp", http.StatusInternalServerError, nil
	}

	// D3-D7: resolve @Name mentions against the destination chat's
	// participants and substitute them into the text before building the
	// outbound message. This necessarily runs after the IsConnected check
	// above (unlike the citation, resolving a group's participants needs a
	// live client for GetGroupInfo) — but still before any media upload or
	// SendMessage call, so an ambiguous/unmatched mention leaves nothing sent.
	var mentionedJIDs []string
	if len(mentions) > 0 {
		resolvedMentions, outrosNomes, candidates, errMsg, statusCode := resolveMentions(client, messageStore, recipientJID, mentions)
		if errMsg != "" {
			return false, errMsg, statusCode, candidates
		}
		var anchorErr string
		var anchorStatus int
		message, mentionedJIDs, anchorErr, anchorStatus = applyMentions(message, resolvedMentions, outrosNomes)
		if anchorErr != "" {
			return false, anchorErr, anchorStatus, nil
		}
	}
	if len(mentionedJIDs) > 0 {
		if contextInfo == nil {
			contextInfo = &waProto.ContextInfo{}
		}
		contextInfo.MentionedJID = mentionedJIDs
	}

	msg := &waProto.Message{}

	// Check if we have media to send
	if mediaPath != "" {
		// Read media file
		mediaData, err := os.ReadFile(mediaPath)
		if err != nil {
			return false, fmt.Sprintf("Error reading media file: %v", err), http.StatusInternalServerError, nil
		}

		// Determine media type and mime type based on file extension
		fileExt := strings.ToLower(mediaPath[strings.LastIndex(mediaPath, ".")+1:])
		var mediaType whatsmeow.MediaType
		var mimeType string

		// Handle different media types
		switch fileExt {
		// Image types
		case "jpg", "jpeg":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/jpeg"
		case "png":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/png"
		case "gif":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/gif"
		case "webp":
			mediaType = whatsmeow.MediaImage
			mimeType = "image/webp"

		// Audio types
		case "ogg":
			mediaType = whatsmeow.MediaAudio
			mimeType = "audio/ogg; codecs=opus"

		// Video types
		case "mp4":
			mediaType = whatsmeow.MediaVideo
			mimeType = "video/mp4"
		case "avi":
			mediaType = whatsmeow.MediaVideo
			mimeType = "video/avi"
		case "mov":
			mediaType = whatsmeow.MediaVideo
			mimeType = "video/quicktime"

		// Document types — use stdlib mime detection, fallback to octet-stream.
		default:
			mediaType = whatsmeow.MediaDocument
			if detected := mime.TypeByExtension("." + fileExt); detected != "" {
				mimeType = detected
			} else {
				mimeType = "application/octet-stream"
			}
		}

		// Upload media to WhatsApp servers
		resp, err := client.Upload(context.Background(), mediaData, mediaType)
		if err != nil {
			return false, fmt.Sprintf("Error uploading media: %v", err), http.StatusInternalServerError, nil
		}

		fmt.Println("Media uploaded", resp)

		// Create the appropriate message type based on media type.
		// ContextInfo (D11: citing a media message is allowed, with the
		// stored caption as its preview) is nil when there's no citation, so
		// this is always safe to set.
		switch mediaType {
		case whatsmeow.MediaImage:
			msg.ImageMessage = &waProto.ImageMessage{
				Caption:       proto.String(message),
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
				ContextInfo:   contextInfo,
			}
		case whatsmeow.MediaAudio:
			// Handle ogg audio files
			var seconds uint32 = 30 // Default fallback
			var waveform []byte = nil

			// Try to analyze the ogg file
			if strings.Contains(mimeType, "ogg") {
				analyzedSeconds, analyzedWaveform, err := analyzeOggOpus(mediaData)
				if err == nil {
					seconds = analyzedSeconds
					waveform = analyzedWaveform
				} else {
					return false, fmt.Sprintf("Failed to analyze Ogg Opus file: %v", err), http.StatusInternalServerError, nil
				}
			} else {
				fmt.Printf("Not an Ogg Opus file: %s\n", mimeType)
			}

			msg.AudioMessage = &waProto.AudioMessage{
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
				Seconds:       proto.Uint32(seconds),
				PTT:           proto.Bool(true),
				Waveform:      waveform,
				ContextInfo:   contextInfo,
			}
		case whatsmeow.MediaVideo:
			msg.VideoMessage = &waProto.VideoMessage{
				Caption:       proto.String(message),
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
				ContextInfo:   contextInfo,
			}
		case whatsmeow.MediaDocument:
			docFilename := filepath.Base(mediaPath)
			msg.DocumentMessage = &waProto.DocumentMessage{
				FileName:      proto.String(docFilename),
				Title:         proto.String(docFilename),
				Caption:       proto.String(message),
				Mimetype:      proto.String(mimeType),
				URL:           &resp.URL,
				DirectPath:    &resp.DirectPath,
				MediaKey:      resp.MediaKey,
				FileEncSHA256: resp.FileEncSHA256,
				FileSHA256:    resp.FileSHA256,
				FileLength:    &resp.FileLength,
				ContextInfo:   contextInfo,
			}
		}
	} else if contextInfo != nil {
		// D14: a ContextInfo cannot ride on Conversation (a bare string) — it
		// only exists on ExtendedTextMessage and the media types. Without a
		// citation, the line below (msg.Conversation) is untouched.
		msg.ExtendedTextMessage = &waProto.ExtendedTextMessage{
			Text:        proto.String(message),
			ContextInfo: contextInfo,
		}
	} else {
		msg.Conversation = proto.String(message)
	}

	// Send message
	resp, err := client.SendMessage(context.Background(), recipientJID, msg)

	if err != nil {
		return false, fmt.Sprintf("Error sending message: %v", err), http.StatusInternalServerError, nil
	}

	// Persist outbounds (text and media) so own-sends appear in the local store.
	// Multi-device echo via handleMessage doesn't fire on single-device accounts.
	if messageStore != nil && client.Store != nil && client.Store.ID != nil {
		chatJID := recipientJID.String()
		sender := client.Store.ID.User
		if ensureErr := messageStore.EnsureChat(chatJID, resp.Timestamp); ensureErr != nil {
			fmt.Printf("Failed to ensure chat row: %v\n", ensureErr)
		}
		mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength := extractMediaInfo(msg)
		if storeErr := messageStore.StoreMessage(
			resp.ID, chatJID, sender, message, resp.Timestamp, true,
			mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength,
		); storeErr != nil {
			fmt.Printf("Failed to persist outbound: %v\n", storeErr)
		} else {
			_ = messageStore.TouchChatLastMessageTime(chatJID, resp.Timestamp)
			// Our own JID, so a later reply can quote this message:
			// buildQuoteContextInfo refuses when sender_jid is empty (D9), and
			// without this every own-send would be unquotable.
			if ownJID := client.Store.ID.ToNonAD().String(); ownJID != "" {
				if jidErr := messageStore.StoreMessageSenderJID(resp.ID, chatJID, ownJID); jidErr != nil {
					fmt.Printf("Failed to persist outbound sender_jid: %v\n", jidErr)
				}
			}
			// The citation/mentions this message carries, so the account that
			// sent it also sees it as a reply — handleMessage only fires for
			// incoming messages, so without this the sender's own view is the
			// one place the thread is invisible (D13).
			if contextInfo != nil {
				if ctxErr := messageStore.StoreMessageContext(resp.ID, chatJID, contextInfo); ctxErr != nil {
					fmt.Printf("Failed to persist outbound context: %v\n", ctxErr)
				}
			}
		}
	}

	return true, fmt.Sprintf("Message sent to %s", recipient), http.StatusOK, nil
}

// Extract media info from a message
func extractMediaInfo(msg *waProto.Message) (mediaType string, filename string, url string, mediaKey []byte, fileSHA256 []byte, fileEncSHA256 []byte, fileLength uint64) {
	if msg == nil {
		return "", "", "", nil, nil, nil, 0
	}

	// Check for image message
	if img := msg.GetImageMessage(); img != nil {
		return "image", "image_" + time.Now().Format("20060102_150405") + ".jpg",
			img.GetURL(), img.GetMediaKey(), img.GetFileSHA256(), img.GetFileEncSHA256(), img.GetFileLength()
	}

	// Check for video message
	if vid := msg.GetVideoMessage(); vid != nil {
		return "video", "video_" + time.Now().Format("20060102_150405") + ".mp4",
			vid.GetURL(), vid.GetMediaKey(), vid.GetFileSHA256(), vid.GetFileEncSHA256(), vid.GetFileLength()
	}

	// Check for audio message
	if aud := msg.GetAudioMessage(); aud != nil {
		return "audio", "audio_" + time.Now().Format("20060102_150405") + ".ogg",
			aud.GetURL(), aud.GetMediaKey(), aud.GetFileSHA256(), aud.GetFileEncSHA256(), aud.GetFileLength()
	}

	// Check for document message
	if doc := msg.GetDocumentMessage(); doc != nil {
		filename := doc.GetFileName()
		if filename == "" {
			filename = "document_" + time.Now().Format("20060102_150405")
		}
		return "document", filename,
			doc.GetURL(), doc.GetMediaKey(), doc.GetFileSHA256(), doc.GetFileEncSHA256(), doc.GetFileLength()
	}

	return "", "", "", nil, nil, nil, 0
}

// resolveToPN converts a LID JID (xxxx@lid) to its PN (phone number) JID using
// the local whatsmeow LID store. Returns the input unchanged for non-LID JIDs.
func resolveToPN(client *whatsmeow.Client, jid types.JID) types.JID {
	if client == nil || client.Store == nil || client.Store.LIDs == nil {
		return jid
	}
	if jid.Server != types.HiddenUserServer {
		return jid
	}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	pn, err := client.Store.LIDs.GetPNForLID(ctx, jid)
	if err != nil || pn.IsEmpty() {
		return jid
	}
	return pn
}

// localChatKey returns the key the local store uses for chatJID — the same
// PN-normalized string handleMessage writes rows under (D2, follow-up to
// issue #21), so applying a revoke/edit against a chatJID that arrived as
// @lid still lands on the live row instead of missing it silently.
func localChatKey(client *whatsmeow.Client, chatJID types.JID) string {
	return resolveToPN(client, chatJID).String()
}

// resolveContactJIDs returns every JID (regular PN + LID) that maps to a phone
// number, using the whatsmeow LID store API (never the internal lid_map table).
// Parity with the Python _resolve_phone_to_jids: PN first, then the LID if known.
func resolveContactJIDs(client *whatsmeow.Client, phone string) []string {
	phone = normalizePhone(phone)
	jids := []string{phone + "@" + types.DefaultUserServer}
	if client == nil || client.Store == nil || client.Store.LIDs == nil {
		return jids
	}
	pnJID := types.JID{User: phone, Server: types.DefaultUserServer}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	if lid, err := client.Store.LIDs.GetLIDForPN(ctx, pnJID); err == nil && !lid.IsEmpty() {
		jids = append(jids, lid.String())
	}
	return jids
}

// searchContactsBridge finds contacts by name or phone across the three sources
// the bridge already owns: the whatsmeow contact store, the senders table, and
// the chats table. Dedups by JID and excludes groups. Parity with the Python
// search_contacts (which read whatsmeow_contacts directly plus a chats fallback).
func searchContactsBridge(client *whatsmeow.Client, store *MessageStore, query string) []ContactHit {
	q := strings.ToLower(strings.TrimSpace(query))
	seen := make(map[string]bool)
	var hits []ContactHit
	add := func(jid, phone, name string) {
		if jid == "" || seen[jid] || strings.HasSuffix(jid, "@"+types.GroupServer) {
			return
		}
		seen[jid] = true
		hits = append(hits, ContactHit{JID: jid, PhoneNumber: phone, Name: name})
	}

	// Source 1: whatsmeow contact store (real names + LID), via the lib API.
	if client != nil && client.Store != nil && client.Store.Contacts != nil {
		if contacts, err := client.Store.Contacts.GetAllContacts(context.Background()); err == nil {
			for jid, info := range contacts {
				name := info.FullName
				if name == "" {
					name = info.PushName
				}
				js := jid.String()
				if !strings.Contains(strings.ToLower(name), q) && !strings.Contains(strings.ToLower(js), q) {
					continue
				}
				phone := jid.User
				if jid.Server == types.HiddenUserServer {
					if pn := resolveToPN(client, jid); pn.Server == types.DefaultUserServer {
						phone = pn.User
					}
				}
				add(js, phone, name)
			}
		}
	}

	// Sources 2 & 3: senders + chats tables (messages.db), for contacts the
	// store doesn't have. LIKE with lowercase for accent-insensitive-ish parity.
	if store != nil && store.db != nil {
		like := "%" + q + "%"
		rows, err := store.db.Query(
			`SELECT jid, name FROM chats
			 WHERE (LOWER(name) LIKE ? OR LOWER(jid) LIKE ?) AND jid NOT LIKE '%@`+types.GroupServer+`'
			 UNION
			 SELECT jid, COALESCE(NULLIF(full_name,''), NULLIF(push_name,'')) AS name FROM senders
			 WHERE (LOWER(full_name) LIKE ? OR LOWER(push_name) LIKE ? OR LOWER(jid) LIKE ?)
			 LIMIT 100`,
			like, like, like, like, like,
		)
		if err == nil {
			defer rows.Close()
			for rows.Next() {
				var jid string
				var name sql.NullString
				if rows.Scan(&jid, &name) == nil {
					add(jid, strings.SplitN(jid, "@", 2)[0], name.String)
				}
			}
		}
	}
	return hits
}

// migrateLIDChats merges any chat stored under a LID JID into its PN JID.
// Idempotent: chats with no known mapping are left for the next startup.
func migrateLIDChats(client *whatsmeow.Client, store *MessageStore, logger waLog.Logger) {
	if client == nil || store == nil || store.db == nil {
		return
	}
	rows, err := store.db.Query("SELECT jid, name, last_message_time FROM chats WHERE jid LIKE '%@" + types.HiddenUserServer + "'")
	if err != nil {
		logger.Warnf("LID migration: failed to list LID chats: %v", err)
		return
	}
	type lidChat struct {
		jid             string
		name            string
		lastMessageTime time.Time
	}
	var lidChats []lidChat
	for rows.Next() {
		var c lidChat
		if err := rows.Scan(&c.jid, &c.name, &c.lastMessageTime); err == nil {
			lidChats = append(lidChats, c)
		}
	}
	rows.Close()
	if len(lidChats) == 0 {
		return
	}
	logger.Infof("LID migration: found %d chat(s) under @lid, attempting to merge", len(lidChats))
	tx, err := store.db.Begin()
	if err != nil {
		logger.Warnf("LID migration: cannot start tx: %v", err)
		return
	}
	merged, skipped := 0, 0
	for _, c := range lidChats {
		lidJID, err := types.ParseJID(c.jid)
		if err != nil {
			skipped++
			continue
		}
		pnJID := resolveToPN(client, lidJID)
		if pnJID.Server != types.DefaultUserServer {
			skipped++
			continue
		}
		pnStr := pnJID.String()
		if _, err := tx.Exec(
			"INSERT INTO chats (jid, name, last_message_time) VALUES (?, ?, ?) "+
				"ON CONFLICT(jid) DO UPDATE SET "+
				"  name = COALESCE(NULLIF(chats.name, ''), excluded.name), "+
				"  last_message_time = MAX(chats.last_message_time, excluded.last_message_time)",
			pnStr, c.name, c.lastMessageTime,
		); err != nil {
			skipped++
			continue
		}
		if _, err := tx.Exec("UPDATE OR IGNORE messages SET chat_jid = ? WHERE chat_jid = ?", pnStr, c.jid); err != nil {
			skipped++
			continue
		}
		if _, err := tx.Exec("DELETE FROM messages WHERE chat_jid = ?", c.jid); err != nil {
			skipped++
			continue
		}
		if _, err := tx.Exec("DELETE FROM chats WHERE jid = ?", c.jid); err != nil {
			skipped++
			continue
		}
		merged++
		logger.Infof("LID migration: merged %s -> %s", c.jid, pnStr)
	}
	if err := tx.Commit(); err != nil {
		tx.Rollback()
		logger.Warnf("LID migration: commit failed: %v", err)
		return
	}
	logger.Infof("LID migration: %d merged, %d skipped (no mapping yet)", merged, skipped)
}

// Handle regular incoming messages with media support
func handleMessage(client *whatsmeow.Client, messageStore *MessageStore, msg *events.Message, logger waLog.Logger) {
	// Normalize LID -> PN so the same contact doesn't split across two chat_jid values.
	chatJID := resolveToPN(client, msg.Info.Chat).String()
	sender := resolveToPN(client, msg.Info.Sender).User
	senderJID := resolveToPN(client, msg.Info.Sender).String()

	// Enrich senders table with identity data from this event.
	var fullName, firstName, businessName string
	if client.Store != nil && client.Store.Contacts != nil {
		if contact, err := client.Store.Contacts.GetContact(context.Background(), msg.Info.Sender); err == nil {
			fullName = contact.FullName
			firstName = contact.FirstName
			businessName = contact.BusinessName
		}
	}
	if err := messageStore.StoreSender(senderJID, msg.Info.PushName, fullName, firstName, businessName); err != nil {
		logger.Warnf("Failed to store sender: %v", err)
	}

	// Get appropriate chat name (pass nil for conversation since we don't have one for regular messages)
	name := GetChatName(client, messageStore, msg.Info.Chat, chatJID, nil, sender, logger)

	// Update chat in database with the message timestamp (keeps last message time updated)
	err := messageStore.StoreChat(chatJID, name, msg.Info.Timestamp)
	if err != nil {
		logger.Warnf("Failed to store chat: %v", err)
	}

	// Issue #21: a delete-for-everyone or an edit arrives as a ProtocolMessage
	// pointing at a message already stored; it has no text or media of its own.
	if applyProtocolMessage(messageStore, chatJID, msg.Message.GetProtocolMessage(), msg.Info.Timestamp, logger) {
		return
	}

	// Extract text content
	content := extractTextContent(msg.Message)

	// Extract media info
	mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength := extractMediaInfo(msg.Message)

	// Gap #11: Handle polls (T003)
	// PollCreationMessage: store poll and treat as message with question as content
	if poll := msg.Message.GetPollCreationMessage(); poll != nil {
		optionNames := make([]string, 0)
		for _, opt := range poll.GetOptions() {
			optionNames = append(optionNames, opt.GetOptionName())
		}
		optionsJSON, _ := json.Marshal(optionNames)
		if err := messageStore.StorePoll(
			msg.Info.ID,
			chatJID,
			senderJID,
			poll.GetName(),
			string(optionsJSON),
			int(poll.GetSelectableOptionsCount()),
			msg.Info.Timestamp.Unix(),
		); err != nil {
			logger.Warnf("Failed to store poll: %v", err)
		}
		// Set content to question so poll appears in history (RN-02)
		content = poll.GetName()
		// Continue to StoreMessage below, do not return
	}

	// PollUpdateMessage: handle vote
	if upd := msg.Message.GetPollUpdateMessage(); upd != nil {
		vote, err := client.DecryptPollVote(context.Background(), msg)
		if err != nil {
			logger.Warnf("Failed to decrypt poll vote: %v", err)
		} else {
			pollID := upd.GetPollCreationMessageKey().GetID()
			voterJID := resolveToPN(client, msg.Info.Sender).String()

			// Try to get poll; if not found, store vote as unresolved (RN-05)
			_, optionsJSON, _, _, err := messageStore.GetPoll(pollID, chatJID)
			if err != nil {
				// Poll unknown (created before this feature, or the bridge was
				// offline when it was sent). The vote is still recorded, as
				// unresolved, instead of vanishing (RN-05).
				if err != sql.ErrNoRows {
					logger.Warnf("Failed to load poll %s for vote: %v", pollID, err)
				}
				optionsJSON = ""
			}
			selectedJSON, resolved := resolvePollVote(optionsJSON, vote.GetSelectedOptions())

			if err := messageStore.UpsertPollVote(
				pollID,
				chatJID,
				voterJID,
				selectedJSON,
				resolved,
				msg.Info.Timestamp.Unix(),
			); err != nil {
				logger.Warnf("Failed to upsert poll vote: %v", err)
			}
		}
		// Vote does not go to messages table (RN per contracts)
		return
	}

	// Skip if there's no content and no media
	if content == "" && mediaType == "" {
		return
	}

	// Store message in database
	err = messageStore.StoreMessage(
		msg.Info.ID,
		chatJID,
		sender,
		content,
		msg.Info.Timestamp,
		msg.Info.IsFromMe,
		mediaType,
		filename,
		url,
		mediaKey,
		fileSHA256,
		fileEncSHA256,
		fileLength,
	)

	if err != nil {
		logger.Warnf("Failed to store message: %v", err)
	} else {
		// D8: persist the full sender JID that resolveToPN already computed
		// above, via its own path — StoreMessage's signature stays at 13 params.
		if err := messageStore.StoreMessageSenderJID(msg.Info.ID, chatJID, senderJID); err != nil {
			logger.Warnf("Failed to store message sender_jid: %v", err)
		}

		// D1/D13: persist what this message quotes and who it mentions, if
		// any. extractContextInfo returns nil for plain text (Conversation has
		// no ContextInfo), so a regular message never pays for the UPDATE.
		if ci := extractContextInfo(msg.Message); ci != nil {
			if err := messageStore.StoreMessageContext(msg.Info.ID, chatJID, ci); err != nil {
				logger.Warnf("Failed to store message context: %v", err)
			}
		}

		// Log message reception
		timestamp := msg.Info.Timestamp.Format("2006-01-02 15:04:05")
		direction := "←"
		if msg.Info.IsFromMe {
			direction = "→"
		}

		displayName := messageStore.ResolveName(senderJID)
		if displayName == "" {
			displayName = sender
		}

		// Log based on message type
		if mediaType != "" {
			fmt.Printf("[%s] %s %s: [%s: %s] %s\n", timestamp, direction, displayName, mediaType, filename, content)
		} else if content != "" {
			fmt.Printf("[%s] %s %s: %s\n", timestamp, direction, displayName, content)
		}
	}
}

// DownloadMediaRequest represents the request body for the download media API
type DownloadMediaRequest struct {
	MessageID string `json:"message_id"`
	ChatJID   string `json:"chat_jid"`
}

// DownloadMediaResponse represents the response for the download media API
// CreateGroupRequest represents the request body for the create group API.
type CreateGroupRequest struct {
	Name               string   `json:"name"`
	Participants       []string `json:"participants"`
	IsCommunity        bool     `json:"is_community,omitempty"`
	CommunityParentJID string   `json:"community_parent_jid,omitempty"`
}

// CreateGroupResponse represents the response for the create group API.
type CreateGroupResponse struct {
	Success          bool   `json:"success"`
	Message          string `json:"message"`
	JID              string `json:"jid,omitempty"`
	Name             string `json:"name,omitempty"`
	ParticipantCount int    `json:"participant_count,omitempty"`
}

// LeaveGroupRequest represents the request body for the leave group API.
type LeaveGroupRequest struct {
	JID string `json:"jid"`
}

// LeaveGroupResponse represents the response for the leave group API.
type LeaveGroupResponse struct {
	Success bool   `json:"success"`
	Message string `json:"message"`
}

// MarkChatReadRequest represents a request to mark a chat as read.
type MarkChatReadRequest struct {
	ChatJID    string   `json:"chat_jid"`
	MessageIDs []string `json:"message_ids"`
	SenderJID  string   `json:"sender_jid,omitempty"`
	Timestamp  int64    `json:"timestamp,omitempty"`
}

// MarkChatUnreadRequest represents a request to mark a chat as unread.
type MarkChatUnreadRequest struct {
	ChatJID string `json:"chat_jid"`
}

// ArchiveChatRequest represents a request to archive or unarchive a chat.
// Archive is a pointer so an omitted field is rejected rather than silently
// defaulting to false (which would unarchive on an "archive" endpoint).
type ArchiveChatRequest struct {
	ChatJID string `json:"chat_jid"`
	Archive *bool  `json:"archive"`
}

// ReactRequest represents a request to react to a message. Emoji may be empty
// to remove an existing reaction.
type ReactRequest struct {
	ChatJID   string `json:"chat_jid"`
	MessageID string `json:"message_id"`
	Emoji     string `json:"emoji"`
	FromMe    bool   `json:"from_me"`
}

// EditRequest represents a request to edit the text of a previously sent message.
type EditRequest struct {
	ChatJID   string `json:"chat_jid"`
	MessageID string `json:"message_id"`
	NewText   string `json:"new_text"`
	FromMe    bool   `json:"from_me"`
}

// RevokeRequest represents a request to revoke (delete for everyone) a message.
type RevokeRequest struct {
	ChatJID   string `json:"chat_jid"`
	MessageID string `json:"message_id"`
	FromMe    bool   `json:"from_me"`
}

// actionSenderJID derives the sender JID to use for react/revoke actions.
// When fromMe is true the sender is the local account (own messages are the
// common case for react/edit/revoke). When fromMe is false and
// participantJID is known — resolved by the caller from the message's stored
// sender_jid (task 6, D2) — that's the author to pass as sender:
// BuildReaction/BuildRevoke's sender parameter is exactly the message
// author's JID (design D2, citing send.go's BuildRevoke doc: an admin
// revokes someone else's message by passing that author's JID here). An
// empty participantJID falls back to chatJID, which is only correct for 1:1
// chats.
func actionSenderJID(ownID *types.JID, chatJID, participantJID types.JID, fromMe bool) types.JID {
	if fromMe && ownID != nil {
		return ownID.ToNonAD()
	}
	if !participantJID.IsEmpty() {
		return participantJID
	}
	return chatJID
}

// resolveActionParticipant looks up the author of messageID in chatJID (D2,
// task 6) for the react/revoke third-party-in-group path: from_me=false in a
// group needs the participant's JID as actionSenderJID's participantJID, not
// the group's own JID. Reuses GetMessageForQuote (task 4) and the same D9
// unknown-author judgment as citing (isUnknownAuthor) — a message whose
// author isn't tracked stays refused, with the same unknownAuthorMessage
// either way.
func resolveActionParticipant(messageStore *MessageStore, messageID, chatJID string) (types.JID, string, int) {
	if messageStore == nil {
		return types.JID{}, "no message store available", http.StatusInternalServerError
	}
	senderJID, sender, _, _, err := messageStore.GetMessageForQuote(messageID, chatJID)
	if err == sql.ErrNoRows {
		return types.JID{}, unknownAuthorMessage, http.StatusBadRequest
	}
	if err != nil {
		return types.JID{}, fmt.Sprintf("Error looking up message author: %v", err), http.StatusInternalServerError
	}
	if isUnknownAuthor(senderJID, sender, chatJID) {
		return types.JID{}, unknownAuthorMessage, http.StatusBadRequest
	}
	parsed, parseErr := types.ParseJID(senderJID)
	if parseErr != nil {
		return types.JID{}, unknownAuthorMessage, http.StatusBadRequest
	}
	return parsed, "", 0
}

// handleReact returns the handler for POST /api/react. Empty emoji removes an
// existing reaction. Reacting to another participant's message in a group
// (from_me=false) resolves the author from the message's stored sender_jid
// via resolveActionParticipant (task 6, D2) and passes it to actionSenderJID
// as participantJID; only a message whose author is unknown (D9) is still
// refused.
func handleReact(client *whatsmeow.Client, messageStore *MessageStore) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req ReactRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" || req.MessageID == "" {
			http.Error(w, "Invalid request: chat_jid and message_id required", http.StatusBadRequest)
			return
		}
		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid chat_jid: %v", err), http.StatusBadRequest)
			return
		}
		var participantJID types.JID
		if !req.FromMe && chatJID.Server == types.GroupServer {
			resolved, errMsg, statusCode := resolveActionParticipant(messageStore, req.MessageID, req.ChatJID)
			if errMsg != "" {
				w.Header().Set("Content-Type", "application/json")
				w.WriteHeader(statusCode)
				json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: errMsg})
				return
			}
			participantJID = resolved
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		senderJID := actionSenderJID(client.Store.ID, chatJID, participantJID, req.FromMe)
		builtMsg := client.BuildReaction(chatJID, senderJID, types.MessageID(req.MessageID), req.Emoji)
		if _, err := client.SendMessage(context.Background(), chatJID, builtMsg); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("SendMessage error: %v", err)})
			return
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(MarkChatResponse{Success: true, Message: fmt.Sprintf("Reaction sent to message %s", req.MessageID)})
	}
}

// handleEdit returns the handler for POST /api/edit. Editing is always the
// caller's own message (WhatsApp only allows editing your own messages), so
// there's no group/from_me ambiguity to guard against here.
func handleEdit(client *whatsmeow.Client, messageStore *MessageStore) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req EditRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" || req.MessageID == "" {
			http.Error(w, "Invalid request: chat_jid and message_id required", http.StatusBadRequest)
			return
		}
		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid chat_jid: %v", err), http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		newContent := &waProto.Message{Conversation: proto.String(req.NewText)}
		builtMsg := client.BuildEdit(chatJID, types.MessageID(req.MessageID), newContent)
		if _, err := client.SendMessage(context.Background(), chatJID, builtMsg); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("SendMessage error: %v", err)})
			return
		}
		// Issue #21 (D3): a single-device account gets no echo of its own
		// action, so the local store needs the same edit applied here.
		if messageStore != nil {
			applyProtocolMessage(messageStore, localChatKey(client, chatJID), &waProto.ProtocolMessage{
				Type:          waProto.ProtocolMessage_MESSAGE_EDIT.Enum(),
				Key:           &waProto.MessageKey{ID: proto.String(req.MessageID)},
				EditedMessage: newContent,
			}, time.Now().Round(0), waLog.Noop)
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(MarkChatResponse{Success: true, Message: fmt.Sprintf("Message %s edited", req.MessageID)})
	}
}

// handleRevoke returns the handler for POST /api/revoke. Revoking another
// participant's message in a group (from_me=false) resolves the author from
// the message's stored sender_jid via resolveActionParticipant (task 6, D2)
// and passes it to actionSenderJID as participantJID; only a message whose
// author is unknown (D9) is still refused — same reasoning as handleReact.
func handleRevoke(client *whatsmeow.Client, messageStore *MessageStore) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req RevokeRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" || req.MessageID == "" {
			http.Error(w, "Invalid request: chat_jid and message_id required", http.StatusBadRequest)
			return
		}
		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid chat_jid: %v", err), http.StatusBadRequest)
			return
		}
		var participantJID types.JID
		if !req.FromMe && chatJID.Server == types.GroupServer {
			resolved, errMsg, statusCode := resolveActionParticipant(messageStore, req.MessageID, req.ChatJID)
			if errMsg != "" {
				w.Header().Set("Content-Type", "application/json")
				w.WriteHeader(statusCode)
				json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: errMsg})
				return
			}
			participantJID = resolved
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		senderJID := actionSenderJID(client.Store.ID, chatJID, participantJID, req.FromMe)
		builtMsg := client.BuildRevoke(chatJID, senderJID, types.MessageID(req.MessageID))
		if _, err := client.SendMessage(context.Background(), chatJID, builtMsg); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("SendMessage error: %v", err)})
			return
		}
		// Issue #21 (D3): a single-device account gets no echo of its own
		// action, so the local store needs the same revoke applied here.
		if messageStore != nil {
			applyProtocolMessage(messageStore, localChatKey(client, chatJID), &waProto.ProtocolMessage{
				Type: waProto.ProtocolMessage_REVOKE.Enum(),
				Key:  &waProto.MessageKey{ID: proto.String(req.MessageID)},
			}, time.Now().Round(0), waLog.Noop)
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(MarkChatResponse{Success: true, Message: fmt.Sprintf("Message %s revoked", req.MessageID)})
	}
}

// GroupParticipantsRequest represents a request to add, remove, promote or
// demote participants in a group.
type GroupParticipantsRequest struct {
	GroupJID     string   `json:"group_jid"`
	Participants []string `json:"participants"`
	Action       string   `json:"action"`
}

// GroupParticipantResult is the per-participant outcome of a group
// participants update.
type GroupParticipantResult struct {
	// Nem JID nem numero: o que volta e o ref opaco com que se aponta esta
	// pessoa de novo, pela mesma razao que /api/group_info parou de devolver
	// telefone de participante.
	Ref        string `json:"ref"`
	IsAdmin    bool   `json:"is_admin"`
	Error      int    `json:"error"`
	AddRequest bool   `json:"add_request,omitempty"`
}

// GroupParticipantsResponse represents the response for
// POST /api/group_participants. Success means the call was accepted by
// WhatsApp, not that every participant change applied — inspect Participants.
type GroupParticipantsResponse struct {
	Success      bool                     `json:"success"`
	Message      string                   `json:"message"`
	Participants []GroupParticipantResult `json:"participants,omitempty"`
}

// Gap #12 — Group Invites
type GroupInviteLinkRequest struct {
	GroupJID string `json:"group_jid"`
	Reset    bool   `json:"reset"`
}

type GroupInviteLinkResponse struct {
	Success bool   `json:"success"`
	Message string `json:"message"`
	Link    string `json:"link,omitempty"`
}

type GroupInviteInfoRequest struct {
	Link string `json:"link"`
}

// GroupInviteInfoResponse represents the response for POST /api/group_invite_info.
//
// Deliberately no is_locked/is_announce: the group node in an invite-query
// response carries no "locked"/"announcement" child, so parseGroupNode leaves
// both false no matter the group's real state. Confirmed by smoke — setting
// both to true and re-reading through this endpoint still reported false.
// An always-false field is worse than an absent one, so those flags are read
// through /api/group_info (full GetGroupInfo) instead.
type GroupInviteInfoResponse struct {
	Success      bool     `json:"success"`
	Message      string   `json:"message"`
	JID          string   `json:"jid,omitempty"`
	Name         string   `json:"name,omitempty"`
	Topic        string   `json:"topic,omitempty"`
	Participants []string `json:"participants,omitempty"`
}

type JoinGroupRequest struct {
	Link string `json:"link"`
}

type JoinGroupResponse struct {
	Success bool   `json:"success"`
	Message string `json:"message"`
	JID     string `json:"jid,omitempty"`
}

// Gap #13 — Group Settings & Photo
type GroupSettingsRequest struct {
	GroupJID string  `json:"group_jid"`
	Name     *string `json:"name"`
	Topic    *string `json:"topic"`
	Announce *bool   `json:"announce"`
	Locked   *bool   `json:"locked"`
}

type GroupSettingResult struct {
	Field   string `json:"field"`
	Success bool   `json:"success"`
	Error   string `json:"error,omitempty"`
}

type GroupSettingsResponse struct {
	Success bool                 `json:"success"`
	Message string               `json:"message"`
	Results []GroupSettingResult `json:"results,omitempty"`
}

type GroupPhotoRequest struct {
	GroupJID  string `json:"group_jid"`
	MediaPath string `json:"media_path"`
	Remove    bool   `json:"remove"`
}

type GroupPhotoResponse struct {
	Success   bool   `json:"success"`
	Message   string `json:"message"`
	PictureID string `json:"picture_id,omitempty"`
}

// Gap #10 — User Info
type UserInfoRequest struct {
	JIDs []string `json:"jids"`
}

type UserInfoResult struct {
	Query        string   `json:"query"`
	JID          string   `json:"jid,omitempty"`
	Found        bool     `json:"found"`
	Status       string   `json:"status,omitempty"`
	PictureID    string   `json:"picture_id,omitempty"`
	VerifiedName string   `json:"verified_name,omitempty"`
	LID          string   `json:"lid,omitempty"`
	Devices      []string `json:"devices,omitempty"`
}

type UserInfoResponse struct {
	Success bool             `json:"success"`
	Message string           `json:"message"`
	Results []UserInfoResult `json:"results,omitempty"`
}

type ProfilePictureRequest struct {
	JID     string `json:"jid"`
	Preview bool   `json:"preview"`
}

type ProfilePictureResponse struct {
	Success    bool   `json:"success"`
	Message    string `json:"message"`
	URL        string `json:"url,omitempty"`
	ID         string `json:"id,omitempty"`
	Type       string `json:"type,omitempty"`
	DirectPath string `json:"direct_path,omitempty"`
}

const maxUserInfoJIDs = 20

var participantChangeByAction = map[string]whatsmeow.ParticipantChange{
	"add":     whatsmeow.ParticipantChangeAdd,
	"remove":  whatsmeow.ParticipantChangeRemove,
	"promote": whatsmeow.ParticipantChangePromote,
	"demote":  whatsmeow.ParticipantChangeDemote,
}

// parseGroupParticipantJIDs turns raw participant strings (bare phone numbers
// or full JIDs) into types.JID. Bare numbers are normalized via normalizePhone
// and assigned DefaultUserServer; full JIDs must be DefaultUserServer or
// HiddenUserServer (LID), since those are the only servers valid as group
// participants. Empty items after trimming are a hard error, not skipped.
func parseGroupParticipantJIDs(participants []string, groupJID string) ([]types.JID, error) {
	jids := make([]types.JID, 0, len(participants))
	for _, p := range participants {
		p = strings.TrimSpace(p)
		if p == "" {
			return nil, fmt.Errorf("Invalid participant: empty string")
		}
		var jid types.JID
		if refID, isRef := strings.CutPrefix(p, "ref:"); isRef {
			// O ref opaco que /api/group_info devolve. E o unico jeito de
			// apontar um membro sem que o numero dele passe pela resposta de
			// API, e ele e preso ao grupo que o emitiu — como o da D6.
			alvo, _, ok := resolveMentionRef(refID, groupJID)
			if !ok {
				return nil, fmt.Errorf("Participant ref %q expired or unknown for this group — read the group again", refID)
			}
			parsed, err := types.ParseJID(alvo)
			if err != nil {
				return nil, fmt.Errorf("Participant ref %q does not resolve to an addressable participant", refID)
			}
			jids = append(jids, parsed)
			continue
		}
		if strings.Contains(p, "@") {
			var err error
			jid, err = types.ParseJID(p)
			if err != nil {
				return nil, fmt.Errorf("Invalid participant JID %q: %v", p, err)
			}
			if jid.Server != types.DefaultUserServer && jid.Server != types.HiddenUserServer {
				return nil, fmt.Errorf("Invalid participant JID %q: unsupported server %q", p, jid.Server)
			}
		} else {
			jid = types.JID{User: normalizePhone(p), Server: types.DefaultUserServer}
		}
		jids = append(jids, jid)
	}
	if len(jids) == 0 {
		return nil, fmt.Errorf("No valid participants after parsing")
	}
	return jids, nil
}

// participantesPorNome descreve os membros de um grupo sem endereco nenhum: o
// nome mais especifico que se conhece de cada um (pela mesma regua da D3, que
// recusa nome com cara de telefone), se e admin, e um `ref` opaco com que
// /api/group_participants aceita aponta-lo de volta.
//
// Os rotulos passam por rotulosDistintos pelo mesmo motivo da D6: dois membros
// sob o mesmo nome deixam quem le sem como apontar um deles.
func participantesPorNome(store *MessageStore, groupInfo *types.GroupInfo, groupJID string) []map[string]interface{} {
	matches := make([]mentionMatch, 0, len(groupInfo.Participants))
	pessoas := make([]mentionParticipant, 0, len(groupInfo.Participants))
	for _, gp := range groupInfo.Participants {
		p := participanteDoGrupo(gp)
		store.fillSenderNames(&p)
		pessoas = append(pessoas, p)
		nome := rotuloDoParticipante(p, "")
		if nome == "" {
			nome = gp.DisplayName
		}
		if nome == "" || len(digitosDe(nome)) >= 8 {
			nome = contatoSemNome
		}
		matches = append(matches, mentionMatch{jid: p.jid, name: nome})
	}
	rotulos := rotulosDistintos(pessoas, matches)

	saida := make([]map[string]interface{}, 0, len(groupInfo.Participants))
	for i, gp := range groupInfo.Participants {
		saida = append(saida, map[string]interface{}{
			"name":           rotulos[i],
			"is_admin":       gp.IsAdmin,
			"is_super_admin": gp.IsSuperAdmin,
			"ref":            storeMentionRef(pessoas[i].jid, rotulos[i], groupJID),
		})
	}
	return saida
}

// youAreAdminIn reports whether the bridge's own account is an admin of this
// group, comparing all three forms a participant can come back as (JID,
// PhoneNumber, LID — same trio participanteDoGrupo already juggles) against
// our own JID, normalized with ToNonAD so a device suffix never breaks the
// match. This stays a plain bool specifically so callers never see anyone's
// raw JID here — the redaction a few lines up (D3/D6) still holds.
func youAreAdminIn(client *whatsmeow.Client, groupInfo *types.GroupInfo) bool {
	if client == nil || client.Store == nil || client.Store.ID == nil {
		return false
	}
	ownJID := client.Store.ID.ToNonAD().String()
	for _, gp := range groupInfo.Participants {
		for _, candidate := range []types.JID{gp.JID, gp.PhoneNumber, gp.LID} {
			if !candidate.IsEmpty() && candidate.ToNonAD().String() == ownJID {
				return gp.IsAdmin
			}
		}
	}
	return false
}

// contatoSemNome e o marcador que a superficie de leitura ja usa quando o nome
// nao resolve. Escrito igual dos dois lados de proposito: e o mesmo texto do
// UNNAMED_CONTACT do servidor MCP.
const contatoSemNome = "(contato sem nome)"

// handleGroupParticipants returns the handler for POST /api/group_participants.
func handleGroupParticipants(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req GroupParticipantsRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.GroupJID == "" || len(req.Participants) == 0 {
			http.Error(w, "Invalid request: group_jid and participants required", http.StatusBadRequest)
			return
		}
		groupJID, err := types.ParseJID(req.GroupJID)
		if err != nil || groupJID.Server != types.GroupServer {
			http.Error(w, "Invalid group_jid: must be a @g.us JID", http.StatusBadRequest)
			return
		}
		action, ok := participantChangeByAction[req.Action]
		if !ok {
			http.Error(w, "Invalid action: must be one of add, remove, promote, demote", http.StatusBadRequest)
			return
		}
		participantJIDs, err := parseGroupParticipantJIDs(req.Participants, groupJID.String())
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(GroupParticipantsResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		results, err := client.UpdateGroupParticipants(r.Context(), groupJID, participantJIDs, action)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(GroupParticipantsResponse{Success: false, Message: fmt.Sprintf("UpdateGroupParticipants error: %v", err)})
			return
		}
		participants := make([]GroupParticipantResult, 0, len(results))
		for _, p := range results {
			participants = append(participants, GroupParticipantResult{
				Ref:        storeMentionRef(p.JID.String(), "", groupJID.String()),
				IsAdmin:    p.IsAdmin,
				Error:      p.Error,
				AddRequest: p.AddRequest != nil,
			})
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(GroupParticipantsResponse{
			Success:      true,
			Message:      fmt.Sprintf("%s applied to %d participant(s)", req.Action, len(participants)),
			Participants: participants,
		})
	}
}

// T001 — Gap #12 handlers: group invites

// handleGroupInviteLink returns the handler for POST /api/group_invite_link.
func handleGroupInviteLink(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req GroupInviteLinkRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.GroupJID == "" {
			http.Error(w, "Invalid request: group_jid required", http.StatusBadRequest)
			return
		}
		groupJID, err := types.ParseJID(req.GroupJID)
		if err != nil || groupJID.Server != types.GroupServer {
			http.Error(w, "Invalid group_jid: must be a @g.us JID", http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(GroupInviteLinkResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		link, err := client.GetGroupInviteLink(r.Context(), groupJID, req.Reset)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(GroupInviteLinkResponse{Success: false, Message: fmt.Sprintf("GetGroupInviteLink error: %v", err)})
			return
		}
		msgSuffix := "retrieved"
		if req.Reset {
			msgSuffix = "reset"
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(GroupInviteLinkResponse{
			Success: true,
			Message: fmt.Sprintf("invite link %s", msgSuffix),
			Link:    link,
		})
	}
}

// handleGroupInviteInfo returns the handler for POST /api/group_invite_info.
func handleGroupInviteInfo(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req GroupInviteInfoRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.Link == "" {
			http.Error(w, "Invalid request: link required", http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(GroupInviteInfoResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		info, err := client.GetGroupInfoFromLink(r.Context(), req.Link)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(GroupInviteInfoResponse{Success: false, Message: fmt.Sprintf("GetGroupInfoFromLink error: %v", err)})
			return
		}
		participants := make([]string, 0, len(info.Participants))
		for _, p := range info.Participants {
			participants = append(participants, p.JID.String())
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(GroupInviteInfoResponse{
			Success:      true,
			Message:      "group info retrieved",
			JID:          info.JID.String(),
			Name:         info.GroupName.Name,
			Topic:        info.Topic,
			Participants: participants,
		})
	}
}

// handleJoinGroup returns the handler for POST /api/join_group_with_link.
func handleJoinGroup(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req JoinGroupRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.Link == "" {
			http.Error(w, "Invalid request: link required", http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(JoinGroupResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		jid, err := client.JoinGroupWithLink(r.Context(), req.Link)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(JoinGroupResponse{Success: false, Message: fmt.Sprintf("JoinGroupWithLink error: %v", err)})
			return
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(JoinGroupResponse{
			Success: true,
			Message: "joined group (or membership request sent)",
			JID:     jid.String(),
		})
	}
}

// T002 — Gap #13 handlers: group settings and photo

// handleGroupSettings returns the handler for POST /api/group_settings.
func handleGroupSettings(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req GroupSettingsRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.GroupJID == "" {
			http.Error(w, "Invalid request: group_jid required", http.StatusBadRequest)
			return
		}
		groupJID, err := types.ParseJID(req.GroupJID)
		if err != nil || groupJID.Server != types.GroupServer {
			http.Error(w, "Invalid group_jid: must be a @g.us JID", http.StatusBadRequest)
			return
		}
		if req.Name == nil && req.Topic == nil && req.Announce == nil && req.Locked == nil {
			http.Error(w, "Invalid request: at least one of name, topic, announce, locked is required", http.StatusBadRequest)
			return
		}
		if req.Name != nil {
			trimmed := strings.TrimSpace(*req.Name)
			if trimmed == "" {
				http.Error(w, "Group name is required", http.StatusBadRequest)
				return
			}
			if len([]rune(trimmed)) > 25 {
				http.Error(w, "Group name must be 25 characters or fewer", http.StatusBadRequest)
				return
			}
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(GroupSettingsResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		results := make([]GroupSettingResult, 0, 4)
		successCount := 0
		if req.Name != nil {
			err := client.SetGroupName(r.Context(), groupJID, *req.Name)
			result := GroupSettingResult{Field: "name", Success: err == nil}
			if err != nil {
				result.Error = err.Error()
			} else {
				successCount++
			}
			results = append(results, result)
		}
		if req.Topic != nil {
			err := client.SetGroupTopic(r.Context(), groupJID, "", "", *req.Topic)
			result := GroupSettingResult{Field: "topic", Success: err == nil}
			if err != nil {
				result.Error = err.Error()
			} else {
				successCount++
			}
			results = append(results, result)
		}
		if req.Announce != nil {
			err := client.SetGroupAnnounce(r.Context(), groupJID, *req.Announce)
			result := GroupSettingResult{Field: "announce", Success: err == nil}
			if err != nil {
				result.Error = err.Error()
			} else {
				successCount++
			}
			results = append(results, result)
		}
		if req.Locked != nil {
			err := client.SetGroupLocked(r.Context(), groupJID, *req.Locked)
			result := GroupSettingResult{Field: "locked", Success: err == nil}
			if err != nil {
				result.Error = err.Error()
			} else {
				successCount++
			}
			results = append(results, result)
		}
		w.Header().Set("Content-Type", "application/json")
		success := successCount == len(results)
		json.NewEncoder(w).Encode(GroupSettingsResponse{
			Success: success,
			Message: fmt.Sprintf("%d of %d setting(s) applied", successCount, len(results)),
			Results: results,
		})
	}
}

// handleGroupPhoto returns the handler for POST /api/group_photo.
func handleGroupPhoto(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req GroupPhotoRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.GroupJID == "" {
			http.Error(w, "Invalid request: group_jid required", http.StatusBadRequest)
			return
		}
		groupJID, err := types.ParseJID(req.GroupJID)
		if err != nil || groupJID.Server != types.GroupServer {
			http.Error(w, "Invalid group_jid: must be a @g.us JID", http.StatusBadRequest)
			return
		}
		if req.Remove {
			if req.MediaPath != "" {
				http.Error(w, "Invalid request: media_path must be empty when remove=true", http.StatusBadRequest)
				return
			}
		} else {
			if req.MediaPath == "" {
				http.Error(w, "Invalid request: media_path required when remove=false", http.StatusBadRequest)
				return
			}
		}
		var avatar []byte
		if !req.Remove {
			data, err := os.ReadFile(req.MediaPath)
			if err != nil {
				http.Error(w, fmt.Sprintf("Failed to read media file: %v", err), http.StatusBadRequest)
				return
			}
			avatar = data
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(GroupPhotoResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		pictureID, err := client.SetGroupPhoto(r.Context(), groupJID, avatar)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(GroupPhotoResponse{Success: false, Message: fmt.Sprintf("SetGroupPhoto error: %v", err)})
			return
		}
		msgSuffix := "updated"
		if req.Remove {
			msgSuffix = "removed"
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(GroupPhotoResponse{
			Success:   true,
			Message:   fmt.Sprintf("group photo %s", msgSuffix),
			PictureID: pictureID,
		})
	}
}

// T003 — Gap #10 handlers: user info

// handleUserInfo returns the handler for POST /api/user_info.
func handleUserInfo(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req UserInfoRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || len(req.JIDs) == 0 {
			http.Error(w, "Invalid request: jids required", http.StatusBadRequest)
			return
		}
		if len(req.JIDs) > maxUserInfoJIDs {
			http.Error(w, fmt.Sprintf("Too many jids: max %d, got %d", maxUserInfoJIDs, len(req.JIDs)), http.StatusBadRequest)
			return
		}
		// Sem grupo no contexto: um ref de grupo NAO resolve aqui, e e assim
		// que tem de ser — ele e preso a conversa que o emitiu.
		jids, err := parseGroupParticipantJIDs(req.JIDs, "")
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(UserInfoResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		userInfoMap, err := client.GetUserInfo(r.Context(), jids)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(UserInfoResponse{Success: false, Message: fmt.Sprintf("GetUserInfo error: %v", err)})
			return
		}
		queryStrings := make([]string, len(jids))
		for i, jid := range jids {
			queryStrings[i] = jid.String()
		}
		results := mergeUserInfoResults(queryStrings, userInfoMap)
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(UserInfoResponse{
			Success: true,
			Message: fmt.Sprintf("%d user(s) info retrieved", len(results)),
			Results: results,
		})
	}
}

// handleProfilePicture returns the handler for POST /api/profile_picture.
func handleProfilePicture(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req ProfilePictureRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.JID == "" {
			http.Error(w, "Invalid request: jid required", http.StatusBadRequest)
			return
		}
		jid, err := types.ParseJID(req.JID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid jid: %v", err), http.StatusBadRequest)
			return
		}
		if jid.Server != types.DefaultUserServer && jid.Server != types.HiddenUserServer && jid.Server != types.GroupServer {
			http.Error(w, "Invalid jid: unsupported server", http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(ProfilePictureResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		info, err := client.GetProfilePictureInfo(r.Context(), jid, &whatsmeow.GetProfilePictureParams{Preview: req.Preview})
		if err != nil {
			if errors.Is(err, whatsmeow.ErrProfilePictureNotSet) {
				w.Header().Set("Content-Type", "application/json")
				json.NewEncoder(w).Encode(ProfilePictureResponse{Success: false, Message: "no profile picture set"})
				return
			}
			if errors.Is(err, whatsmeow.ErrProfilePictureUnauthorized) {
				w.Header().Set("Content-Type", "application/json")
				json.NewEncoder(w).Encode(ProfilePictureResponse{Success: false, Message: "profile picture hidden by privacy settings"})
				return
			}
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(ProfilePictureResponse{Success: false, Message: fmt.Sprintf("GetProfilePictureInfo error: %v", err)})
			return
		}
		if info == nil {
			w.Header().Set("Content-Type", "application/json")
			json.NewEncoder(w).Encode(ProfilePictureResponse{Success: false, Message: "no profile picture available"})
			return
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(ProfilePictureResponse{
			Success:    true,
			Message:    "profile picture info retrieved",
			URL:        info.URL,
			ID:         info.ID,
			Type:       info.Type,
			DirectPath: info.DirectPath,
		})
	}
}

// Gap #11: Poll types and handlers (T004)

type CreatePollRequest struct {
	ChatJID         string   `json:"chat_jid"`
	Question        string   `json:"question"`
	Options         []string `json:"options"`
	SelectableCount int      `json:"selectable_count"`
}

type CreatePollResponse struct {
	Success   bool   `json:"success"`
	Message   string `json:"message"`
	MessageID string `json:"message_id,omitempty"`
}

type VotePollRequest struct {
	ChatJID string   `json:"chat_jid"`
	PollID  string   `json:"poll_id"`
	Options []string `json:"options"`
}

type PollResultsRequest struct {
	ChatJID string `json:"chat_jid"`
	PollID  string `json:"poll_id"`
}

type PollOptionResult struct {
	Option string   `json:"option"`
	Count  int      `json:"count"`
	Voters []string `json:"voters,omitempty"`
}

type PollResultsResponse struct {
	Success         bool               `json:"success"`
	Message         string             `json:"message"`
	Question        string             `json:"question,omitempty"`
	Results         []PollOptionResult `json:"results,omitempty"`
	TotalVoters     int                `json:"total_voters"`
	UnresolvedVotes int                `json:"unresolved_votes"`
}

// handleCreatePoll returns the handler for POST /api/create_poll
func handleCreatePoll(client *whatsmeow.Client, messageStore *MessageStore) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		var req CreatePollRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request: could not decode JSON", http.StatusBadRequest)
			return
		}

		// Validation
		req.ChatJID = strings.TrimSpace(req.ChatJID)
		if req.ChatJID == "" {
			http.Error(w, "Invalid request: chat_jid required", http.StatusBadRequest)
			return
		}

		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, "Invalid chat_jid", http.StatusBadRequest)
			return
		}

		req.Question = strings.TrimSpace(req.Question)
		if req.Question == "" {
			http.Error(w, "Invalid request: question cannot be empty", http.StatusBadRequest)
			return
		}

		if len(req.Options) < 2 || len(req.Options) > 12 {
			http.Error(w, "Invalid options: must have between 2 and 12 options", http.StatusBadRequest)
			return
		}

		// Trim in place, not just in the loop variable: the trimmed form is what
		// gets validated, so it has to also be what is sent and stored. Otherwise
		// " Sim" passes the duplicate check as "Sim" but reaches WhatsApp — and
		// polls.options — with the leading space still on it.
		seenOptions := make(map[string]bool)
		for i, opt := range req.Options {
			opt = strings.TrimSpace(opt)
			if opt == "" {
				http.Error(w, "Invalid options: names must be unique and non-empty", http.StatusBadRequest)
				return
			}
			if seenOptions[opt] {
				http.Error(w, "Invalid options: names must be unique and non-empty", http.StatusBadRequest)
				return
			}
			seenOptions[opt] = true
			req.Options[i] = opt
		}

		if req.SelectableCount < 1 || req.SelectableCount > len(req.Options) {
			http.Error(w, "Invalid request: selectable_count must be between 1 and number of options", http.StatusBadRequest)
			return
		}

		// Check client connection
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(CreatePollResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}

		// Build and send poll
		msg := client.BuildPollCreation(req.Question, req.Options, req.SelectableCount)
		resp, err := client.SendMessage(r.Context(), chatJID, msg)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(CreatePollResponse{Success: false, Message: fmt.Sprintf("SendMessage error: %v", err)})
			return
		}

		// The chat row has to exist first: polls carries a foreign key to
		// chats(jid) and foreign keys are enforced on this connection, so
		// storing a poll in a chat we've never written would fail outright —
		// the poll would go out on WhatsApp and then be unknown to vote_poll
		// and poll_results.
		if messageStore != nil && client.Store != nil && client.Store.ID != nil {
			if ensureErr := messageStore.EnsureChat(chatJID.String(), resp.Timestamp); ensureErr != nil {
				fmt.Printf("Failed to ensure chat row for poll: %v\n", ensureErr)
			}
		}

		// Store poll in database
		optionsJSON, _ := json.Marshal(req.Options)
		if err := messageStore.StorePoll(
			resp.ID,
			chatJID.String(),
			client.Store.ID.String(),
			req.Question,
			string(optionsJSON),
			req.SelectableCount,
			time.Now().Unix(),
		); err != nil {
			// Log but don't fail the response - poll was sent even if storage failed
			fmt.Printf("Failed to store poll in database: %v\n", err)
		}

		// Persist the poll as a message too, for the same reason /api/send does
		// it (main.go, sendWhatsAppMessage): on a single-device account the
		// multi-device echo never fires, so handleMessage never sees our own
		// poll and RN-02 would hold only for polls received from other people.
		// Without this, create_poll leaves a hole in list_messages exactly where
		// the poll is.
		if messageStore != nil && client.Store != nil && client.Store.ID != nil {
			if storeErr := messageStore.StoreMessage(
				resp.ID, chatJID.String(), client.Store.ID.User, req.Question,
				resp.Timestamp, true, "", "", "", nil, nil, nil, 0,
			); storeErr != nil {
				fmt.Printf("Failed to store poll message: %v\n", storeErr)
			}
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(CreatePollResponse{
			Success:   true,
			Message:   "Poll created and sent",
			MessageID: resp.ID,
		})
	}
}

// handleVotePoll returns the handler for POST /api/vote_poll
func handleVotePoll(client *whatsmeow.Client, messageStore *MessageStore) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		var req VotePollRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" || req.PollID == "" {
			http.Error(w, "Invalid request: chat_jid and poll_id required", http.StatusBadRequest)
			return
		}

		// Get poll from database
		_, optionsJSON, selectableCount, senderJID, err := messageStore.GetPoll(req.PollID, req.ChatJID)
		if err == sql.ErrNoRows {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusNotFound)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"message": "Poll not found. The bridge may not know this poll if it was created before this feature was enabled.",
			})
			return
		}
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"message": fmt.Sprintf("Database error: %v", err),
			})
			return
		}

		// Validate options exist in poll
		var pollOptions []string
		if err := json.Unmarshal([]byte(optionsJSON), &pollOptions); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"message": "Failed to parse poll options",
			})
			return
		}

		pollOptionsMap := make(map[string]bool)
		for _, opt := range pollOptions {
			pollOptionsMap[opt] = true
		}

		var invalidOptions []string
		for _, opt := range req.Options {
			if !pollOptionsMap[opt] {
				invalidOptions = append(invalidOptions, opt)
			}
		}
		if len(invalidOptions) > 0 {
			http.Error(w, fmt.Sprintf("Invalid options: %v", invalidOptions), http.StatusBadRequest)
			return
		}

		// Validate selectable_count
		if selectableCount > 0 && len(req.Options) > selectableCount {
			http.Error(w, "Too many options selected", http.StatusBadRequest)
			return
		}

		// Check client connection
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"message": "WhatsApp client not connected",
			})
			return
		}

		// Reconstruct MessageInfo for the poll creation message
		pollJID, _ := types.ParseJID(req.ChatJID)
		senderJIDParsed, _ := types.ParseJID(senderJID)
		pollInfo := types.MessageInfo{
			ID: req.PollID,
			MessageSource: types.MessageSource{
				Chat:   pollJID,
				Sender: senderJIDParsed,
			},
		}

		// Build and send vote
		msg, err := client.BuildPollVote(r.Context(), &pollInfo, req.Options)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"message": fmt.Sprintf("BuildPollVote error: %v", err),
			})
			return
		}
		resp, err := client.SendMessage(r.Context(), pollJID, msg)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false,
				"message": fmt.Sprintf("SendMessage error: %v", err),
			})
			return
		}

		// Record our own vote directly, for the same reason handleCreatePoll
		// stores its own message: on a single-device account the multi-device
		// echo never fires, so handleMessage never sees this PollUpdateMessage
		// and the vote we just cast would be missing from our own tally. Found
		// by smoke — the vote sent fine and poll_results stayed at zero.
		if messageStore != nil && client.Store != nil && client.Store.ID != nil {
			selectedJSON, err := json.Marshal(req.Options)
			if err != nil {
				fmt.Printf("Failed to encode own vote: %v\n", err)
			} else if storeErr := messageStore.UpsertPollVote(
				req.PollID, req.ChatJID, client.Store.ID.ToNonAD().String(),
				string(selectedJSON), 1, resp.Timestamp.Unix(),
			); storeErr != nil {
				fmt.Printf("Failed to store own poll vote: %v\n", storeErr)
			}
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]interface{}{
			"success": true,
			"message": "Vote submitted",
		})
	}
}

// handlePollResults returns the handler for POST /api/poll_results
func handlePollResults(messageStore *MessageStore) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		var req PollResultsRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" || req.PollID == "" {
			http.Error(w, "Invalid request: chat_jid and poll_id required", http.StatusBadRequest)
			return
		}

		// Get poll
		question, optionsJSON, _, _, err := messageStore.GetPoll(req.PollID, req.ChatJID)
		if err == sql.ErrNoRows {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusNotFound)
			json.NewEncoder(w).Encode(PollResultsResponse{
				Success: false,
				Message: "Poll not found",
			})
			return
		}
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(PollResultsResponse{
				Success: false,
				Message: fmt.Sprintf("Database error: %v", err),
			})
			return
		}

		// Parse poll options
		var pollOptions []string
		if err := json.Unmarshal([]byte(optionsJSON), &pollOptions); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(PollResultsResponse{
				Success: false,
				Message: "Failed to parse poll options",
			})
			return
		}

		// Get all votes
		votes, err := messageStore.GetPollVotes(req.PollID, req.ChatJID)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(PollResultsResponse{
				Success: false,
				Message: fmt.Sprintf("Database error: %v", err),
			})
			return
		}

		// Build results
		optionCounts := make(map[string]int)
		optionVoters := make(map[string]map[string]bool)
		totalVoters := 0
		unresolvedVotes := 0

		for _, option := range pollOptions {
			optionVoters[option] = make(map[string]bool)
		}

		for _, vote := range votes {
			if vote.Resolved == 0 {
				unresolvedVotes++
				continue
			}

			var selectedOptions []string
			if err := json.Unmarshal([]byte(vote.SelectedJSON), &selectedOptions); err != nil {
				continue
			}

			// A withdrawn vote (empty selection) is a resolved, understood vote,
			// but it is not a voter: counting it would let total_voters exceed
			// the sum of the per-option counts, and "3 people voted" would be
			// read as three actual choices.
			if len(selectedOptions) == 0 {
				continue
			}
			totalVoters++

			for _, opt := range selectedOptions {
				optionCounts[opt]++
				optionVoters[opt][vote.VoterJID] = true
			}
		}

		// Build response with all options in original order
		results := make([]PollOptionResult, 0, len(pollOptions))
		for _, option := range pollOptions {
			voters := make([]string, 0)
			for voter := range optionVoters[option] {
				voters = append(voters, voter)
			}
			// Sort for consistent output
			sort.Strings(voters)

			results = append(results, PollOptionResult{
				Option: option,
				Count:  optionCounts[option],
				Voters: voters,
			})
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(PollResultsResponse{
			Success:         true,
			Message:         "Poll results retrieved",
			Question:        question,
			Results:         results,
			TotalVoters:     totalVoters,
			UnresolvedVotes: unresolvedVotes,
		})
	}
}

// ChatPresenceRequest represents a request to send a typing/recording indicator.
type ChatPresenceRequest struct {
	ChatJID string `json:"chat_jid"`
	State   string `json:"state"`
	Media   string `json:"media"`
}

var chatPresenceByState = map[string]types.ChatPresence{
	"composing": types.ChatPresenceComposing,
	"paused":    types.ChatPresencePaused,
}

var chatPresenceMediaByValue = map[string]types.ChatPresenceMedia{
	"":      types.ChatPresenceMediaText,
	"audio": types.ChatPresenceMediaAudio,
}

// handleChatPresence returns the handler for POST /api/chat_presence. Ephemeral:
// nothing is persisted, and there's no timer — the caller is responsible for
// sending "paused" to end the indicator (WhatsApp expires "composing" on its own).
func handleChatPresence(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req ChatPresenceRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" {
			http.Error(w, "Invalid request: chat_jid required", http.StatusBadRequest)
			return
		}
		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid chat_jid: %v", err), http.StatusBadRequest)
			return
		}
		state, ok := chatPresenceByState[req.State]
		if !ok {
			http.Error(w, "Invalid state: must be one of composing, paused", http.StatusBadRequest)
			return
		}
		media, ok := chatPresenceMediaByValue[req.Media]
		if !ok {
			http.Error(w, "Invalid media: must be one of \"\", audio", http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		if err := client.SendChatPresence(r.Context(), chatJID, state, media); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("SendChatPresence error: %v", err)})
			return
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(MarkChatResponse{Success: true, Message: "chat presence sent"})
	}
}

// IsOnWhatsAppRequest represents a request to check phone number registration.
type IsOnWhatsAppRequest struct {
	Phones []string `json:"phones"`
}

// IsOnWhatsAppResult is the per-number outcome of an is_on_whatsapp check.
type IsOnWhatsAppResult struct {
	Query        string `json:"query"`
	JID          string `json:"jid"`
	IsIn         bool   `json:"is_in"`
	VerifiedName string `json:"verified_name,omitempty"`
}

// IsOnWhatsAppApiResponse represents the response for POST /api/is_on_whatsapp.
type IsOnWhatsAppApiResponse struct {
	Success bool                 `json:"success"`
	Message string               `json:"message"`
	Results []IsOnWhatsAppResult `json:"results,omitempty"`
}

const maxIsOnWhatsAppPhones = 50

var checkPhoneRe = regexp.MustCompile(`^\d{8,15}$`)

// normalizeCheckPhones validates and normalizes phone numbers for
// /api/is_on_whatsapp: strips formatting via normalizePhone, rejects anything
// that isn't 8-15 digits after normalization (catches internal spaces/hyphens,
// "00" prefixes, empty items), and caps the list at maxIsOnWhatsAppPhones to
// bound the WhatsApp lookup (also closes a mass-scan vector).
func normalizeCheckPhones(phones []string) ([]string, error) {
	if len(phones) > maxIsOnWhatsAppPhones {
		return nil, fmt.Errorf("Too many phones: max %d, got %d", maxIsOnWhatsAppPhones, len(phones))
	}
	out := make([]string, len(phones))
	for i, p := range phones {
		digits := normalizePhone(strings.TrimSpace(p))
		if !checkPhoneRe.MatchString(digits) {
			return nil, fmt.Errorf("Invalid phone %q: must be 8-15 digits", p)
		}
		out[i] = "+" + digits
	}
	return out, nil
}

// mergeIsOnWhatsAppResults correlates the whatsmeow response (which omits
// unregistered numbers instead of returning IsIn=false for them) with the
// original query list, so the API always returns exactly one result per
// input phone, in input order, with is_in:false filled in for omissions.
func mergeIsOnWhatsAppResults(queries []string, resp []types.IsOnWhatsAppResponse) []IsOnWhatsAppResult {
	byQuery := make(map[string]types.IsOnWhatsAppResponse, len(resp))
	for _, res := range resp {
		byQuery[res.Query] = res
	}
	out := make([]IsOnWhatsAppResult, 0, len(queries))
	for _, q := range queries {
		res, found := byQuery[q]
		if !found {
			out = append(out, IsOnWhatsAppResult{Query: q, IsIn: false})
			continue
		}
		item := IsOnWhatsAppResult{Query: res.Query, IsIn: res.IsIn}
		if res.IsIn {
			item.JID = res.JID.String()
		}
		if res.VerifiedName != nil && res.VerifiedName.Details != nil {
			item.VerifiedName = res.VerifiedName.Details.GetVerifiedName()
		}
		out = append(out, item)
	}
	return out
}

// mergeUserInfoResults correlates the whatsmeow response (which omits
// unregistered users) with the original query list, so the API always returns
// exactly one result per input JID, in input order, with Found:false filled in
// for omissions.
//
// The lookup key is ToNonAD: Client.GetUserInfo delegates to usync, which calls
// jid.ToNonAD() before building the query node, so the returned map is always
// keyed without device/agent. Indexing it with an AD-qualified JID (a caller
// can legitimately pass "5511999999999:26@s.whatsapp.net") would miss every
// time and report Found:false for a user WhatsApp actually resolved. Query
// still echoes the caller's original string so they can correlate.
func mergeUserInfoResults(queries []string, userInfoMap map[types.JID]types.UserInfo) []UserInfoResult {
	out := make([]UserInfoResult, 0, len(queries))
	for _, q := range queries {
		parsed, err := types.ParseJID(q)
		if err != nil {
			// Query should already be validated, but be defensive
			out = append(out, UserInfoResult{Query: q, Found: false})
			continue
		}
		jid := parsed.ToNonAD()
		info, found := userInfoMap[jid]
		if !found {
			out = append(out, UserInfoResult{Query: q, Found: false})
			continue
		}
		item := UserInfoResult{Query: q, Found: true, JID: jid.String()}
		if info.Status != "" {
			item.Status = info.Status
		}
		if info.PictureID != "" {
			item.PictureID = info.PictureID
		}
		if info.VerifiedName != nil && info.VerifiedName.Details != nil {
			item.VerifiedName = info.VerifiedName.Details.GetVerifiedName()
		}
		if !info.LID.IsEmpty() {
			item.LID = info.LID.String()
		}
		if len(info.Devices) > 0 {
			item.Devices = make([]string, 0, len(info.Devices))
			for _, d := range info.Devices {
				item.Devices = append(item.Devices, d.String())
			}
		}
		out = append(out, item)
	}
	return out
}

// handleIsOnWhatsApp returns the handler for POST /api/is_on_whatsapp.
func handleIsOnWhatsApp(client *whatsmeow.Client) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req IsOnWhatsAppRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || len(req.Phones) == 0 {
			http.Error(w, "Invalid request: phones required", http.StatusBadRequest)
			return
		}
		phones, err := normalizeCheckPhones(req.Phones)
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(IsOnWhatsAppApiResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		results, err := client.IsOnWhatsApp(r.Context(), phones)
		if err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(IsOnWhatsAppApiResponse{Success: false, Message: fmt.Sprintf("IsOnWhatsApp error: %v", err)})
			return
		}
		out := mergeIsOnWhatsAppResults(phones, results)
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(IsOnWhatsAppApiResponse{
			Success: true,
			Message: fmt.Sprintf("%d number(s) checked", len(out)),
			Results: out,
		})
	}
}

// MarkChatResponse represents the response for mark-read / mark-unread.
type MarkChatResponse struct {
	Success bool   `json:"success"`
	Message string `json:"message"`
}

// ResolveContactResponse is the response for GET /api/resolve_contact. It moves
// phone->JID resolution (regular + LID) into the bridge, which owns whatsmeow,
// so the Python side no longer reads the library's internal whatsmeow_lid_map
// table directly (decoupling from the lib's physical schema).
type ResolveContactResponse struct {
	Success bool     `json:"success"`
	Message string   `json:"message,omitempty"`
	Phone   string   `json:"phone,omitempty"`
	JIDs    []string `json:"jids,omitempty"`
}

// ContactHit is one contact returned by GET /api/search_contacts.
type ContactHit struct {
	JID         string `json:"jid"`
	PhoneNumber string `json:"phone_number"`
	Name        string `json:"name"`
}

// SearchContactsResponse is the response for GET /api/search_contacts.
type SearchContactsResponse struct {
	Success  bool         `json:"success"`
	Message  string       `json:"message,omitempty"`
	Contacts []ContactHit `json:"contacts,omitempty"`
}

// normalizePhone strips '+', spaces and '-' from a phone number so lookups match
// regardless of formatting. Parity with the Python _normalize_phone helper.
func normalizePhone(phone string) string {
	r := strings.NewReplacer("+", "", " ", "", "-", "")
	return r.Replace(phone)
}

// safeSendAppState calls cli.SendAppState recovering from any panic (e.g. uninitialized
// app-state keys during session restore) and returns it as a regular error.
func safeSendAppState(cli *whatsmeow.Client, ctx context.Context, patch appstate.PatchInfo) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("app state not ready: %v", r)
		}
	}()
	return cli.SendAppState(ctx, patch)
}

// createWhatsAppGroup creates a new group on WhatsApp.
func createWhatsAppGroup(client *whatsmeow.Client, messageStore *MessageStore, req CreateGroupRequest) CreateGroupResponse {
	if !client.IsConnected() {
		return CreateGroupResponse{Success: false, Message: "Not connected to WhatsApp"}
	}
	if strings.TrimSpace(req.Name) == "" {
		return CreateGroupResponse{Success: false, Message: "Group name is required"}
	}
	if len([]rune(req.Name)) > 25 {
		return CreateGroupResponse{Success: false, Message: "Group name must be 25 characters or fewer"}
	}
	if len(req.Participants) == 0 {
		return CreateGroupResponse{Success: false, Message: "At least one participant is required"}
	}

	participantJIDs := make([]types.JID, 0, len(req.Participants))
	for _, p := range req.Participants {
		p = strings.TrimSpace(p)
		if p == "" {
			continue
		}
		var jid types.JID
		var err error
		if strings.Contains(p, "@") {
			jid, err = types.ParseJID(p)
			if err != nil {
				return CreateGroupResponse{Success: false, Message: fmt.Sprintf("Invalid participant JID %q: %v", p, err)}
			}
		} else {
			jid = types.JID{User: strings.TrimPrefix(p, "+"), Server: "s.whatsapp.net"}
		}
		participantJIDs = append(participantJIDs, jid)
	}
	if len(participantJIDs) == 0 {
		return CreateGroupResponse{Success: false, Message: "No valid participants after parsing"}
	}

	createReq := whatsmeow.ReqCreateGroup{
		Name:         req.Name,
		Participants: participantJIDs,
	}
	if req.IsCommunity {
		createReq.GroupParent.IsParent = true
	}
	if req.CommunityParentJID != "" {
		parentJID, err := types.ParseJID(req.CommunityParentJID)
		if err != nil {
			return CreateGroupResponse{Success: false, Message: fmt.Sprintf("Invalid community_parent_jid: %v", err)}
		}
		createReq.GroupLinkedParent.LinkedParentJID = parentJID
	}

	groupInfo, err := client.CreateGroup(context.Background(), createReq)
	if err != nil {
		return CreateGroupResponse{Success: false, Message: fmt.Sprintf("Error creating group: %v", err)}
	}

	createdAt := groupInfo.GroupCreated
	if createdAt.IsZero() {
		createdAt = time.Now()
	}
	if err := messageStore.StoreChat(groupInfo.JID.String(), groupInfo.Name, createdAt); err != nil {
		fmt.Printf("Warning: failed to store newly created group chat: %v\n", err)
	}

	return CreateGroupResponse{
		Success:          true,
		Message:          "Group created",
		JID:              groupInfo.JID.String(),
		Name:             groupInfo.Name,
		ParticipantCount: len(groupInfo.Participants),
	}
}

// leaveWhatsAppGroup leaves the specified group on WhatsApp.
func leaveWhatsAppGroup(client *whatsmeow.Client, jidStr string) LeaveGroupResponse {
	if !client.IsConnected() {
		return LeaveGroupResponse{Success: false, Message: "Not connected to WhatsApp"}
	}
	jidStr = strings.TrimSpace(jidStr)
	if jidStr == "" {
		return LeaveGroupResponse{Success: false, Message: "Group JID is required"}
	}
	jid, err := types.ParseJID(jidStr)
	if err != nil {
		return LeaveGroupResponse{Success: false, Message: fmt.Sprintf("Invalid JID: %v", err)}
	}
	if jid.Server != "g.us" {
		return LeaveGroupResponse{Success: false, Message: "Only group JIDs (@g.us) can be left"}
	}
	if err := client.LeaveGroup(context.Background(), jid); err != nil {
		return LeaveGroupResponse{Success: false, Message: fmt.Sprintf("Error leaving group: %v", err)}
	}
	return LeaveGroupResponse{Success: true, Message: fmt.Sprintf("Left group %s", jid.String())}
}

type DownloadMediaResponse struct {
	Success  bool   `json:"success"`
	Message  string `json:"message"`
	Filename string `json:"filename,omitempty"`
	Path     string `json:"path,omitempty"`
}

// Store additional media info in the database
func (store *MessageStore) StoreMediaInfo(id, chatJID, url string, mediaKey, fileSHA256, fileEncSHA256 []byte, fileLength uint64) error {
	_, err := store.db.Exec(
		"UPDATE messages SET url = ?, media_key = ?, file_sha256 = ?, file_enc_sha256 = ?, file_length = ? WHERE id = ? AND chat_jid = ?",
		url, mediaKey, fileSHA256, fileEncSHA256, fileLength, id, chatJID,
	)
	return err
}

// Get media info from the database
func (store *MessageStore) GetMediaInfo(id, chatJID string) (string, string, string, []byte, []byte, []byte, uint64, error) {
	var mediaType, filename, url string
	var mediaKey, fileSHA256, fileEncSHA256 []byte
	var fileLength uint64

	err := store.db.QueryRow(
		"SELECT media_type, filename, url, media_key, file_sha256, file_enc_sha256, file_length FROM messages WHERE id = ? AND chat_jid = ?",
		id, chatJID,
	).Scan(&mediaType, &filename, &url, &mediaKey, &fileSHA256, &fileEncSHA256, &fileLength)

	return mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength, err
}

// Gap #11: Poll store methods (T002)

// resolvePollVote maps the SHA-256 option hashes in a poll vote back to option
// names, using the poll's stored option list. It returns the JSON array to
// persist in poll_votes.selected and the resolved flag for that column.
//
// A vote carries only hashes (HashPollOptions is sha256 of the option name), so
// without the original option list it is meaningless. Every path that can't
// produce a complete mapping — unknown poll (empty optionsJSON), unparseable
// stored options, or a hash that matches none of them — yields resolved=0 so
// the vote is still recorded and reported as unresolved rather than dropped or,
// worse, counted as if it had been understood (RN-05).
//
// Kept as a pure function on purpose: the hash mapping is the one piece of this
// feature that can be wrong in a way no HTTP test would reveal.
func resolvePollVote(optionsJSON string, selected [][]byte) (selectedJSON string, resolved int) {
	var optionNames []string
	if optionsJSON == "" {
		return "[]", 0
	}
	if err := json.Unmarshal([]byte(optionsJSON), &optionNames); err != nil {
		return "[]", 0
	}
	nameByHash := make(map[string]string, len(optionNames))
	for _, name := range optionNames {
		hash := sha256.Sum256([]byte(name))
		nameByHash[hex.EncodeToString(hash[:])] = name
	}
	names := make([]string, 0, len(selected))
	for _, hash := range selected {
		if name, ok := nameByHash[hex.EncodeToString(hash)]; ok {
			names = append(names, name)
		}
	}
	encoded, err := json.Marshal(names)
	if err != nil {
		return "[]", 0
	}
	// An empty selection is a legitimate, fully-understood vote: it means the
	// voter withdrew their choice. Only a partial mapping is unresolved.
	if len(names) != len(selected) {
		return string(encoded), 0
	}
	return string(encoded), 1
}

// StorePoll stores a poll in the polls table
func (store *MessageStore) StorePoll(id, chatJID, sender, name, optionsJSON string, selectableCount int, timestamp int64) error {
	_, err := store.db.Exec(
		`INSERT INTO polls (id, chat_jid, sender, name, options, selectable_count, timestamp)
		VALUES (?, ?, ?, ?, ?, ?, ?)
		ON CONFLICT(id, chat_jid) DO UPDATE SET
			sender = excluded.sender,
			name = excluded.name,
			options = excluded.options,
			selectable_count = excluded.selectable_count,
			timestamp = excluded.timestamp`,
		id, chatJID, sender, name, optionsJSON, selectableCount, timestamp,
	)
	return err
}

// GetPoll retrieves a poll from the polls table
func (store *MessageStore) GetPoll(pollID, chatJID string) (name, optionsJSON string, selectableCount int, senderJID string, err error) {
	err = store.db.QueryRow(
		"SELECT name, options, selectable_count, sender FROM polls WHERE id = ? AND chat_jid = ?",
		pollID, chatJID,
	).Scan(&name, &optionsJSON, &selectableCount, &senderJID)
	return
}

// UpsertPollVote stores or updates a poll vote with timestamp guard (RN-04)
func (store *MessageStore) UpsertPollVote(pollID, chatJID, voterJID, selectedJSON string, resolved int, timestamp int64) error {
	_, err := store.db.Exec(
		`INSERT INTO poll_votes (poll_id, chat_jid, voter_jid, selected, resolved, timestamp)
		VALUES (?, ?, ?, ?, ?, ?)
		ON CONFLICT(poll_id, chat_jid, voter_jid) DO UPDATE SET
			selected = excluded.selected,
			resolved = excluded.resolved,
			timestamp = excluded.timestamp
		WHERE excluded.timestamp >= poll_votes.timestamp`,
		pollID, chatJID, voterJID, selectedJSON, resolved, timestamp,
	)
	return err
}

// PollVote represents a single vote record
type PollVote struct {
	VoterJID     string
	SelectedJSON string
	Resolved     int
}

// GetPollVotes retrieves all votes for a poll
func (store *MessageStore) GetPollVotes(pollID, chatJID string) ([]PollVote, error) {
	rows, err := store.db.Query(
		"SELECT voter_jid, selected, resolved FROM poll_votes WHERE poll_id = ? AND chat_jid = ? ORDER BY timestamp",
		pollID, chatJID,
	)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	var votes []PollVote
	for rows.Next() {
		var v PollVote
		if err := rows.Scan(&v.VoterJID, &v.SelectedJSON, &v.Resolved); err != nil {
			return nil, err
		}
		votes = append(votes, v)
	}
	return votes, rows.Err()
}

// safeMediaPath builds a media file path inside chatDir, rejecting any message
// ID or filename that could escape the directory via path traversal. Both
// components are partly attacker-influenced (filename comes from the message,
// the retry message ID comes from the phone's response), so they are reduced to
// their base name and checked for separators / dot segments.
func safeMediaPath(chatDir, messageID, filename string) (string, error) {
	// Reject the raw components rather than silently reducing them with
	// filepath.Base — a value containing a separator or dot segment is treated
	// as an attack and surfaced, not sanitized away.
	for _, c := range []string{messageID, filename} {
		if c == "" || c == "." || c == ".." || strings.ContainsAny(c, `/\`) {
			return "", fmt.Errorf("unsafe media path component: %q", c)
		}
	}
	joined := filepath.Join(chatDir, messageID+"_"+filename)
	// Defense in depth: ensure the cleaned result is still under chatDir.
	rel, err := filepath.Rel(chatDir, joined)
	if err != nil || strings.HasPrefix(rel, "..") {
		return "", fmt.Errorf("media path escapes chat directory: %q", joined)
	}
	return joined, nil
}

// MediaDownloader implements the whatsmeow.DownloadableMessage interface
type MediaDownloader struct {
	URL           string
	DirectPath    string
	MediaKey      []byte
	FileLength    uint64
	FileSHA256    []byte
	FileEncSHA256 []byte
	MediaType     whatsmeow.MediaType
}

// GetDirectPath implements the DownloadableMessage interface
func (d *MediaDownloader) GetDirectPath() string {
	return d.DirectPath
}

// GetURL implements the DownloadableMessage interface
func (d *MediaDownloader) GetURL() string {
	return d.URL
}

// GetMediaKey implements the DownloadableMessage interface
func (d *MediaDownloader) GetMediaKey() []byte {
	return d.MediaKey
}

// GetFileLength implements the DownloadableMessage interface
func (d *MediaDownloader) GetFileLength() uint64 {
	return d.FileLength
}

// GetFileSHA256 implements the DownloadableMessage interface
func (d *MediaDownloader) GetFileSHA256() []byte {
	return d.FileSHA256
}

// GetFileEncSHA256 implements the DownloadableMessage interface
func (d *MediaDownloader) GetFileEncSHA256() []byte {
	return d.FileEncSHA256
}

// GetMediaType implements the DownloadableMessage interface
func (d *MediaDownloader) GetMediaType() whatsmeow.MediaType {
	return d.MediaType
}

// Function to download media from a message
// downloadMedia serves the media of a stored message. allowRevoked lets one
// caller through the D2 refusal: get_deleted_message's download=true (D3,
// task 3) — every other caller passes false and keeps being refused.
func downloadMedia(client *whatsmeow.Client, messageStore *MessageStore, messageID, chatJID string, allowRevoked bool) (bool, string, string, string, error) {
	// Query the database for the message
	var mediaType, filename, url string
	var mediaKey, fileSHA256, fileEncSHA256 []byte
	var fileLength uint64
	var err error

	// First, check if we already have this file
	chatDir := fmt.Sprintf("store/%s", strings.ReplaceAll(chatJID, ":", "_"))
	localPath := ""

	// Issue #21: the sender deleted it for everyone — refuse before anything
	// else, including the local-cache hit below.
	if !allowRevoked {
		if revoked, err := messageStore.IsMessageRevoked(messageID, chatJID); err != nil {
			return false, "", "", "", fmt.Errorf("failed to check message: %v", err)
		} else if revoked {
			return false, "", "", "", fmt.Errorf("message was deleted by the sender")
		}
	}

	// Get media info from the database
	mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength, err = messageStore.GetMediaInfo(messageID, chatJID)

	if err != nil {
		// Try to get basic info if extended info isn't available
		err = messageStore.db.QueryRow(
			"SELECT media_type, filename FROM messages WHERE id = ? AND chat_jid = ?",
			messageID, chatJID,
		).Scan(&mediaType, &filename)

		if err != nil {
			return false, "", "", "", fmt.Errorf("failed to find message: %v", err)
		}
	}

	// Check if this is a media message
	if mediaType == "" {
		return false, "", "", "", fmt.Errorf("not a media message")
	}

	// Create directory for the chat if it doesn't exist
	if err := os.MkdirAll(chatDir, 0755); err != nil {
		return false, "", "", "", fmt.Errorf("failed to create chat directory: %v", err)
	}

	// Generate a local path for the file. Prefix with the message ID because the
	// stored filename is derived from sync time and collides across messages
	// received in the same second within a chat (the cache check below would
	// otherwise return the wrong message's bytes).
	localPath, err = safeMediaPath(chatDir, messageID, filename)
	if err != nil {
		return false, "", "", "", err
	}

	// Get absolute path
	absPath, err := filepath.Abs(localPath)
	if err != nil {
		return false, "", "", "", fmt.Errorf("failed to get absolute path: %v", err)
	}

	// Check if file already exists
	if _, err := os.Stat(localPath); err == nil {
		// File exists, return it
		return true, mediaType, filename, absPath, nil
	}

	// If we don't have all the media info we need, we can't download
	if url == "" || len(mediaKey) == 0 || len(fileSHA256) == 0 || len(fileEncSHA256) == 0 || fileLength == 0 {
		return false, "", "", "", fmt.Errorf("incomplete media information for download")
	}

	fmt.Printf("Attempting to download media for message %s in chat %s...\n", messageID, chatJID)

	// Extract direct path from URL
	directPath := extractDirectPathFromURL(url)

	// Create a downloader that implements DownloadableMessage
	var waMediaType whatsmeow.MediaType
	switch mediaType {
	case "image":
		waMediaType = whatsmeow.MediaImage
	case "video":
		waMediaType = whatsmeow.MediaVideo
	case "audio":
		waMediaType = whatsmeow.MediaAudio
	case "document":
		waMediaType = whatsmeow.MediaDocument
	default:
		return false, "", "", "", fmt.Errorf("unsupported media type: %s", mediaType)
	}

	downloader := &MediaDownloader{
		URL:           url,
		DirectPath:    directPath,
		MediaKey:      mediaKey,
		FileLength:    fileLength,
		FileSHA256:    fileSHA256,
		FileEncSHA256: fileEncSHA256,
		MediaType:     waMediaType,
	}

	// Download the media using whatsmeow client
	mediaData, err := client.Download(context.Background(), downloader)
	if err != nil {
		return false, "", "", "", fmt.Errorf("failed to download media: %v", err)
	}

	// Save the downloaded media to file
	if err := os.WriteFile(localPath, mediaData, 0644); err != nil {
		return false, "", "", "", fmt.Errorf("failed to save media file: %v", err)
	}

	fmt.Printf("Successfully downloaded %s media to %s (%d bytes)\n", mediaType, absPath, len(mediaData))
	return true, mediaType, filename, absPath, nil
}

// Extract direct path from a WhatsApp media URL.
//
// The query string is part of the direct path, not decoration: it carries the
// CDN's authorization token (oh) and its expiry (oe). whatsmeow builds the
// download URL by concatenating "&hash=..." onto whatever this returns
// (DownloadMediaWithPath), so a path stripped of its query produces a URL with
// no "?" and no token, and the CDN answers 403 to every media in the store.
// Keeping the query mirrors the directPath the protobuf itself carries.
func extractDirectPathFromURL(url string) string {
	// Example URL: https://mmg.whatsapp.net/v/t62.7118-24/13812002_69805803_n.enc?ccb=11-4&oh=...&oe=...&_nc_sid=...
	// Example return: /v/t62.7118-24/13812002_69805803_n.enc?ccb=11-4&oh=...&oe=...&_nc_sid=...

	// Find the path part after the domain
	parts := strings.SplitN(url, ".net/", 2)
	if len(parts) < 2 {
		return url // Return original URL if parsing fails
	}

	// Create proper direct path format
	return "/" + parts[1]
}

// ---------------------------------------------------------------------------
// Read-only REST endpoints (mirrors of whatsapp-mcp-server/whatsapp.py SQLite
// reads) so a remote MCP server can consume message/chat/contact history over
// HTTP instead of opening the SQLite files directly.
// ---------------------------------------------------------------------------

// stripAccents lowercases a string and strips Unicode diacritics (NFD
// decomposition, drop Mn category), matching Python's _strip_accents exactly
// so LIKE-based search behaves the same regardless of accents/case.
func stripAccents(s string) string {
	normalizado, _, _ := textoNormalizado(s)
	return normalizado
}

// nomeNormalizado e a regua de nome inteira: sem espaco nas pontas, sem acento,
// sem caixa, e com todo separador reduzido a um espaco. E a UNICA regua — quem
// casa nome, aqui ou na varredura do texto, chama esta funcao.
func nomeNormalizado(s string) string {
	return stripAccents(strings.TrimSpace(s))
}

// ehSeparadorDeNome diz se o rune separa duas partes de um nome em vez de fazer
// parte dele. Todo espaco entra (inclusive o inquebravel U+00A0 e o fino
// U+202F, que saem de teclado de celular e de colagem), e tambem o hifen e o
// sublinhado.
//
// A classe e generosa DE PROPOSITO, e a direcao importa: o candidato longo que
// protege o prefixo so protege se casar. Nao casar significa substituir o nome
// curto e ENVIAR com a pessoa errada grifada; casar de mais significa, no pior
// caso, deixar o texto intacto e pagar uma recusa. Falha segura de um lado so
// (achado 1 da rodada 9: "@Ana  Paula" com espaco duplo, NBSP, quebra de linha
// ou hifen enviava a Ana grifada onde o autor nomeou a Ana Paula).
//
// O ponto final fica de fora: ele tambem encerra frase, e "@Ana. Paula vem?"
// viraria recusa num texto em que o autor quis mesmo a Ana.
func ehSeparadorDeNome(r rune) bool {
	if unicode.IsSpace(r) {
		return true
	}
	switch r {
	case '-', '\u2010', '\u2011', '\u2013', '\u2014', '_':
		return true
	}
	return false
}

// APIMessage is the wire shape for a message row (Message is already taken by
// the whatsmeow event struct above).
type APIMessage struct {
	Timestamp       time.Time `json:"timestamp"`
	Sender          string    `json:"sender"`
	ChatName        *string   `json:"chat_name"`
	Content         string    `json:"content"`
	IsFromMe        bool      `json:"is_from_me"`
	ChatJID         string    `json:"chat_jid"`
	ID              string    `json:"id"`
	MediaType       *string   `json:"media_type"`
	QuotedMessageID *string   `json:"quoted_message_id"`
	QuotedSender    *string   `json:"quoted_sender"`
	QuotedContent   *string   `json:"quoted_content"`
	Mentions        []string  `json:"mentions,omitempty"`
	// Issue #21: Revoked means the sender deleted it for everyone — Content is
	// then revokedPlaceholder and there is no media to download. Edited means
	// Content is the latest edit, not the original text.
	Revoked bool `json:"revoked,omitempty"`
	Edited  bool `json:"edited,omitempty"`
}

// revokedPlaceholder is what the read endpoints show in place of the content
// of a message the sender deleted for everyone.
const revokedPlaceholder = "[mensagem apagada]"

// applyMessageFlags sets Revoked/Edited on a scanned row and, for a revoked
// one, swaps in the placeholder and drops the media type — the one place the
// read endpoints decide how a deleted message looks.
func (m *APIMessage) applyMessageFlags(revoked, edited bool) {
	m.Revoked = revoked
	m.Edited = edited && !revoked
	if revoked {
		m.Content = revokedPlaceholder
		m.MediaType = nil
		m.QuotedMessageID, m.QuotedSender, m.QuotedContent, m.Mentions = nil, nil, nil, nil
	}
}

// lastMessageCaseSQL is the CASE expression for the last_message column of
// listChats, getContactChats, getChat and getDirectChatByContact (D2, soft
// delete): those four build their own SELECT by hand — unlike the
// message-listing endpoints, which go through scanAPIMessageRow/
// applyMessageFlags — so each needs its own guard against showing a revoked
// row's real content. col is the SQL alias/table name the messages row is
// selected under (e.g. "messages" or "m").
func lastMessageCaseSQL(col string) string {
	return fmt.Sprintf("CASE WHEN %s.revoked_at IS NOT NULL THEN '%s' ELSE %s.content END", col, revokedPlaceholder, col)
}

// APIChat is the wire shape for a chat row.
type APIChat struct {
	JID             string  `json:"jid"`
	Name            *string `json:"name"`
	LastMessageTime *string `json:"last_message_time"`
	LastMessage     *string `json:"last_message"`
	LastSender      *string `json:"last_sender"`
	LastIsFromMe    *bool   `json:"last_is_from_me"`
}

// APIContact is the wire shape for a contact search result.
type APIContact struct {
	PhoneNumber string  `json:"phone_number"`
	Name        *string `json:"name"`
	JID         string  `json:"jid"`
}

func writeJSONError(w http.ResponseWriter, status int, msg string) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	json.NewEncoder(w).Encode(map[string]string{"error": msg})
}

func writeJSON(w http.ResponseWriter, v interface{}) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(v)
}

// resolvePhoneToJIDs mirrors _resolve_phone_to_jids: returns every JID form
// (regular + LID) that could refer to this phone number. Degrades to just the
// plain-JID guess if whatsapp.db can't be opened or queried, mirroring
// Python's `except Exception: pass`.
// resolvePhoneToJIDs looks up LID/PN variants for a phone number in
// whatsapp.db. The base "@s.whatsapp.net" JID is always included even if the
// lookup fails — a missing/locked store degrades the *quality* of the match
// (misses LID-only contacts) but callers can still search on the base JID.
// Failures are logged (not returned as an error) because this is best-effort
// enrichment used inline by several read endpoints, not something that
// should fail the whole request.
func resolvePhoneToJIDs(phone string) []string {
	phone = normalizePhone(phone)
	jids := []string{phone + "@s.whatsapp.net"}

	db, err := openStoreDBReadOnly()
	if err != nil {
		fmt.Printf("resolvePhoneToJIDs: whatsapp.db unavailable (%v), falling back to base JID only for %s\n", err, phone)
		return jids
	}
	defer db.Close()

	var lid, pn string
	row := db.QueryRow("SELECT lid, pn FROM whatsmeow_lid_map WHERE pn = ?", phone)
	err = row.Scan(&lid, &pn)
	if err != nil && err != sql.ErrNoRows && len(phone) > 10 {
		fmt.Printf("resolvePhoneToJIDs: exact lid_map lookup failed for %s: %v\n", phone, err)
	}
	if err != nil && len(phone) > 10 {
		suffix := phone[len(phone)-10:]
		row = db.QueryRow("SELECT lid, pn FROM whatsmeow_lid_map WHERE pn LIKE ?", "%"+suffix)
		err = row.Scan(&lid, &pn)
		if err != nil && err != sql.ErrNoRows {
			fmt.Printf("resolvePhoneToJIDs: suffix lid_map lookup failed for %s: %v\n", phone, err)
		}
	}
	if err == nil {
		jids = append(jids, lid+"@lid")
		if pn != phone {
			jids = append(jids, pn+"@s.whatsapp.net")
		}
	}
	return jids
}

// getContactNameFromStore mirrors _get_contact_name: look up a contact's
// display name in whatsapp.db by phone number. Empty string means "not
// found" (a normal, expected outcome) or "lookup failed" (logged below) —
// callers already treat both the same way (fall back to no enrichment).
func getContactNameFromStore(phone string) string {
	phone = normalizePhone(phone)
	db, err := openStoreDBReadOnly()
	if err != nil {
		fmt.Printf("getContactNameFromStore: whatsapp.db unavailable (%v) for %s\n", err, phone)
		return ""
	}
	defer db.Close()

	var fullName, pushName sql.NullString
	err = db.QueryRow(
		`SELECT full_name, push_name FROM whatsmeow_contacts WHERE their_jid = ? OR their_jid LIKE ?`,
		phone+"@s.whatsapp.net", phone+"%",
	).Scan(&fullName, &pushName)
	if err != nil {
		if err != sql.ErrNoRows {
			fmt.Printf("getContactNameFromStore: query failed for %s: %v\n", phone, err)
		}
		return ""
	}
	if fullName.Valid && fullName.String != "" {
		return fullName.String
	}
	if pushName.Valid && pushName.String != "" {
		return pushName.String
	}
	return ""
}

// nullTimeToPtr renders a sql.NullTime as an RFC3339 string pointer, or nil.
// storedTimeToPtr renders a timestamp read back as text (see getDeletedMessage)
// as RFC3339, like nullTimeToPtr does for a scanned time. The layouts are the
// ones the SQLite drivers write for a time.Time parameter; a value in none of
// them is returned as stored rather than dropped.
func storedTimeToPtr(v sql.NullString) *string {
	if !v.Valid {
		return nil
	}
	// A time.Now() written before the Round(0) in handleRevoke/handleEdit
	// carries Go's monotonic reading in its String() form (" m=+58.98...").
	raw := v.String
	if i := strings.Index(raw, " m="); i >= 0 {
		raw = raw[:i]
	}
	// The first layout is time.Time.String(), which the Windows driver
	// (modernc) writes into a TEXT column — the real store holds e.g.
	// "2026-09-24 15:32:41 -0300 -03".
	for _, layout := range []string{"2006-01-02 15:04:05.999999999 -0700 MST", "2006-01-02 15:04:05.999999999-07:00", time.RFC3339Nano, "2006-01-02 15:04:05"} {
		if t, err := time.Parse(layout, raw); err == nil {
			s := t.Format(time.RFC3339)
			return &s
		}
	}
	s := v.String
	return &s
}

func nullTimeToPtr(t sql.NullTime) *string {
	if !t.Valid {
		return nil
	}
	// Keep the original offset (matches messages.timestamp's own tz, and how
	// time.Time.MarshalJSON renders APIMessage.Timestamp) instead of forcing
	// UTC — consistent RFC3339 with offset, not a mix of offset and "Z".
	s := t.Time.Format(time.RFC3339)
	return &s
}

func nullStringToPtr(s sql.NullString) *string {
	if !s.Valid {
		return nil
	}
	v := s.String
	return &v
}

func nullBoolToPtr(b sql.NullBool) *bool {
	if !b.Valid {
		return nil
	}
	v := b.Bool
	return &v
}

// scanAPIChatRow scans one row shaped like the list_chats/get_chat/etc.
// queries below: jid, name, last_message_time, last_message, last_sender, last_is_from_me.
func scanAPIChatRow(rows interface {
	Scan(dest ...interface{}) error
}) (APIChat, error) {
	var jid string
	var name, lastMessage, lastSender sql.NullString
	var lastMessageTime sql.NullTime
	var lastIsFromMe sql.NullBool
	err := rows.Scan(&jid, &name, &lastMessageTime, &lastMessage, &lastSender, &lastIsFromMe)
	if err != nil {
		return APIChat{}, err
	}
	return APIChat{
		JID:             jid,
		Name:            nullStringToPtr(name),
		LastMessageTime: nullTimeToPtr(lastMessageTime),
		LastMessage:     nullStringToPtr(lastMessage),
		LastSender:      nullStringToPtr(lastSender),
		LastIsFromMe:    nullBoolToPtr(lastIsFromMe),
	}, nil
}

// scanAPIMessageRow scans one row shaped like: timestamp, sender, chat_name,
// content, is_from_me, chat_jid, id, media_type, quoted_message_id,
// quoted_sender, quoted_content, mentions.
func scanAPIMessageRow(rows interface {
	Scan(dest ...interface{}) error
}) (APIMessage, error) {
	var timestamp time.Time
	var sender, content, chatJID, id string
	var chatName, mediaType, quotedMessageID, quotedSender, quotedContent, mentions sql.NullString
	var isFromMe, revoked, edited bool
	err := rows.Scan(&timestamp, &sender, &chatName, &content, &isFromMe, &chatJID, &id, &mediaType, &quotedMessageID, &quotedSender, &quotedContent, &mentions, &revoked, &edited)
	if err != nil {
		return APIMessage{}, err
	}
	msg := APIMessage{
		Timestamp:       timestamp,
		Sender:          sender,
		ChatName:        nullStringToPtr(chatName),
		Content:         content,
		IsFromMe:        isFromMe,
		ChatJID:         chatJID,
		ID:              id,
		MediaType:       nullStringToPtr(mediaType),
		QuotedMessageID: nullStringToPtr(quotedMessageID),
		QuotedSender:    nullStringToPtr(quotedSender),
		QuotedContent:   nullStringToPtr(quotedContent),
		Mentions:        decodeMentionsColumn(mentions),
	}
	msg.applyMessageFlags(revoked, edited)
	return msg, nil
}

// decodeMentionsColumn deserializes the mentions column (a JSON array of
// strings, or NULL/empty for no mentions) into a []string. Invalid JSON in
// the column is treated as no mentions rather than failing the query — a
// malformed row shouldn't take down a whole listMessages/getMessageContext
// call.
func decodeMentionsColumn(col sql.NullString) []string {
	if !col.Valid || col.String == "" {
		return nil
	}
	var mentions []string
	if err := json.Unmarshal([]byte(col.String), &mentions); err != nil {
		return nil
	}
	return mentions
}

// ---- /api/chats ----

type ChatsRequest struct {
	Query              *string `json:"query"`
	Limit              int     `json:"limit"`
	Page               int     `json:"page"`
	IncludeLastMessage *bool   `json:"include_last_message"`
	SortBy             string  `json:"sort_by"`
}

type ChatsResponse struct {
	Chats []APIChat `json:"chats"`
}

func listChats(db *sql.DB, req ChatsRequest) (ChatsResponse, error) {
	limit := req.Limit
	if limit <= 0 {
		limit = 20
	}
	includeLastMessage := true
	if req.IncludeLastMessage != nil {
		includeLastMessage = *req.IncludeLastMessage
	}

	selectClause := `
		SELECT
			chats.jid,
			chats.name,
			chats.last_message_time,
			NULL as last_message,
			NULL as last_sender,
			NULL as last_is_from_me
		FROM chats
	`
	if includeLastMessage {
		selectClause = fmt.Sprintf(`
			SELECT
				chats.jid,
				chats.name,
				chats.last_message_time,
				%s as last_message,
				messages.sender as last_sender,
				messages.is_from_me as last_is_from_me
			FROM chats
		`, lastMessageCaseSQL("messages"))
	}
	queryParts := []string{selectClause}
	if includeLastMessage {
		queryParts = append(queryParts, `
			LEFT JOIN messages ON chats.jid = messages.chat_jid
			AND chats.last_message_time = messages.timestamp
		`)
	}

	var whereClauses []string
	var params []interface{}
	if req.Query != nil && *req.Query != "" {
		whereClauses = append(whereClauses, "(unaccent(chats.name) LIKE unaccent(?) OR chats.jid LIKE ?)")
		params = append(params, "%"+*req.Query+"%", "%"+*req.Query+"%")
	}
	if len(whereClauses) > 0 {
		queryParts = append(queryParts, "WHERE "+strings.Join(whereClauses, " AND "))
	}

	orderBy := "chats.name"
	if req.SortBy != "name" {
		orderBy = "chats.last_message_time DESC"
	}
	queryParts = append(queryParts, "ORDER BY "+orderBy)

	offset := req.Page * limit
	queryParts = append(queryParts, "LIMIT ? OFFSET ?")
	params = append(params, limit, offset)

	rows, err := db.Query(strings.Join(queryParts, " "), params...)
	if err != nil {
		return ChatsResponse{}, err
	}
	defer rows.Close()

	chats := []APIChat{}
	for rows.Next() {
		chat, err := scanAPIChatRow(rows)
		if err != nil {
			return ChatsResponse{}, err
		}
		chats = append(chats, chat)
	}
	return ChatsResponse{Chats: chats}, rows.Err()
}

// ---- /api/messages ----

type MessagesRequest struct {
	After             *string `json:"after"`
	Before            *string `json:"before"`
	SenderPhoneNumber *string `json:"sender_phone_number"`
	ChatJID           *string `json:"chat_jid"`
	Query             *string `json:"query"`
	Limit             int     `json:"limit"`
	Page              int     `json:"page"`
}

type MessagesResponse struct {
	Messages []APIMessage `json:"messages"`
}

// errInvalidRequest marks errors that should surface as 400 (bad input) to
// callers, as opposed to unwrapped errors from db.Query/Scan which mean a
// genuine internal/DB failure and should surface as 500.
type errInvalidRequest struct{ msg string }

func (e *errInvalidRequest) Error() string { return e.msg }

// isoDateLayouts covers the subset of Python's datetime.fromisoformat that the
// old whatsapp.py callers could plausibly send: full offset-aware RFC3339,
// naive date+time, and date-only. Tried in order, first match wins.
var isoDateLayouts = []string{
	time.RFC3339,
	"2006-01-02T15:04:05",
	"2006-01-02 15:04:05",
	"2006-01-02",
}

// parseISODate mirrors Python's datetime.fromisoformat leniency: accepts an
// offset (kept as-is) or a naive timestamp/date. Naive input is interpreted
// as UTC, matching what whatsmeow actually writes to messages.timestamp
// (msg.Info.Timestamp is a protocol-level UTC value; there's no per-deploy
// local-time conversion anywhere in the write path). Deliberately NOT
// time.Local: that depends on the deploying machine/container's OS timezone
// config, which has no relationship to the timezone messages were stored in
// and would silently shift query windows by the offset on any host not
// configured to the same zone (e.g. any VPS left at the common UTC default).
func parseISODate(s string) (time.Time, error) {
	for _, layout := range isoDateLayouts {
		if layout == time.RFC3339 {
			if t, err := time.Parse(layout, s); err == nil {
				return t, nil
			}
			continue
		}
		if t, err := time.ParseInLocation(layout, s, time.UTC); err == nil {
			return t, nil
		}
	}
	return time.Time{}, &errInvalidRequest{msg: fmt.Sprintf("invalid date format: %s", s)}
}

func listMessages(db *sql.DB, req MessagesRequest) (MessagesResponse, error) {
	limit := req.Limit
	if limit <= 0 {
		limit = 20
	}

	queryParts := []string{
		`SELECT messages.timestamp, messages.sender, chats.name, messages.content, messages.is_from_me, chats.jid, messages.id, messages.media_type, messages.quoted_message_id, messages.quoted_sender, messages.quoted_content, messages.mentions, messages.revoked_at IS NOT NULL, messages.edited_at IS NOT NULL FROM messages`,
		`JOIN chats ON messages.chat_jid = chats.jid`,
	}
	var whereClauses []string
	var params []interface{}

	if req.After != nil && *req.After != "" {
		t, err := parseISODate(*req.After)
		if err != nil {
			return MessagesResponse{}, &errInvalidRequest{msg: fmt.Sprintf("invalid date format for 'after': %s", *req.After)}
		}
		whereClauses = append(whereClauses, "messages.timestamp > ?")
		params = append(params, t)
	}
	if req.Before != nil && *req.Before != "" {
		t, err := parseISODate(*req.Before)
		if err != nil {
			return MessagesResponse{}, &errInvalidRequest{msg: fmt.Sprintf("invalid date format for 'before': %s", *req.Before)}
		}
		whereClauses = append(whereClauses, "messages.timestamp < ?")
		params = append(params, t)
	}
	if req.SenderPhoneNumber != nil && *req.SenderPhoneNumber != "" {
		jids := resolvePhoneToJIDs(*req.SenderPhoneNumber)
		placeholders := make([]string, len(jids))
		for i, jid := range jids {
			placeholders[i] = "?"
			params = append(params, jid)
		}
		whereClauses = append(whereClauses, fmt.Sprintf(
			"(messages.chat_jid IN (%s) AND messages.chat_jid NOT LIKE '%%@g.us')",
			strings.Join(placeholders, ","),
		))
	}
	if req.ChatJID != nil && *req.ChatJID != "" {
		whereClauses = append(whereClauses, "messages.chat_jid = ?")
		params = append(params, *req.ChatJID)
	}
	if req.Query != nil && *req.Query != "" {
		whereClauses = append(whereClauses, "unaccent(messages.content) LIKE unaccent(?) AND messages.revoked_at IS NULL")
		params = append(params, "%"+*req.Query+"%")
	}
	if len(whereClauses) > 0 {
		queryParts = append(queryParts, "WHERE "+strings.Join(whereClauses, " AND "))
	}

	offset := req.Page * limit
	queryParts = append(queryParts, "ORDER BY messages.timestamp DESC", "LIMIT ? OFFSET ?")
	params = append(params, limit, offset)

	rows, err := db.Query(strings.Join(queryParts, " "), params...)
	if err != nil {
		return MessagesResponse{}, err
	}
	defer rows.Close()

	messages := []APIMessage{}
	for rows.Next() {
		msg, err := scanAPIMessageRow(rows)
		if err != nil {
			return MessagesResponse{}, err
		}
		messages = append(messages, msg)
	}
	return MessagesResponse{Messages: messages}, rows.Err()
}

// ---- /api/message_context ----

type MessageContextRequest struct {
	MessageID string `json:"message_id"`
	Before    int    `json:"before"`
	After     int    `json:"after"`
}

type MessageContextResponse struct {
	Message APIMessage   `json:"message"`
	Before  []APIMessage `json:"before"`
	After   []APIMessage `json:"after"`
}

func getMessageContext(db *sql.DB, req MessageContextRequest) (MessageContextResponse, bool, error) {
	before := req.Before
	if before <= 0 {
		before = 5
	}
	after := req.After
	if after <= 0 {
		after = 5
	}

	row := db.QueryRow(`
		SELECT messages.timestamp, messages.sender, chats.name, messages.content, messages.is_from_me, chats.jid, messages.id, messages.chat_jid, messages.media_type, messages.quoted_message_id, messages.quoted_sender, messages.quoted_content, messages.mentions, messages.revoked_at IS NOT NULL, messages.edited_at IS NOT NULL
		FROM messages
		JOIN chats ON messages.chat_jid = chats.jid
		WHERE messages.id = ?
	`, req.MessageID)

	var timestamp time.Time
	var sender, content, chatJID, id, targetChatJID string
	var chatName, mediaType, quotedMessageID, quotedSender, quotedContent, mentions sql.NullString
	var isFromMe, revoked, edited bool
	err := row.Scan(&timestamp, &sender, &chatName, &content, &isFromMe, &chatJID, &id, &targetChatJID, &mediaType, &quotedMessageID, &quotedSender, &quotedContent, &mentions, &revoked, &edited)
	if err == sql.ErrNoRows {
		return MessageContextResponse{}, false, nil
	}
	if err != nil {
		return MessageContextResponse{}, false, err
	}
	target := APIMessage{
		Timestamp:       timestamp,
		Sender:          sender,
		ChatName:        nullStringToPtr(chatName),
		Content:         content,
		IsFromMe:        isFromMe,
		ChatJID:         chatJID,
		ID:              id,
		MediaType:       nullStringToPtr(mediaType),
		QuotedMessageID: nullStringToPtr(quotedMessageID),
		QuotedSender:    nullStringToPtr(quotedSender),
		QuotedContent:   nullStringToPtr(quotedContent),
		Mentions:        decodeMentionsColumn(mentions),
	}
	target.applyMessageFlags(revoked, edited)

	beforeRows, err := db.Query(`
		SELECT messages.timestamp, messages.sender, chats.name, messages.content, messages.is_from_me, chats.jid, messages.id, messages.media_type, messages.quoted_message_id, messages.quoted_sender, messages.quoted_content, messages.mentions, messages.revoked_at IS NOT NULL, messages.edited_at IS NOT NULL
		FROM messages
		JOIN chats ON messages.chat_jid = chats.jid
		WHERE messages.chat_jid = ? AND messages.timestamp < ?
		ORDER BY messages.timestamp DESC
		LIMIT ?
	`, targetChatJID, timestamp, before)
	if err != nil {
		return MessageContextResponse{}, false, err
	}
	defer beforeRows.Close()
	beforeMessages := []APIMessage{}
	for beforeRows.Next() {
		msg, err := scanAPIMessageRow(beforeRows)
		if err != nil {
			return MessageContextResponse{}, false, err
		}
		beforeMessages = append(beforeMessages, msg)
	}
	if err := beforeRows.Err(); err != nil {
		return MessageContextResponse{}, false, err
	}

	afterRows, err := db.Query(`
		SELECT messages.timestamp, messages.sender, chats.name, messages.content, messages.is_from_me, chats.jid, messages.id, messages.media_type, messages.quoted_message_id, messages.quoted_sender, messages.quoted_content, messages.mentions, messages.revoked_at IS NOT NULL, messages.edited_at IS NOT NULL
		FROM messages
		JOIN chats ON messages.chat_jid = chats.jid
		WHERE messages.chat_jid = ? AND messages.timestamp > ?
		ORDER BY messages.timestamp ASC
		LIMIT ?
	`, targetChatJID, timestamp, after)
	if err != nil {
		return MessageContextResponse{}, false, err
	}
	defer afterRows.Close()
	afterMessages := []APIMessage{}
	for afterRows.Next() {
		msg, err := scanAPIMessageRow(afterRows)
		if err != nil {
			return MessageContextResponse{}, false, err
		}
		afterMessages = append(afterMessages, msg)
	}
	if err := afterRows.Err(); err != nil {
		return MessageContextResponse{}, false, err
	}

	return MessageContextResponse{Message: target, Before: beforeMessages, After: afterMessages}, true, nil
}

// ---- /api/contacts/search ----

type ContactsSearchRequest struct {
	Query string `json:"query"`
}

type ContactsSearchResponse struct {
	Contacts []APIContact `json:"contacts"`
}

// searchContactsFromStore queries whatsapp.db for real names + LID contacts.
// A missing/unopenable store (e.g. fresh pairing, whatsmeow hasn't written it
// yet) is expected and returns no results with no error; any failure that
// occurs once the DB is open (query, scan, iteration) is a real error and
// propagates so the caller doesn't silently return partial data as success.
func searchContactsFromStore(pattern string) ([]APIContact, error) {
	storeDB, err := openStoreDBReadOnly()
	if err != nil {
		return nil, nil
	}
	defer storeDB.Close()

	rows, err := storeDB.Query(`
		SELECT their_jid, full_name, push_name
		FROM whatsmeow_contacts
		WHERE (LOWER(full_name) LIKE LOWER(?)
		       OR LOWER(push_name) LIKE LOWER(?)
		       OR their_jid LIKE ?)
		  AND their_jid NOT LIKE '%@g.us'
		ORDER BY full_name, push_name
		LIMIT 50
	`, pattern, pattern, pattern)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	var result []APIContact
	for rows.Next() {
		var jid string
		var fullName, pushName sql.NullString
		if err := rows.Scan(&jid, &fullName, &pushName); err != nil {
			return nil, err
		}
		name := fullName.String
		if name == "" {
			name = pushName.String
		}
		raw := strings.SplitN(jid, "@", 2)[0]
		phone := raw
		if strings.HasSuffix(jid, "@lid") {
			var pn string
			if err := storeDB.QueryRow("SELECT pn FROM whatsmeow_lid_map WHERE lid = ?", raw).Scan(&pn); err == nil {
				phone = pn
			}
		}
		var namePtr *string
		if name != "" {
			namePtr = &name
		}
		result = append(result, APIContact{PhoneNumber: phone, Name: namePtr, JID: jid})
	}
	return result, rows.Err()
}

func searchContacts(messagesDB *sql.DB, query string) (ContactsSearchResponse, error) {
	pattern := "%" + query + "%"
	result := []APIContact{}
	seen := map[string]bool{}

	storeContacts, err := searchContactsFromStore(pattern)
	if err != nil {
		return ContactsSearchResponse{}, err
	}
	for _, c := range storeContacts {
		if !seen[c.JID] {
			seen[c.JID] = true
			result = append(result, c)
		}
	}

	// Fallback: messages.db chats (catches contacts not in whatsmeow's own store).
	rows, err := messagesDB.Query(`
		SELECT DISTINCT jid, name FROM chats
		WHERE (LOWER(name) LIKE LOWER(?) OR LOWER(jid) LIKE LOWER(?))
		  AND jid NOT LIKE '%@g.us'
		ORDER BY name, jid LIMIT 50
	`, pattern, pattern)
	if err != nil {
		return ContactsSearchResponse{}, err
	}
	defer rows.Close()
	for rows.Next() {
		var jid string
		var name sql.NullString
		if err := rows.Scan(&jid, &name); err != nil {
			return ContactsSearchResponse{}, err
		}
		if !seen[jid] {
			seen[jid] = true
			result = append(result, APIContact{
				PhoneNumber: strings.SplitN(jid, "@", 2)[0],
				Name:        nullStringToPtr(name),
				JID:         jid,
			})
		}
	}

	return ContactsSearchResponse{Contacts: result}, rows.Err()
}

// ---- /api/contacts/chats ----

type ContactChatsRequest struct {
	JID   string `json:"jid"`
	Limit int    `json:"limit"`
	Page  int    `json:"page"`
}

func getContactChats(db *sql.DB, req ContactChatsRequest) (ChatsResponse, error) {
	limit := req.Limit
	if limit <= 0 {
		limit = 20
	}
	rows, err := db.Query(fmt.Sprintf(`
		SELECT DISTINCT
			c.jid,
			c.name,
			c.last_message_time,
			%s as last_message,
			m.sender as last_sender,
			m.is_from_me as last_is_from_me
		FROM chats c
		JOIN messages m ON c.jid = m.chat_jid
		WHERE m.sender = ? OR c.jid = ?
		ORDER BY c.last_message_time DESC
		LIMIT ? OFFSET ?
	`, lastMessageCaseSQL("m")), req.JID, req.JID, limit, req.Page*limit)
	if err != nil {
		return ChatsResponse{}, err
	}
	defer rows.Close()

	chats := []APIChat{}
	for rows.Next() {
		chat, err := scanAPIChatRow(rows)
		if err != nil {
			return ChatsResponse{}, err
		}
		chats = append(chats, chat)
	}
	return ChatsResponse{Chats: chats}, rows.Err()
}

// ---- /api/contacts/last_interaction ----

type LastInteractionRequest struct {
	JID string `json:"jid"`
}

type LastInteractionResponse struct {
	Message *APIMessage `json:"message"`
}

func getLastInteraction(db *sql.DB, jid string) (LastInteractionResponse, error) {
	row := db.QueryRow(`
		SELECT
			m.timestamp, m.sender, c.name, m.content, m.is_from_me, c.jid, m.id, m.media_type, m.quoted_message_id, m.quoted_sender, m.quoted_content, m.mentions, m.revoked_at IS NOT NULL, m.edited_at IS NOT NULL
		FROM messages m
		JOIN chats c ON m.chat_jid = c.jid
		WHERE m.sender = ? OR c.jid = ?
		ORDER BY m.timestamp DESC
		LIMIT 1
	`, jid, jid)

	msg, err := scanAPIMessageRow(row)
	if err == sql.ErrNoRows {
		return LastInteractionResponse{Message: nil}, nil
	}
	if err != nil {
		return LastInteractionResponse{}, err
	}
	return LastInteractionResponse{Message: &msg}, nil
}

// ---- /api/chat ----

type ChatRequest struct {
	ChatJID            string `json:"chat_jid"`
	IncludeLastMessage *bool  `json:"include_last_message"`
}

type ChatResponse struct {
	Chat *APIChat `json:"chat"`
}

func getChat(db *sql.DB, req ChatRequest) (ChatResponse, error) {
	includeLastMessage := true
	if req.IncludeLastMessage != nil {
		includeLastMessage = *req.IncludeLastMessage
	}

	query := `
		SELECT
			c.jid,
			c.name,
			c.last_message_time,
			NULL as last_message,
			NULL as last_sender,
			NULL as last_is_from_me
		FROM chats c
	`
	if includeLastMessage {
		query = fmt.Sprintf(`
			SELECT
				c.jid,
				c.name,
				c.last_message_time,
				%s as last_message,
				m.sender as last_sender,
				m.is_from_me as last_is_from_me
			FROM chats c
		`, lastMessageCaseSQL("m"))
		query += `
			LEFT JOIN messages m ON c.jid = m.chat_jid
			AND c.last_message_time = m.timestamp
		`
	}
	query += " WHERE c.jid = ?"

	row := db.QueryRow(query, req.ChatJID)
	chat, err := scanAPIChatRow(row)
	if err == sql.ErrNoRows {
		return ChatResponse{Chat: nil}, nil
	}
	if err != nil {
		return ChatResponse{}, err
	}
	return ChatResponse{Chat: &chat}, nil
}

// ---- /api/chat/by_contact ----

type ChatByContactRequest struct {
	SenderPhoneNumber string `json:"sender_phone_number"`
}

func getDirectChatByContact(db *sql.DB, req ChatByContactRequest) (ChatResponse, error) {
	jids := resolvePhoneToJIDs(req.SenderPhoneNumber)
	placeholders := make([]string, len(jids))
	params := make([]interface{}, len(jids))
	for i, jid := range jids {
		placeholders[i] = "?"
		params[i] = jid
	}

	query := fmt.Sprintf(`
		SELECT c.jid, c.name, c.last_message_time,
		       %s, m.sender, m.is_from_me
		FROM chats c
		LEFT JOIN messages m ON c.jid = m.chat_jid
			AND c.last_message_time = m.timestamp
		WHERE c.jid IN (%s) AND c.jid NOT LIKE '%%@g.us'
		LIMIT 1
	`, lastMessageCaseSQL("m"), strings.Join(placeholders, ","))

	row := db.QueryRow(query, params...)
	chat, err := scanAPIChatRow(row)
	if err == sql.ErrNoRows {
		return ChatResponse{Chat: nil}, nil
	}
	if err != nil {
		return ChatResponse{}, err
	}

	// Mirror Python: if the resolved name is empty or all-digits (after
	// stripping "@lid"), fall back to the contact name from whatsapp.db.
	nameEmpty := chat.Name == nil || *chat.Name == ""
	nameAllDigits := false
	if chat.Name != nil {
		stripped := strings.ReplaceAll(*chat.Name, "@lid", "")
		nameAllDigits = stripped != "" && isAllDigits(stripped)
	}
	if nameEmpty || nameAllDigits {
		if contactName := getContactNameFromStore(req.SenderPhoneNumber); contactName != "" {
			chat.Name = &contactName
		}
	}

	return ChatResponse{Chat: &chat}, nil
}

func isAllDigits(s string) bool {
	for _, r := range s {
		if r < '0' || r > '9' {
			return false
		}
	}
	return true
}

// ---- /api/deleted_message ----

// DeletedMessageRequest is the body of POST /api/deleted_message (D3): the
// one explicit path to what a sender deleted, or what a message said before
// it was edited. Download, when true, also fetches the message's media
// through the allowRevoked exception in downloadMedia (task 3).
type DeletedMessageRequest struct {
	MessageID string `json:"message_id"`
	ChatJID   string `json:"chat_jid"`
	Download  bool   `json:"download"`
}

// DeletedMessageResponse carries what get_deleted_message needs to show: the
// content as stored (the original caption/text for a revoked row, or the
// latest edit for one that's only edited), the text before the first edit
// (nil unless the message was ever edited), the media type, and when it was
// revoked/edited.
type DeletedMessageResponse struct {
	Content         string  `json:"content"`
	PreviousContent *string `json:"previous_content"`
	MediaType       *string `json:"media_type"`
	RevokedAt       *string `json:"revoked_at"`
	EditedAt        *string `json:"edited_at"`
	Downloaded      bool    `json:"downloaded,omitempty"`
	Filename        string  `json:"filename,omitempty"`
	Path            string  `json:"path,omitempty"`
	DownloadError   string  `json:"download_error,omitempty"`
}

// getDeletedMessage answers D3, kept separate from the HTTP handler so it's
// directly testable. A message that was never revoked nor edited is refused
// (found=false, no error) — asking to see the withdrawn content has to be an
// explicit act, not something a normal read stumbles into.
func getDeletedMessage(db *sql.DB, req DeletedMessageRequest) (DeletedMessageResponse, bool, error) {
	var content string
	var previousContent, mediaType sql.NullString
	// CAST AS TEXT: on a database that predates these columns,
	// ensureMessagesSchema added them as TEXT, and the driver then hands back a
	// string that a sql.NullTime cannot scan (seen on the real store: "unsupported
	// Scan, storing driver.Value type string into type *time.Time"). A fresh
	// database declares them TIMESTAMP; reading both as text covers either.
	var revokedAt, editedAt sql.NullString
	err := db.QueryRow(
		"SELECT content, previous_content, media_type, CAST(revoked_at AS TEXT), CAST(edited_at AS TEXT) FROM messages WHERE id = ? AND chat_jid = ?",
		req.MessageID, req.ChatJID,
	).Scan(&content, &previousContent, &mediaType, &revokedAt, &editedAt)
	if err == sql.ErrNoRows {
		return DeletedMessageResponse{}, false, nil
	}
	if err != nil {
		return DeletedMessageResponse{}, false, err
	}
	if !revokedAt.Valid && !editedAt.Valid {
		return DeletedMessageResponse{}, false, nil
	}
	return DeletedMessageResponse{
		Content:         content,
		PreviousContent: nullStringToPtr(previousContent),
		MediaType:       nullStringToPtr(mediaType),
		RevokedAt:       storedTimeToPtr(revokedAt),
		EditedAt:        storedTimeToPtr(editedAt),
	}, true, nil
}

// handleDeletedMessage returns the handler for POST /api/deleted_message
// (D3). Registered next to /api/revoke and /api/edit — unlike the
// list/search endpoints under readDB, it looks up a single row by id and
// needs no unaccent(), so it reads through messageStore.db directly and
// keeps working even if openUnaccentMessagesDB failed to open.
func handleDeletedMessage(client *whatsmeow.Client, messageStore *MessageStore) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
			return
		}
		var req DeletedMessageRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.MessageID == "" || req.ChatJID == "" {
			writeJSONError(w, http.StatusBadRequest, "message_id and chat_jid are required")
			return
		}
		if messageStore == nil {
			writeJSONError(w, http.StatusInternalServerError, "no message store available")
			return
		}
		resp, found, err := getDeletedMessage(messageStore.db, req)
		if err != nil {
			writeJSONError(w, http.StatusInternalServerError, err.Error())
			return
		}
		if !found {
			writeJSONError(w, http.StatusNotFound, fmt.Sprintf("message %s was neither deleted nor edited", req.MessageID))
			return
		}
		if req.Download {
			ok, _, filename, path, err := downloadMedia(client, messageStore, req.MessageID, req.ChatJID, true)
			if err != nil || !ok {
				// The content was already found: hand it back with the reason
				// the download failed, instead of losing it behind a 500 (a
				// deleted text message has no media to download).
				resp.DownloadError = "unknown error"
				if err != nil {
					resp.DownloadError = err.Error()
				}
				writeJSON(w, resp)
				return
			}
			resp.Downloaded = true
			resp.Filename = filename
			resp.Path = path
		}
		writeJSON(w, resp)
	}
}

// ---- /api/sender_name ----

type SenderNameRequest struct {
	SenderJID string `json:"sender_jid"`
}

type SenderNameResponse struct {
	Name string `json:"name"`
}

func getSenderName(db *sql.DB, senderJID string, lids mapaDeLID) (SenderNameResponse, error) {
	var name sql.NullString
	err := db.QueryRow("SELECT name FROM chats WHERE jid = ? LIMIT 1", senderJID).Scan(&name)
	if err != nil && err != sql.ErrNoRows {
		return SenderNameResponse{}, err
	}
	// `chats.name` com cara de telefone NAO e nome, e nao pode vencer a tabela
	// `senders`, que e onde o nome de verdade esta. Era o que acontecia: uma
	// conversa 1:1 sem nome salvo guarda o proprio numero em `chats.name`,
	// essa primeira consulta acertava, e a busca terminava ali — a leitura
	// respondia "(contato sem nome)" para quem tinha nome gravado uma tabela ao
	// lado (verificacao do criterio 7, medido em 2026-09-12 contra as pontes
	// reais). A regua e a mesma da D3, a mesma que rotuloDoParticipante usa.
	if err == nil && nomeUsavel(name.String) {
		return SenderNameResponse{Name: name.String}, nil
	}

	// A tabela `senders` e onde moram os nomes de PARTICIPANTE, e esta busca
	// nunca a consultava: so `chats`, que tem o nome de uma CONVERSA. Em grupo
	// isso significava que a leitura respondia "(contato sem nome)" para a
	// mesma pessoa que /api/group_info acabara de resolver pelo nome — as duas
	// superficies liam tabelas diferentes. Achado da verificacao do criterio 7,
	// medido em 2026-09-12 contra as duas pontes reais.
	//
	// As chaves sao varias porque `messages.sender` e gravado como a parte de
	// usuario do JID, sem servidor, e a linha de `senders` pode estar sob a
	// forma PN ou sob a @lid — a mesma razao do `outrasChaves` da resolucao de
	// mencao (rodadas 9 e 10).
	if nome := nomeEmSenders(db, senderJID, lids); nome != "" {
		return SenderNameResponse{Name: nome}, nil
	}

	phonePart := senderJID
	if idx := strings.Index(senderJID, "@"); idx >= 0 {
		phonePart = senderJID[:idx]
	}
	err = db.QueryRow("SELECT name FROM chats WHERE jid LIKE ? LIMIT 1", "%"+phonePart+"%").Scan(&name)
	if err != nil && err != sql.ErrNoRows {
		return SenderNameResponse{}, err
	}
	if err == nil && nomeUsavel(name.String) {
		return SenderNameResponse{Name: name.String}, nil
	}

	return SenderNameResponse{Name: senderJID}, nil
}

// nomeUsavel e a regua da D3 num lugar so: nome e o que NAO tem cara de
// telefone. Vazio, ou oito digitos ou mais, nao serve — e devolver o proprio
// identificador e como quem le sabe que nao houve nome.
func nomeUsavel(n string) bool {
	return n != "" && len(digitosDe(n)) < 8
}

// nomeEmSenders devolve o nome mais especifico que a tabela `senders` conhece
// para este remetente, pela mesma regua da D3: campo com cara de telefone nao e
// nome, e nesse caso devolve-se vazio para quem chama cair no marcador neutro.
func nomeEmSenders(db *sql.DB, senderJID string, lids mapaDeLID) string {
	semDisp := semDispositivo(senderJID)
	chaves := []string{senderJID, semDisp}
	if strings.Contains(semDisp, "@") {
		// Endereco completo: a OUTRA forma vem do mapa da propria lib, que e
		// autoritativo. Trocar o servidor na mao seria heuristica, e uma
		// heuristica errada aqui atribui o nome de uma pessoa a outra.
		if jid, err := types.ParseJID(semDisp); err == nil {
			chaves = append(chaves, outrasFormasDoJID(lids, jid)...)
		}
	} else {
		// Parte de usuario crua, que e como `messages.sender` e gravado. E
		// ambigua por natureza: pode ser um telefone ou o user part de um
		// @lid. As duas formas entram, mas se AS DUAS tiverem linha em
		// `senders` sao dois JIDs distintos com o mesmo user part — escolher
		// ali seria atribuir o nome de uma pessoa a outra, entao nao se
		// escolhe: devolve-se vazio e quem le cai no marcador neutro.
		u := strings.SplitN(semDisp, ":", 2)[0]
		pn := types.JID{User: u, Server: types.DefaultUserServer}
		lid := types.JID{User: u, Server: types.HiddenUserServer}
		if linhasEmSenders(db, pn.String(), lid.String()) > 1 {
			return ""
		}
		chaves = append(chaves, pn.String(), lid.String())
		chaves = append(chaves, outrasFormasDoJID(lids, pn)...)
	}
	var p mentionParticipant
	vistas := make(map[string]bool, len(chaves))
	for _, chave := range chaves {
		if chave == "" || vistas[chave] {
			continue
		}
		vistas[chave] = true
		var pushName, fullName, firstName, businessName sql.NullString
		err := db.QueryRow(
			"SELECT push_name, full_name, first_name, business_name FROM senders WHERE jid = ?", chave,
		).Scan(&pushName, &fullName, &firstName, &businessName)
		if err != nil {
			continue
		}
		for _, campo := range []struct {
			destino *string
			veio    sql.NullString
		}{
			{&p.pushName, pushName}, {&p.fullName, fullName},
			{&p.firstName, firstName}, {&p.businessName, businessName},
		} {
			if *campo.destino == "" {
				*campo.destino = campo.veio.String
			}
		}
	}
	return rotuloDoParticipante(p, "")
}

// linhasEmSenders conta quantos destes JIDs tem linha em `senders`. Serve a uma
// pergunta so: "este user part pertence a mais de uma pessoa?".
func linhasEmSenders(db *sql.DB, jids ...string) int {
	n := 0
	for _, jid := range jids {
		var existe int
		if err := db.QueryRow("SELECT 1 FROM senders WHERE jid = ? LIMIT 1", jid).Scan(&existe); err == nil {
			n++
		}
	}
	return n
}

// Start a REST API server to expose the WhatsApp client functionality
// renderQRPage returns the HTML for the QR code pairing page. Every page the
// bridge serves on /qr identifies its account through accountHeading, so two
// bridges never render the same page.
// Extracted for testability (similar to handleStatus).
// accountHeading returns the line that tells the person WHICH bridge this page
// belongs to. It is deliberately never empty: a multi-account setup serves one of
// these pages per account and they are otherwise byte-identical, so the person
// holding a phone cannot tell which account the QR pairs. With no alias set, the
// port still separates one bridge from another.
//
// This revises D8/D1 ("without WHATSAPP_ACCOUNT the page is unchanged"). Leaving the
// default account page untouched is precisely what made the pages indistinguishable.
// The alias is escaped because it arrives from the environment.
func accountHeading(accountAlias string, port int) string {
	if accountAlias != "" {
		return fmt.Sprintf("<p>Account: %s (port %d)</p>\n", html.EscapeString(accountAlias), port)
	}
	return fmt.Sprintf("<p>Port %d</p>\n", port)
}

// accountTitle is the same identity for the <title>: with one tab open per account,
// the tab strip is where the person picks, before the page is even visible.
func accountTitle(accountAlias string, port int) string {
	if accountAlias != "" {
		return fmt.Sprintf("WhatsApp - %s", html.EscapeString(accountAlias))
	}
	return fmt.Sprintf("WhatsApp - port %d", port)
}

func renderQRPage(accountAlias string, port int) string {
	return fmt.Sprintf(`<!DOCTYPE html><html><head>
<meta http-equiv="refresh" content="20">
<title>%s</title>
<style>body{font-family:sans-serif;text-align:center;padding:2rem;background:#f0f0f0}
img{border:8px solid white;border-radius:8px;box-shadow:0 4px 20px rgba(0,0,0,.2)}</style>
</head><body>
<h2>Scan with WhatsApp to connect</h2>
%s<p>Open WhatsApp → Settings → Linked Devices → Link a Device</p>
<img src="/qr.png" width="300" height="300" alt="QR Code">
<p style="color:#888;font-size:.85rem">Page refreshes every 20 s</p>
</body></html>`, accountTitle(accountAlias, port), accountHeading(accountAlias, port))
}

// renderConnectedPage and renderWaitingPage carry the same identity as the QR page.
// They used to be anonymous literals, which meant the two states a person actually
// waits on -- "which one still needs pairing?" and "did THIS one connect?" -- were
// exactly the states that never said which account they were about.
func renderConnectedPage(accountAlias string, port int) string {
	return fmt.Sprintf(`<!DOCTYPE html><html><head><title>%s</title></head>
<body style="font-family:sans-serif;text-align:center;padding:4rem">
<h2 style="color:#25d366">&#10003; WhatsApp connected</h2>
%s<p>You can close this tab.</p></body></html>`,
		accountTitle(accountAlias, port), accountHeading(accountAlias, port))
}

func renderWaitingPage(accountAlias string, port int) string {
	return fmt.Sprintf(`<!DOCTYPE html><html><head><title>%s</title></head>
<body style="font-family:sans-serif;text-align:center;padding:4rem">
<h2>Waiting for QR code...</h2>
%s<p>This page refreshes automatically.</p></body></html>`,
		accountTitle(accountAlias, port), accountHeading(accountAlias, port))
}

func startRESTServer(client *whatsmeow.Client, messageStore *MessageStore, port int) {
	// /qr — serves the current QR code as PNG (during pairing) or a status page (when connected).
	// Open http://localhost:8080/qr in a browser to scan the QR code on first setup.
	// If WHATSAPP_ACCOUNT is set, includes the account name and port in the page (D8, D3).
	// Without WHATSAPP_ACCOUNT the page falls back to identifying the bridge by port,
	// so two accounts never serve identical pages (revises D1).
	http.HandleFunc("/qr", func(w http.ResponseWriter, r *http.Request) {
		qrState.RLock()
		png := qrState.png
		connected := qrState.connected
		qrState.RUnlock()

		accountAlias := os.Getenv("WHATSAPP_ACCOUNT")

		if connected {
			w.Header().Set("Content-Type", "text/html; charset=utf-8")
			fmt.Fprint(w, renderConnectedPage(accountAlias, port))
			return
		}
		if png == nil {
			w.Header().Set("Content-Type", "text/html; charset=utf-8")
			w.Header().Set("Refresh", "2")
			fmt.Fprint(w, renderWaitingPage(accountAlias, port))
			return
		}
		// Serve an auto-refreshing HTML page that embeds the QR as a data URI.
		// Refreshes every 20 s so a new QR is shown if the first one expires.
		w.Header().Set("Content-Type", "text/html; charset=utf-8")

		fmt.Fprint(w, renderQRPage(accountAlias, port))
	})

	// /qr.png — raw PNG for embedding or direct download
	http.HandleFunc("/qr.png", func(w http.ResponseWriter, r *http.Request) {
		qrState.RLock()
		png := qrState.png
		qrState.RUnlock()
		if png == nil {
			http.Error(w, "QR not available", http.StatusNotFound)
			return
		}
		w.Header().Set("Content-Type", "image/png")
		w.Header().Set("Cache-Control", "no-store")
		w.Write(png)
	})

	// GET /api/status — health-check endpoint (always HTTP 200 while bridge is up).
	// RN-01: always 200, never 503, even with client == nil.
	// Method != GET → 405.
	http.HandleFunc("/api/status", handleStatus(client))

	// Handler for sending messages
	http.HandleFunc("/api/send", func(w http.ResponseWriter, r *http.Request) {
		// Only allow POST requests
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		// Parse the request body
		var req SendMessageRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}

		// Validate request
		if req.Recipient == "" {
			http.Error(w, "Recipient is required", http.StatusBadRequest)
			return
		}

		if req.Message == "" && req.MediaPath == "" {
			http.Error(w, "Message or media path is required", http.StatusBadRequest)
			return
		}

		fmt.Println("Received request to send message", req.Message, req.MediaPath)

		// Send the message
		success, message, statusCode, candidates := sendWhatsAppMessage(client, messageStore, req.Recipient, req.Message, req.MediaPath, req.QuotedMessageID, req.Mentions)
		fmt.Println("Message sent", success, message)
		// Set response headers
		w.Header().Set("Content-Type", "application/json")

		// Set appropriate status code
		if !success {
			if statusCode == 0 {
				statusCode = http.StatusInternalServerError
			}
			w.WriteHeader(statusCode)
		}

		// Send response
		json.NewEncoder(w).Encode(SendMessageResponse{
			Success:    success,
			Message:    message,
			Candidates: candidates,
		})
	})

	// Handler for downloading media
	http.HandleFunc("/api/download", func(w http.ResponseWriter, r *http.Request) {
		// Only allow POST requests
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}

		// Parse the request body
		var req DownloadMediaRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}

		// Validate request
		if req.MessageID == "" || req.ChatJID == "" {
			http.Error(w, "Message ID and Chat JID are required", http.StatusBadRequest)
			return
		}

		// Download the media
		success, mediaType, filename, path, err := downloadMedia(client, messageStore, req.MessageID, req.ChatJID, false)

		// Set response headers
		w.Header().Set("Content-Type", "application/json")

		// Handle download result
		if !success || err != nil {
			errMsg := "Unknown error"
			if err != nil {
				errMsg = err.Error()
			}

			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(DownloadMediaResponse{
				Success: false,
				Message: fmt.Sprintf("Failed to download media: %s", errMsg),
			})
			return
		}

		// Send successful response
		json.NewEncoder(w).Encode(DownloadMediaResponse{
			Success:  true,
			Message:  fmt.Sprintf("Successfully downloaded %s media", mediaType),
			Filename: filename,
			Path:     path,
		})
	})

	// Handler for requesting media retry (re-upload of expired media from the phone)
	http.HandleFunc("/api/mediaretry", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req DownloadMediaRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}
		if req.MessageID == "" || req.ChatJID == "" {
			http.Error(w, "Message ID and Chat JID are required", http.StatusBadRequest)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		if err := requestMediaRetry(client, messageStore, req.MessageID, req.ChatJID); err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(map[string]interface{}{
				"success": false, "message": fmt.Sprintf("Failed to request media retry: %s", err.Error()),
			})
			return
		}
		json.NewEncoder(w).Encode(map[string]interface{}{
			"success": true, "message": "Media retry requested; watch bridge log for response",
		})
	})

	// Handler for creating a group
	http.HandleFunc("/api/create_group", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req CreateGroupRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}
		fmt.Printf("Received request to create group %q with %d participants\n", req.Name, len(req.Participants))
		resp := createWhatsAppGroup(client, messageStore, req)
		w.Header().Set("Content-Type", "application/json")
		if !resp.Success {
			w.WriteHeader(http.StatusInternalServerError)
		}
		json.NewEncoder(w).Encode(resp)
	})

	// Handler for getting group info (name + participants)
	http.HandleFunc("/api/group_info", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		jid, err := types.ParseJID(r.URL.Query().Get("jid"))
		if err != nil {
			http.Error(w, "Invalid JID", http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(map[string]interface{}{"success": false, "message": "WhatsApp client not connected"})
			return
		}
		groupInfo, err := client.GetGroupInfo(context.Background(), jid)
		w.Header().Set("Content-Type", "application/json")
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(map[string]interface{}{"success": false, "message": err.Error()})
			return
		}
		// D3 ate aqui: a resposta trazia jid, phone_number e lid de TODO
		// participante — num grupo de 40 pessoas, 40 telefones numa resposta de
		// API. O que quem le precisa e o NOME; o que quem ESCREVE precisa e de
		// um jeito de apontar a pessoa, e isso e o mesmo `ref` opaco que a
		// pergunta da D6 ja usa, aceito de volta por /api/group_participants.
		participants := participantesPorNome(messageStore, groupInfo, jid.String())
		json.NewEncoder(w).Encode(map[string]interface{}{
			// topic/is_locked/is_announce round out what /api/group_settings can
			// write. GetGroupInfoFromLink is not a substitute for reading them back:
			// the group node in an invite-query response carries no "locked" or
			// "announcement" child, so those flags always parse as false there
			// regardless of the group's real state.
			"success": true, "name": groupInfo.Name, "participants": participants,
			"topic": groupInfo.Topic, "is_locked": groupInfo.IsLocked,
			"is_announce": groupInfo.IsAnnounce,
			// you_are_admin: a bool, never a JID -- a caller that needs to know "did
			// our own account just get promoted here" (e.g. an onboarding flow gating
			// on it) can read this without the ref/name redaction above having to
			// leak anyone's number to get there.
			"you_are_admin": youAreAdminIn(client, groupInfo),
		})
	})

	// Handler for leaving a group
	http.HandleFunc("/api/leave_group", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req LeaveGroupRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, "Invalid request format", http.StatusBadRequest)
			return
		}
		fmt.Printf("Received request to leave group %s\n", req.JID)
		resp := leaveWhatsAppGroup(client, req.JID)
		w.Header().Set("Content-Type", "application/json")
		if !resp.Success {
			w.WriteHeader(http.StatusInternalServerError)
		}
		json.NewEncoder(w).Encode(resp)
	})

	// Handler for marking a chat as read
	http.HandleFunc("/api/mark_chat_read", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req MarkChatReadRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" {
			http.Error(w, "Invalid request: chat_jid is required", http.StatusBadRequest)
			return
		}
		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid chat_jid: %v", err), http.StatusBadRequest)
			return
		}
		var senderJID types.JID
		if req.SenderJID != "" {
			senderJID, err = types.ParseJID(req.SenderJID)
			if err != nil {
				http.Error(w, fmt.Sprintf("Invalid sender_jid: %v", err), http.StatusBadRequest)
				return
			}
		}
		ts := time.Now()
		if req.Timestamp > 0 {
			ts = time.Unix(req.Timestamp, 0)
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		ctx := context.Background()
		// Send read receipts to the sender(s)
		if len(req.MessageIDs) > 0 {
			if err := client.MarkRead(ctx, req.MessageIDs, ts, chatJID, senderJID); err != nil {
				w.Header().Set("Content-Type", "application/json")
				w.WriteHeader(http.StatusInternalServerError)
				json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("MarkRead error: %v", err)})
				return
			}
		}
		// Sync read state via app state so the unread badge clears on all devices
		if err := safeSendAppState(client, ctx, appstate.BuildMarkChatAsRead(chatJID, true, ts, nil)); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("AppState error: %v", err)})
			return
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(MarkChatResponse{Success: true, Message: fmt.Sprintf("Chat %s marked as read", req.ChatJID)})
	})

	// Handler for marking a chat as unread
	http.HandleFunc("/api/mark_chat_unread", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req MarkChatUnreadRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.ChatJID == "" {
			http.Error(w, "Invalid request: chat_jid required", http.StatusBadRequest)
			return
		}
		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid chat_jid: %v", err), http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		ctx := context.Background()
		if err := safeSendAppState(client, ctx, appstate.BuildMarkChatAsRead(chatJID, false, time.Time{}, nil)); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("AppState error: %v", err)})
			return
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(MarkChatResponse{Success: true, Message: fmt.Sprintf("Chat %s marked as unread", req.ChatJID)})
	})

	// Read-only endpoints below query messages.db through a second connection
	// (unaccent-enabled driver) rather than messageStore.db, so search filters
	// (list_chats/list_messages/search_contacts) can use the unaccent() SQL
	// function without touching the existing write path's driver.
	readDB, err := openUnaccentMessagesDB()
	if err != nil {
		fmt.Printf("Failed to open read-only messages.db handle: %v\n", err)
	} else {
		http.HandleFunc("/api/chats", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req ChatsRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			resp, err := listChats(readDB, req)
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/messages", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req MessagesRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			resp, err := listMessages(readDB, req)
			if err != nil {
				var invalid *errInvalidRequest
				if errors.As(err, &invalid) {
					writeJSONError(w, http.StatusBadRequest, err.Error())
				} else {
					writeJSONError(w, http.StatusInternalServerError, err.Error())
				}
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/message_context", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req MessageContextRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			if req.MessageID == "" {
				writeJSONError(w, http.StatusBadRequest, "message_id is required")
				return
			}
			resp, found, err := getMessageContext(readDB, req)
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			if !found {
				writeJSONError(w, http.StatusBadRequest, fmt.Sprintf("Message with ID %s not found", req.MessageID))
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/contacts/search", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req ContactsSearchRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			if req.Query == "" {
				writeJSONError(w, http.StatusBadRequest, "query is required")
				return
			}
			resp, err := searchContacts(readDB, req.Query)
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/contacts/chats", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req ContactChatsRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			if req.JID == "" {
				writeJSONError(w, http.StatusBadRequest, "jid is required")
				return
			}
			resp, err := getContactChats(readDB, req)
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/contacts/last_interaction", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req LastInteractionRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			if req.JID == "" {
				writeJSONError(w, http.StatusBadRequest, "jid is required")
				return
			}
			resp, err := getLastInteraction(readDB, req.JID)
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/chat", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req ChatRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			if req.ChatJID == "" {
				writeJSONError(w, http.StatusBadRequest, "chat_jid is required")
				return
			}
			resp, err := getChat(readDB, req)
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/chat/by_contact", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req ChatByContactRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			if req.SenderPhoneNumber == "" {
				writeJSONError(w, http.StatusBadRequest, "sender_phone_number is required")
				return
			}
			resp, err := getDirectChatByContact(readDB, req)
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			writeJSON(w, resp)
		})

		http.HandleFunc("/api/sender_name", func(w http.ResponseWriter, r *http.Request) {
			if r.Method != http.MethodPost {
				writeJSONError(w, http.StatusMethodNotAllowed, "Method not allowed")
				return
			}
			var req SenderNameRequest
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				writeJSONError(w, http.StatusBadRequest, "Invalid request format")
				return
			}
			if req.SenderJID == "" {
				writeJSONError(w, http.StatusBadRequest, "sender_jid is required")
				return
			}
			resp, err := getSenderName(readDB, req.SenderJID, mapaDeLIDDoCliente(client))
			if err != nil {
				writeJSONError(w, http.StatusInternalServerError, err.Error())
				return
			}
			writeJSON(w, resp)
		})
	}

	// Handler for archiving / unarchiving a chat
	http.HandleFunc("/api/archive_chat", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		var req ArchiveChatRequest
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, fmt.Sprintf("Invalid request format: %v", err), http.StatusBadRequest)
			return
		}
		if req.ChatJID == "" {
			http.Error(w, "Invalid request: chat_jid required", http.StatusBadRequest)
			return
		}
		if req.Archive == nil {
			http.Error(w, "Invalid request: archive (true|false) required", http.StatusBadRequest)
			return
		}
		chatJID, err := types.ParseJID(req.ChatJID)
		if err != nil {
			http.Error(w, fmt.Sprintf("Invalid chat_jid: %v", err), http.StatusBadRequest)
			return
		}
		if client == nil || !client.IsConnected() {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		ctx := context.Background()
		// last message timestamp/key are optional; zero values are accepted by BuildArchive.
		if err := safeSendAppState(client, ctx, appstate.BuildArchive(chatJID, *req.Archive, time.Time{}, nil)); err != nil {
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusInternalServerError)
			json.NewEncoder(w).Encode(MarkChatResponse{Success: false, Message: fmt.Sprintf("AppState error: %v", err)})
			return
		}
		action := "archived"
		if !*req.Archive {
			action = "unarchived"
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(MarkChatResponse{Success: true, Message: fmt.Sprintf("Chat %s %s", req.ChatJID, action)})
	})

	// Handler for reacting to a message. Empty emoji removes an existing reaction.
	http.HandleFunc("/api/react", handleReact(client, messageStore))

	// Handler for editing the text of a previously sent message.
	http.HandleFunc("/api/edit", handleEdit(client, messageStore))

	// Handler for revoking (deleting for everyone) a previously sent message.
	http.HandleFunc("/api/revoke", handleRevoke(client, messageStore))

	// Handler for the D3 explicit lookup of a deleted/edited message's
	// original content (soft delete, 2026-09-24).
	http.HandleFunc("/api/deleted_message", handleDeletedMessage(client, messageStore))

	// Handler for adding, removing, promoting or demoting group participants.
	http.HandleFunc("/api/group_participants", handleGroupParticipants(client))

	// T001 — Gap #12: group invites
	http.HandleFunc("/api/group_invite_link", handleGroupInviteLink(client))
	http.HandleFunc("/api/group_invite_info", handleGroupInviteInfo(client))
	http.HandleFunc("/api/join_group_with_link", handleJoinGroup(client))

	// T002 — Gap #13: group settings and photo
	http.HandleFunc("/api/group_settings", handleGroupSettings(client))
	http.HandleFunc("/api/group_photo", handleGroupPhoto(client))

	// T003 — Gap #10: user info
	http.HandleFunc("/api/user_info", handleUserInfo(client))
	http.HandleFunc("/api/profile_picture", handleProfilePicture(client))

	// T004 — Gap #11: polls
	http.HandleFunc("/api/create_poll", handleCreatePoll(client, messageStore))
	http.HandleFunc("/api/vote_poll", handleVotePoll(client, messageStore))
	http.HandleFunc("/api/poll_results", handlePollResults(messageStore))

	// Handler for sending a typing/recording indicator to a chat.
	http.HandleFunc("/api/chat_presence", handleChatPresence(client))

	// Handler for checking whether phone numbers are registered on WhatsApp.
	http.HandleFunc("/api/is_on_whatsapp", handleIsOnWhatsApp(client))

	// Handler for resolving a phone number to all its JIDs (regular + LID).
	// Replaces the Python-side direct read of whatsmeow_lid_map.
	http.HandleFunc("/api/resolve_contact", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		phone := strings.TrimSpace(r.URL.Query().Get("phone"))
		if phone == "" {
			w.WriteHeader(http.StatusBadRequest)
			json.NewEncoder(w).Encode(ResolveContactResponse{Success: false, Message: "phone required"})
			return
		}
		if client == nil || !client.IsConnected() {
			w.WriteHeader(http.StatusServiceUnavailable)
			json.NewEncoder(w).Encode(ResolveContactResponse{Success: false, Message: "WhatsApp client not connected"})
			return
		}
		jids := resolveContactJIDs(client, phone)
		json.NewEncoder(w).Encode(ResolveContactResponse{Success: true, Phone: normalizePhone(phone), JIDs: jids})
	})

	// Handler for searching contacts by name or phone across the three sources
	// the bridge owns (contact store + senders + chats). Replaces the Python-side
	// direct read of whatsmeow_contacts. Degrades to senders+chats when the client
	// is offline (the contact store is unavailable but the local tables aren't).
	http.HandleFunc("/api/search_contacts", func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodGet {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		query := strings.TrimSpace(r.URL.Query().Get("query"))
		if query == "" {
			w.WriteHeader(http.StatusBadRequest)
			json.NewEncoder(w).Encode(SearchContactsResponse{Success: false, Message: "query required"})
			return
		}
		msg := ""
		if client == nil || !client.IsConnected() {
			// Degrade gracefully: local tables still answer, contact store won't.
			msg = "client offline: contact store skipped, searched senders+chats only"
		}
		hits := searchContactsBridge(client, messageStore, query)
		json.NewEncoder(w).Encode(SearchContactsResponse{Success: true, Message: msg, Contacts: hits})
	})

	// Bind to loopback only — no auth on REST API, anyone on LAN could send messages.
	// Set BIND_ADDR=0.0.0.0 (or a specific interface IP, e.g. a Tailscale address) to opt into wider exposure.
	bindAddr := os.Getenv("BIND_ADDR")
	if bindAddr == "" {
		bindAddr = "127.0.0.1"
	}
	serverAddr := fmt.Sprintf("%s:%d", bindAddr, port)
	fmt.Printf("Starting REST API server on %s...\n", serverAddr)

	// If BIND_ADDR is not loopback, an auth token is required — the /api/* routes
	// can send messages and read message history, so anyone who can reach the port
	// must present a bearer token. /qr and /qr.png stay open (that's the pairing flow itself).
	authToken := os.Getenv("API_AUTH_TOKEN")
	if bindAddr != "127.0.0.1" && bindAddr != "localhost" && authToken == "" {
		fmt.Println("FATAL: BIND_ADDR is set to a non-loopback address but API_AUTH_TOKEN is not set. Refusing to start exposed without auth.")
		os.Exit(1)
	}

	handler := http.DefaultServeMux
	var finalHandler http.Handler = handler
	if authToken != "" {
		finalHandler = requireBearerToken(authToken, handler)
	}

	// Run server in a goroutine so it doesn't block
	go func() {
		if err := http.ListenAndServe(serverAddr, finalHandler); err != nil {
			fmt.Printf("REST API server error: %v\n", err)
		}
	}()
}

// requireBearerToken wraps a handler so every /api/* request must present
// "Authorization: Bearer <token>". /qr and /qr.png stay open since that's
// the initial pairing flow, not an authenticated API call.
func requireBearerToken(token string, next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if !strings.HasPrefix(r.URL.Path, "/api/") {
			next.ServeHTTP(w, r)
			return
		}
		expected := "Bearer " + token
		if got := r.Header.Get("Authorization"); got != expected {
			http.Error(w, "Unauthorized", http.StatusUnauthorized)
			return
		}
		next.ServeHTTP(w, r)
	})
}

// watchdogLoop runs the automatic reconnection logic on an interval (T004).
// It checks connected/loggedIn state and decides whether to reconnect.
func watchdogLoop(client *whatsmeow.Client, logger waLog.Logger) {
	// Parse WHATSAPP_WATCHDOG_INTERVAL, default 60s, minimum 10s
	interval := 60
	if portStr := os.Getenv("WHATSAPP_WATCHDOG_INTERVAL"); portStr != "" {
		if parsed, err := strconv.Atoi(portStr); err == nil && parsed >= 10 {
			interval = parsed
		} else {
			logger.Infof("Watchdog interval invalid or < 10: %s, using default 60s", portStr)
		}
	}
	logger.Infof("Watchdog starting with interval %d seconds", interval)

	// Publish the interval the loop actually resolved, so /api/status reports
	// what is in force instead of re-reading the environment on its own.
	watchdogState.Lock()
	watchdogState.effectiveInterval = interval
	watchdogState.Unlock()

	ticker := time.NewTicker(time.Duration(interval) * time.Second)
	defer ticker.Stop()

	for range ticker.C {
		// Stamped before any early return, so a tick counts as a tick even when
		// there is nothing to do — that is precisely the case a caller needs to
		// distinguish from a dead loop.
		watchdogState.Lock()
		watchdogState.lastTickAt = time.Now()
		watchdogState.Unlock()

		if client == nil {
			continue
		}

		connected := client.IsConnected()
		loggedIn := client.Store != nil && client.Store.ID != nil

		decision := decideWatchdogAction(connected, loggedIn)
		reconnect, attempt, warnLoggedOut := applyWatchdogDecision(decision)

		if warnLoggedOut {
			logger.Warnf("Watchdog: device logged out, reconnect impossible without QR scan")
		}
		if reconnect {
			logger.Warnf("Watchdog: attempting reconnect (attempt %d)", attempt)
			if err := client.Connect(); err != nil {
				logger.Warnf("Watchdog reconnect failed: %v", err)
			}
		}
	}
}

// applyWatchdogDecision applies one tick to the shared watchdog state and
// returns what the caller must do outside the lock: whether to reconnect, which
// attempt number to log, and whether this tick earned a logged-out warning.
//
// Returning the attempt number instead of letting the caller read
// watchdogState.reconnects is not cosmetic. The first version logged
// "attempt %d" by reading that field *after* releasing the mutex — an
// unsynchronized read of mutex-protected state, racing with every concurrent
// GET /api/status. It survived a green `go test -race` run only because no test
// ever started the watchdog goroutine, which is the same reason this function
// exists: the effects (Connect, logging) are now outside, so the state
// transitions can be driven from a test.
func applyWatchdogDecision(d watchdogDecision) (reconnect bool, attempt int, warnLoggedOut bool) {
	watchdogState.Lock()
	defer watchdogState.Unlock()

	switch d {
	case watchdogNone:
		// Any healthy tick clears the streak, so two *consecutive* bad ticks are
		// required — a single blip is probably the library's own backoff working.
		watchdogState.disconnectedTicks = 0
		// Also clears the logged-out warning streak: after a re-pair, the next
		// logout has to warn immediately instead of inheriting the old counter.
		watchdogState.loggedOutWarnTick = 0

	case watchdogReconnect:
		watchdogState.disconnectedTicks++
		if watchdogState.disconnectedTicks >= 2 {
			watchdogState.lastAction = watchdogReconnect
			watchdogState.lastActionAt = time.Now()
			watchdogState.reconnects++
			watchdogState.disconnectedTicks = 0
			return true, watchdogState.reconnects, false
		}

	case watchdogLoggedOut:
		watchdogState.lastAction = watchdogLoggedOut
		watchdogState.lastActionAt = time.Now()
		// Warn on the first tick of a logged-out streak, then at most once every
		// 10. Warning only on the 10th would keep a dead session silent for ten
		// minutes at the default interval — the opposite of the point.
		warn := watchdogState.loggedOutWarnTick == 0
		watchdogState.loggedOutWarnTick++
		if watchdogState.loggedOutWarnTick >= 10 {
			watchdogState.loggedOutWarnTick = 0
		}
		return false, 0, warn
	}
	return false, 0, false
}

func main() {
	// Set up logger
	logger := waLog.Stdout("Client", "INFO", true)
	logger.Infof("Starting WhatsApp client...")

	// Create database connection for storing session data
	dbLog := waLog.Stdout("Database", "INFO", true)

	// Create directory for database if it doesn't exist
	if err := os.MkdirAll("store", 0755); err != nil {
		logger.Errorf("Failed to create store directory: %v", err)
		return
	}

	container, err := sqlstore.New(context.Background(), "sqlite3", storeDSN(), dbLog)
	if err != nil {
		logger.Errorf("Failed to connect to database: %v", err)
		return
	}

	// Get device store - This contains session information
	deviceStore, err := container.GetFirstDevice(context.Background())
	if err != nil {
		if err == sql.ErrNoRows {
			// No device exists, create one
			deviceStore = container.NewDevice()
			logger.Infof("Created new device")
		} else {
			logger.Errorf("Failed to get device: %v", err)
			return
		}
	}

	// Request a full history sync on pairing (only fires on a fresh QR scan).
	// WhatsApp delivers up to this window as events.HistorySync after login.
	store.DeviceProps.RequireFullSync = proto.Bool(true)
	store.DeviceProps.HistorySyncConfig = &waCompanionReg.DeviceProps_HistorySyncConfig{
		FullSyncDaysLimit:   proto.Uint32(365),
		FullSyncSizeMbLimit: proto.Uint32(10240),
		StorageQuotaMb:      proto.Uint32(10240),
	}

	// Create client instance
	client := whatsmeow.NewClient(deviceStore, logger)
	if client == nil {
		logger.Errorf("Failed to create WhatsApp client")
		return
	}

	// Initialize message store
	messageStore, err := NewMessageStore()
	if err != nil {
		logger.Errorf("Failed to initialize message store: %v", err)
		return
	}
	defer messageStore.Close()

	// Setup event handling for messages and history sync
	client.AddEventHandler(func(evt interface{}) {
		// Record the timestamp of any event (RF-02).
		// This is read by the /api/status handler (different thread).
		lastEventAtNanos.Store(time.Now().UnixNano())

		switch v := evt.(type) {
		case *events.Message:
			// Process regular messages
			handleMessage(client, messageStore, v, logger)

		case *events.HistorySync:
			// Process history sync events
			handleHistorySync(client, messageStore, v, logger)

		case *events.MediaRetry:
			// Phone responded to a media retry request with a (hopefully) fresh
			// directPath. Handle off the event loop — it does a synchronous
			// download + disk write, and whatsmeow serializes event callbacks,
			// so running it inline would stall all other events during a
			// recover_audios.py flood.
			go handleMediaRetry(client, messageStore, v, logger)

		case *events.Connected:
			logger.Infof("Connected to WhatsApp")
			go SyncAllContacts(client, messageStore, logger)
			sweepOnce.Do(func() { startTranscriptionSweep(5 * time.Minute) })

		case *events.LoggedOut:
			logger.Warnf("Device logged out, please scan QR code to log in again")
		}
	})

	// Create channel to track connection success
	connected := make(chan bool, 1)

	// Start REST API server early so /qr is available during the QR pairing flow.
	bridgePort := 8080
	if portStr := os.Getenv("WHATSAPP_BRIDGE_PORT"); portStr != "" {
		if p, err := fmt.Sscanf(portStr, "%d", &bridgePort); p != 1 || err != nil {
			bridgePort = 8080
		}
	}
	startRESTServer(client, messageStore, bridgePort)

	// Connect to WhatsApp
	if client.Store.ID == nil {
		// No ID stored, this is a new client, need to pair with phone
		qrChan, _ := client.GetQRChannel(context.Background())
		err = client.Connect()
		if err != nil {
			logger.Errorf("Failed to connect: %v", err)
			return
		}

		fmt.Printf("\nOpen http://localhost:%d/qr in your browser to scan the QR code.\n", bridgePort)

		// Print QR code for pairing with phone
		for evt := range qrChan {
			if evt.Event == "code" {
				fmt.Println("\nScan this QR code with your WhatsApp app:")
				qrterminal.GenerateHalfBlock(evt.Code, qrterminal.L, os.Stdout)

				// Generate PNG and store in memory for /qr endpoint.
				if pngBytes, err := goqr.Encode(evt.Code, goqr.Medium, 512); err == nil {
					qrState.Lock()
					qrState.png = pngBytes
					qrState.connected = false
					qrState.Unlock()
				}

				// Also save to disk for convenience.
				qrFilename, err := accountScopedTempFilename("whatsapp-qr.png")
				if err != nil {
					fmt.Printf("\nCould not derive QR filename: %v\n", err)
					continue
				}
				qrFile := filepath.Join(os.TempDir(), qrFilename)
				if err := goqr.WriteFile(evt.Code, goqr.Medium, 512, qrFile); err != nil {
					// Previously this failure was swallowed by `err == nil`, so on
					// any OS where the path was unwritable the QR just never
					// appeared and nothing said why.
					fmt.Printf("\nCould not save QR image to %s: %v\n", qrFile, err)
				} else {
					fmt.Printf("\nQR also saved as image: %s\n", qrFile)
					if err := openInDefaultApp(qrFile); err != nil {
						fmt.Printf("Could not open it automatically (%v) — open the file, or use the /qr endpoint.\n", err)
					}
				}
			} else if evt.Event == "success" {
				qrState.Lock()
				qrState.png = nil
				qrState.connected = true
				qrState.Unlock()
				connected <- true
				break
			}
		}

		// Wait for connection
		select {
		case <-connected:
			fmt.Println("\nSuccessfully connected and authenticated!")
		case <-time.After(3 * time.Minute):
			logger.Errorf("Timeout waiting for QR code scan")
			return
		}
	} else {
		// Already logged in, just connect
		err = client.Connect()
		if err != nil {
			logger.Errorf("Failed to connect: %v", err)
			return
		}
		qrState.Lock()
		qrState.connected = true
		qrState.Unlock()
		connected <- true
	}

	// Wait a moment for connection to stabilize
	time.Sleep(2 * time.Second)

	if !client.IsConnected() {
		logger.Errorf("Failed to establish stable connection")
		return
	}

	fmt.Println("\n✓ Connected to WhatsApp! Type 'help' for commands.")

	// Initialize watchdog state
	watchdogState.Lock()
	watchdogState.upstartTime = time.Now()
	watchdogState.lastAction = watchdogNone
	watchdogState.Unlock()

	// Start watchdog goroutine (T004)
	go watchdogLoop(client, logger)

	// Merge any chats stored under LID JIDs into their PN equivalents.
	migrateLIDChats(client, messageStore, logger)

	// Create a channel to keep the main goroutine alive
	exitChan := make(chan os.Signal, 1)
	signal.Notify(exitChan, syscall.SIGINT, syscall.SIGTERM)

	fmt.Println("REST server is running. Press Ctrl+C to disconnect and exit.")

	// Wait for termination signal
	<-exitChan

	fmt.Println("Disconnecting...")
	// Disconnect client
	client.Disconnect()
}

// GetChatName determines the appropriate name for a chat based on JID and other info
func GetChatName(client *whatsmeow.Client, messageStore *MessageStore, jid types.JID, chatJID string, conversation interface{}, sender string, logger waLog.Logger) string {
	// First, check if chat already exists in database with a name
	var existingName string
	err := messageStore.db.QueryRow("SELECT name FROM chats WHERE jid = ?", chatJID).Scan(&existingName)
	if err == nil && existingName != "" {
		// Chat exists with a name, use that
		logger.Infof("Using existing chat name for %s: %s", chatJID, existingName)
		return existingName
	}

	// Need to determine chat name
	var name string

	if jid.Server == "g.us" {
		// This is a group chat
		logger.Infof("Getting name for group: %s", chatJID)

		// Use conversation data if provided (from history sync)
		if conversation != nil {
			// Extract name from conversation if available
			// This uses type assertions to handle different possible types
			var displayName, convName *string
			// Try to extract the fields we care about regardless of the exact type
			v := reflect.ValueOf(conversation)
			if v.Kind() == reflect.Ptr && !v.IsNil() {
				v = v.Elem()

				// Try to find DisplayName field
				if displayNameField := v.FieldByName("DisplayName"); displayNameField.IsValid() && displayNameField.Kind() == reflect.Ptr && !displayNameField.IsNil() {
					dn := displayNameField.Elem().String()
					displayName = &dn
				}

				// Try to find Name field
				if nameField := v.FieldByName("Name"); nameField.IsValid() && nameField.Kind() == reflect.Ptr && !nameField.IsNil() {
					n := nameField.Elem().String()
					convName = &n
				}
			}

			// Use the name we found
			if displayName != nil && *displayName != "" {
				name = *displayName
			} else if convName != nil && *convName != "" {
				name = *convName
			}
		}

		// If we didn't get a name, try group info
		if name == "" {
			groupInfo, err := client.GetGroupInfo(context.Background(), jid)
			if err == nil && groupInfo.Name != "" {
				name = groupInfo.Name
			} else {
				// Fallback name for groups
				name = fmt.Sprintf("Group %s", jid.User)
			}
		}

		logger.Infof("Using group name: %s", name)
	} else {
		// This is an individual contact
		logger.Infof("Getting name for contact: %s", chatJID)

		// Try senders table first (populated from every message event and SyncAllContacts)
		if resolved := messageStore.ResolveName(chatJID); resolved != "" {
			name = resolved
		} else {
			contact, err := client.Store.Contacts.GetContact(context.Background(), jid)
			if err == nil && contact.FullName != "" {
				name = contact.FullName
			} else if err == nil && contact.BusinessName != "" {
				name = contact.BusinessName
			} else if err == nil && contact.PushName != "" {
				name = contact.PushName
			} else if sender != "" {
				name = sender
			} else {
				name = jid.User
			}
		}

		logger.Infof("Using contact name: %s", name)
	}

	return name
}

// Handle history sync events
func handleHistorySync(client *whatsmeow.Client, messageStore *MessageStore, historySync *events.HistorySync, logger waLog.Logger) {
	fmt.Printf("Received history sync event with %d conversations\n", len(historySync.Data.Conversations))

	syncedCount := 0
	for _, conversation := range historySync.Data.Conversations {
		// Parse JID from the conversation
		if conversation.ID == nil {
			continue
		}

		chatJID := *conversation.ID

		// Try to parse the JID
		jid, err := types.ParseJID(chatJID)
		if err != nil {
			logger.Warnf("Failed to parse JID %s: %v", chatJID, err)
			continue
		}

		// Normalize LID -> PN at write time
		jid = resolveToPN(client, jid)
		chatJID = jid.String()

		// Get appropriate chat name by passing the history sync conversation directly
		name := GetChatName(client, messageStore, jid, chatJID, conversation, "", logger)

		// Process messages
		messages := conversation.Messages
		if len(messages) > 0 {
			// Update chat with latest message timestamp
			latestMsg := messages[0]
			if latestMsg == nil || latestMsg.Message == nil {
				continue
			}

			// Get timestamp from message info
			timestamp := time.Time{}
			if ts := latestMsg.Message.GetMessageTimestamp(); ts != 0 {
				timestamp = time.Unix(int64(ts), 0)
			} else {
				continue
			}

			messageStore.StoreChat(chatJID, name, timestamp)

			// Store messages
			syncedCount += storeHistoryConversation(client, messageStore, jid, chatJID, messages, logger)
		}
	}

	fmt.Printf("History sync complete. Stored %d messages.\n", syncedCount)
	SyncAllContacts(client, messageStore, logger)
}

// pendingHistorySyncProtocolMsg is a ProtocolMessage (REVOKE or MESSAGE_EDIT)
// found while storing a history-sync conversation, held until every message
// of that conversation has been written (D3, issue #23) — see
// storeHistoryConversation.
type pendingHistorySyncProtocolMsg struct {
	pm *waProto.ProtocolMessage
	at time.Time
}

// historySyncSender determines the sender and is-from-me flag for a history
// sync entry from its key, the same logic handleHistorySync always used —
// pulled out here so both the stub-REVOKE path and the regular StoreMessage
// path in storeHistoryConversation share it instead of duplicating it.
//
// senderJID is the full author JID the live path records in sender_jid (D8),
// derived the same way (issue #28, D1): the key's participant in a group, the
// chat itself in a 1:1, the account without its device part for our own
// messages. It stays empty when the author can't be told — a participant that
// doesn't parse, or an entry with no participant in anything but a 1:1 (group,
// status@broadcast, newsletter) — so the row reads as unknown author (D9)
// instead of getting the chat's own JID as its author: isUnknownAuthor only
// catches that for @g.us, so a broadcast JID would pass as a real author.
func historySyncSender(client *whatsmeow.Client, jid types.JID, key *waCommon.MessageKey) (sender, senderJID string, isFromMe bool) {
	if key == nil {
		return jid.User, "", false
	}
	if key.FromMe != nil {
		isFromMe = *key.FromMe
	}
	if !isFromMe && key.Participant != nil && *key.Participant != "" {
		if pjid, err := types.ParseJID(*key.Participant); err == nil {
			pn := resolveToPN(client, pjid)
			sender = pn.User
			senderJID = pn.String()
		} else {
			sender = *key.Participant
		}
	} else if isFromMe {
		sender = client.Store.ID.User
		senderJID = client.Store.ID.ToNonAD().String()
	} else {
		sender = jid.User
		if jid.Server == types.DefaultUserServer || jid.Server == types.HiddenUserServer {
			senderJID = resolveToPN(client, jid).String()
		}
	}
	return sender, senderJID, isFromMe
}

// unwrapHistoryMessage peels the same wrappers the live path gets peeled by
// events.Message.UnwrapRaw (DeviceSentMessage, EphemeralMessage, ViewOnce,
// EditedMessage...). A revoke or edit made from one of the user's own other
// devices reaches the history sync inside DeviceSentMessage, and reading
// GetProtocolMessage() off the outer message would miss it (review of #23).
// It matters for every edit, too: BuildEdit sends MESSAGE_EDIT inside
// EditedMessage, never as a bare ProtocolMessage.
func unwrapHistoryMessage(m *waProto.Message) *waProto.Message {
	if m == nil {
		return nil
	}
	return (&events.Message{RawMessage: m}).UnwrapRaw().Message
}

// storeHistoryConversation stores the messages of one history-sync
// conversation (issue #23). The sync delivers newest-first, so a
// ProtocolMessage REVOKE/MESSAGE_EDIT arrives before the message it targets —
// applying it right away would never find the target row (D3). Every such
// entry is deferred into pending instead of going through StoreMessage, and
// applied with applyProtocolMessage only after the whole conversation has
// been written.
//
// A stub entry (no waE2E message, just a system event) with type REVOKE is
// how the sync delivers "this message was deleted for everyone" (D1): it is
// routed through the same applyProtocolMessage path the live revoke event
// uses, so a message the store already has is revoked and its cached media
// removed. When the store never saw the original (a fresh database), that
// leaves nothing to revoke — StoreRevokedTombstone then leaves a placeholder
// row so the conversation keeps the gap (D2); its ON CONFLICT DO NOTHING
// makes the call a no-op for the case the row already exists.
//
// Returns how many rows it stored.
func storeHistoryConversation(client *whatsmeow.Client, messageStore *MessageStore, jid types.JID, chatJID string, messages []*waHistorySync.HistorySyncMsg, logger waLog.Logger) int {
	syncedCount := 0
	var pending []*pendingHistorySyncProtocolMsg

	for _, msg := range messages {
		if msg == nil || msg.Message == nil {
			continue
		}

		msgID := ""
		if msg.Message.Key != nil && msg.Message.Key.ID != nil {
			msgID = *msg.Message.Key.ID
		}

		// Get message timestamp
		timestamp := time.Time{}
		if ts := msg.Message.GetMessageTimestamp(); ts != 0 {
			timestamp = time.Unix(int64(ts), 0)
		} else {
			continue
		}

		if msg.Message.Message == nil {
			if msgID != "" {
				if msg.Message.GetMessageStubType() == waWeb.WebMessageInfo_REVOKE {
					sender, _, isFromMe := historySyncSender(client, jid, msg.Message.Key)
					applyProtocolMessage(messageStore, chatJID, &waProto.ProtocolMessage{
						Type: waProto.ProtocolMessage_REVOKE.Enum(),
						Key:  &waCommon.MessageKey{ID: proto.String(msgID)},
					}, timestamp, logger)
					if err := messageStore.StoreRevokedTombstone(msgID, chatJID, sender, timestamp, isFromMe); err != nil {
						logger.Warnf("Failed to store revoked tombstone for %s: %v", msgID, err)
					}
				}
			}
			continue
		}

		if pm := unwrapHistoryMessage(msg.Message.GetMessage()).GetProtocolMessage(); pm != nil &&
			(pm.GetType() == waProto.ProtocolMessage_REVOKE || pm.GetType() == waProto.ProtocolMessage_MESSAGE_EDIT) {
			pending = append(pending, &pendingHistorySyncProtocolMsg{pm: pm, at: timestamp})
			continue
		}

		// The sync hands over the raw message, still wrapped in
		// EphemeralMessage (disappearing-messages chats), DeviceSentMessage
		// (sent from another of the user's devices), ViewOnce... — the live
		// path gets it already unwrapped by whatsmeow. Read the content from
		// the same shape, or a wrapped message looks empty and is dropped (#25).
		inner := unwrapHistoryMessage(msg.Message.Message)

		// Extract text content (includes media captions)
		content := extractTextContent(inner)

		// Extract media info
		var mediaType, filename, url string
		var mediaKey, fileSHA256, fileEncSHA256 []byte
		var fileLength uint64

		if inner != nil {
			mediaType, filename, url, mediaKey, fileSHA256, fileEncSHA256, fileLength = extractMediaInfo(inner)
		}

		// Log the message content for debugging
		logger.Infof("Message content: %v, Media Type: %v", content, mediaType)

		// Skip messages with no content and no media
		if content == "" && mediaType == "" {
			continue
		}

		sender, senderJID, isFromMe := historySyncSender(client, jid, msg.Message.Key)

		err := messageStore.StoreMessage(
			msgID,
			chatJID,
			sender,
			content,
			timestamp,
			isFromMe,
			mediaType,
			filename,
			url,
			mediaKey,
			fileSHA256,
			fileEncSHA256,
			fileLength,
		)
		if err != nil {
			logger.Warnf("Failed to store history message: %v", err)
		} else {
			syncedCount++
			// #28: the author and the quote/mention context, the two writes the
			// live path makes right after StoreMessage (D8, D1/D13) — without
			// them a synced message can't be quoted, reacted to or revoked as
			// someone else's, and doesn't show what it replied to.
			if err := messageStore.StoreMessageSenderJID(msgID, chatJID, senderJID); err != nil {
				logger.Warnf("Failed to store history message sender_jid: %v", err)
			}
			if ci := extractContextInfo(inner); ci != nil {
				if err := messageStore.StoreMessageContext(msgID, chatJID, ci); err != nil {
					logger.Warnf("Failed to store history message context: %v", err)
				}
			}
			// Log successful message storage
			if mediaType != "" {
				logger.Infof("Stored message: [%s] %s -> %s: [%s: %s] %s",
					timestamp.Format("2006-01-02 15:04:05"), sender, chatJID, mediaType, filename, content)
			} else {
				logger.Infof("Stored message: [%s] %s -> %s: %s",
					timestamp.Format("2006-01-02 15:04:05"), sender, chatJID, content)
			}
		}
	}

	for _, pm := range pending {
		applyProtocolMessage(messageStore, chatJID, pm.pm, pm.at, logger)
	}

	return syncedCount
}

// Request history sync from the server
// requestHistorySync asks the primary device (phone) for `count` messages
// immediately BEFORE lastKnown, via whatsmeow's on-demand history sync
// (BuildHistorySyncRequest + SendPeerMessage — see
// https://github.com/tulir/whatsmeow/blob/main/send.go). lastKnown must be a
// real, already-known message (chat/ID/IsFromMe/timestamp) — the whatsmeow
// call dereferences it unconditionally and panics on nil. The response
// arrives later as a normal *events.HistorySync (type ON_DEMAND), handled by
// the same handleHistorySync used for the initial pairing sync — no separate
// handler needed.
func requestHistorySync(client *whatsmeow.Client, lastKnown *types.MessageInfo, count int) {
	if client == nil || !client.IsConnected() || client.Store.ID == nil {
		fmt.Println("Client not ready for history sync request.")
		return
	}
	if lastKnown == nil {
		fmt.Println("requestHistorySync: lastKnown message info is required (whatsmeow dereferences it unconditionally).")
		return
	}

	historyMsg := client.BuildHistorySyncRequest(lastKnown, count)
	_, err := client.SendPeerMessage(context.Background(), historyMsg)
	if err != nil {
		fmt.Printf("Failed to request history sync: %v\n", err)
	} else {
		fmt.Printf("History sync requested for %d messages before %s in %s. Waiting for server response...\n",
			count, lastKnown.ID, lastKnown.Chat.String())
	}
}

// sweepOnce guards against launching the transcription ticker more than once,
// since events.Connected fires on every reconnect.
var sweepOnce sync.Once

// accountScopedTempFilename derives a temporary filename from a base name and
// the WHATSAPP_ACCOUNT environment variable. If the variable is unset or empty,
// it returns the base name unchanged; otherwise, it inserts the sanitized
// account name before the file extension.
//
// Invalid characters (/, \, :, ..) in the account name are rejected with an error.
func accountScopedTempFilename(basename string) (string, error) {
	account := os.Getenv("WHATSAPP_ACCOUNT")
	if account == "" {
		return basename, nil
	}

	// Validate account name: reject characters that cannot appear in filenames.
	// The checks below must align with what the OS forbids.
	invalidChars := []string{"/", "\\", ":", ".."}
	for _, c := range invalidChars {
		if strings.Contains(account, c) {
			return "", fmt.Errorf("invalid account name %q: contains %q", account, c)
		}
	}

	// Split basename into name and extension
	ext := filepath.Ext(basename)
	name := basename[:len(basename)-len(ext)]

	// Insert account name before extension
	return name + "-" + account + ext, nil
}

// startTranscriptionSweep periodically shells out to the Python transcriber to
// turn newly-arrived audio messages into searchable text. Whisper runs in a
// separate process so it never blocks the bridge's message handling. A lockfile
// prevents overlapping runs if a sweep outlasts the interval (e.g. a backlog
// after downtime).
func startTranscriptionSweep(interval time.Duration) {
	pyDir, err := filepath.Abs("../whatsapp-mcp-server")
	if err != nil {
		fmt.Printf("transcription sweep disabled: %v\n", err)
		return
	}
	python := venvPython(pyDir)
	script := filepath.Join(pyDir, "transcribe.py")
	lockFilename, err := accountScopedTempFilename("wa_transcribe.lock")
	if err != nil {
		fmt.Printf("transcription sweep disabled: %v\n", err)
		return
	}
	lockPath := filepath.Join(os.TempDir(), lockFilename)

	if _, err := os.Stat(python); err != nil {
		fmt.Printf("transcription sweep disabled: python not found at %s\n", python)
		return
	}
	if _, err := os.Stat(script); err != nil {
		fmt.Printf("transcription sweep disabled: script not found at %s\n", script)
		return
	}

	go func() {
		ticker := time.NewTicker(interval)
		defer ticker.Stop()
		for range ticker.C {
			// Drop media-retry entries the phone never answered, so unused
			// decryption keys don't accumulate in memory across a long run.
			mediaRetryCache.evictOlderThan(30*time.Minute, time.Now())

			// Skip if a previous sweep is still running.
			if data, err := os.ReadFile(lockPath); err == nil {
				if pid, perr := strconv.Atoi(strings.TrimSpace(string(data))); perr == nil {
					if processAlive(pid) {
						continue // prior sweep alive
					}
				}
			}
			cmd := exec.Command(python, script)
			cmd.Dir = pyDir
			// Surface the transcriber's output (its DONE summary, per-audio
			// errors, the oversized-audio RuntimeError) in the bridge log
			// instead of discarding it to /dev/null.
			cmd.Stdout = os.Stdout
			cmd.Stderr = os.Stderr
			// Point transcribe.py at THIS bridge's REST port. Without this it
			// defaults to :8080 and every download fails when the bridge runs
			// on a non-default port. A pre-set WHATSAPP_API_BASE_URL wins.
			cmd.Env = os.Environ()
			if os.Getenv("WHATSAPP_API_BASE_URL") == "" {
				port := "8080"
				if p := os.Getenv("WHATSAPP_BRIDGE_PORT"); p != "" {
					port = p
				}
				cmd.Env = append(cmd.Env, fmt.Sprintf("WHATSAPP_API_BASE_URL=http://localhost:%s/api", port))
			}
			if err := cmd.Start(); err != nil {
				fmt.Printf("transcription sweep: failed to start: %v\n", err)
				continue
			}
			// The lockfile is the only overlap guard; if we can't write it,
			// don't leave a process running unguarded — kill it and retry next tick.
			if err := os.WriteFile(lockPath, []byte(fmt.Sprintf("%d", cmd.Process.Pid)), 0644); err != nil {
				fmt.Printf("transcription sweep: cannot write lockfile (%v); killing sweep to preserve overlap guard\n", err)
				_ = cmd.Process.Kill()
				_ = cmd.Wait()
				continue
			}
			go func(c *exec.Cmd) {
				if err := c.Wait(); err != nil {
					fmt.Printf("transcription sweep: transcribe.py exited with error: %v\n", err)
				}
				_ = os.Remove(lockPath)
			}(cmd)
		}
	}()
	fmt.Printf("Transcription sweep started (every %s)\n", interval)
}

// mediaRetryEntry holds the info needed to decrypt + download a media retry
// response. It is keyed by message ID inside mediaRetryCache. The four crypto
// fields (mediaKey, fileSHA256, fileEncSHA256, fileLength) plus mediaType are
// consumed together by DownloadMediaWithPath and must travel as a set.
type mediaRetryEntry struct {
	chatJID       string
	mediaKey      []byte
	fileSHA256    []byte
	fileEncSHA256 []byte
	fileLength    uint64
	mediaType     string
	filename      string
	storedAt      time.Time
}

// retryCache maps message ID -> pending retry entry. All access goes through its
// methods so the map is never touched without the lock, and consume() evicts on
// read so entries (which pin a decryption key in memory) don't accumulate.
type retryCache struct {
	mu sync.Mutex // guards m
	m  map[string]mediaRetryEntry
}

func (c *retryCache) store(id string, e mediaRetryEntry) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.m[id] = e
}

// consume returns the entry for id and removes it, so a retry response is
// handled at most once and the key material is freed.
func (c *retryCache) consume(id string) (mediaRetryEntry, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	e, ok := c.m[id]
	if ok {
		delete(c.m, id)
	}
	return e, ok
}

// evictOlderThan drops entries the phone never answered, so a media-retry
// request that gets no response doesn't leak its key material forever.
func (c *retryCache) evictOlderThan(maxAge time.Duration, now time.Time) {
	c.mu.Lock()
	defer c.mu.Unlock()
	for id, e := range c.m {
		if now.Sub(e.storedAt) > maxAge {
			delete(c.m, id)
		}
	}
}

var mediaRetryCache = &retryCache{m: make(map[string]mediaRetryEntry)}

// requestMediaRetry asks the phone to re-upload media whose CDN reference has
// expired (download returns 403). The phone responds with an events.MediaRetry
// carrying a fresh directPath, handled by handleMediaRetry.
func requestMediaRetry(client *whatsmeow.Client, messageStore *MessageStore, messageID, chatJID string) error {
	// Soft delete keeps the media keys, so the "no media key" refusal below no
	// longer covers a deleted message: refuse it explicitly, before asking the
	// phone for anything.
	if deleted, err := messageStore.IsMessageRevoked(messageID, chatJID); err != nil {
		return fmt.Errorf("failed to check message: %v", err)
	} else if deleted {
		return fmt.Errorf("message was deleted by the sender")
	}
	mediaType, filename, _, mediaKey, fileSHA256, fileEncSHA256, fileLength, err := messageStore.GetMediaInfo(messageID, chatJID)
	if err != nil {
		return fmt.Errorf("failed to get media info: %v", err)
	}
	if len(mediaKey) == 0 {
		return fmt.Errorf("no media key for message")
	}

	jid, err := types.ParseJID(chatJID)
	if err != nil {
		return fmt.Errorf("invalid chat jid: %v", err)
	}

	// Read sender + direction: groups require the participant JID in the retry
	// receipt, and from-me messages must be flagged correctly.
	var sender string
	var isFromMe bool
	err = messageStore.db.QueryRow(
		"SELECT sender, is_from_me FROM messages WHERE id = ? AND chat_jid = ?",
		messageID, chatJID,
	).Scan(&sender, &isFromMe)
	if err != nil {
		return fmt.Errorf("failed to read message sender: %v", err)
	}

	isGroup := jid.Server == types.GroupServer
	senderJID := jid
	if isGroup && sender != "" {
		senderJID = types.JID{User: sender, Server: types.DefaultUserServer}
	}

	mediaRetryCache.store(messageID, mediaRetryEntry{
		chatJID: chatJID, mediaKey: mediaKey, fileSHA256: fileSHA256,
		fileEncSHA256: fileEncSHA256, fileLength: fileLength,
		mediaType: mediaType, filename: filename, storedAt: time.Now(),
	})

	info := &types.MessageInfo{
		ID: messageID,
		MessageSource: types.MessageSource{
			Chat:     jid,
			Sender:   senderJID,
			IsFromMe: isFromMe,
			IsGroup:  isGroup,
		},
	}
	return client.SendMediaRetryReceipt(context.Background(), info, mediaKey)
}

// handleMediaRetry processes the phone's response to a media retry request: on
// success it downloads with the fresh directPath and persists the file so the
// normal download/transcription path can use it.
// writeRecoveredMedia writes a media-retry download to disk, unless the
// sender revoked (deleted for everyone) the message in the meantime — the
// phone's asynchronous retry response must not resurrect bytes on disk for a
// message the store no longer carries (D1, follow-up to issue #21).
func writeRecoveredMedia(messageStore *MessageStore, messageID, chatJID, filename string, data []byte) (string, error) {
	deleted, err := messageStore.IsMessageRevoked(messageID, chatJID)
	if err != nil {
		return "", fmt.Errorf("failed to check message: %v", err)
	}
	if deleted {
		return "", fmt.Errorf("message was deleted by the sender")
	}
	chatDir := fmt.Sprintf("store/%s", strings.ReplaceAll(chatJID, ":", "_"))
	if err := os.MkdirAll(chatDir, 0755); err != nil {
		return "", fmt.Errorf("mkdir failed: %v", err)
	}
	localPath, err := safeMediaPath(chatDir, messageID, filename)
	if err != nil {
		return "", err
	}
	if err := os.WriteFile(localPath, data, 0644); err != nil {
		return "", fmt.Errorf("write failed: %v", err)
	}
	return localPath, nil
}

// Stable log contract consumed by recover_audios.py. Every terminal outcome
// emits exactly one of these tags so the recovery orchestrator can classify it
// without guessing — keep these in sync with the regexes in recover_audios.py.
//
//	MEDIA RETRY <id>: SUCCESS recovered <n> bytes -> <path>
//	MEDIA RETRY <id>: NOTONPHONE <result>   (phone no longer has the file)
//	MEDIA RETRY <id>: ERROR <reason>        (terminal local/decrypt failure)
func handleMediaRetry(client *whatsmeow.Client, messageStore *MessageStore, evt *events.MediaRetry, logger waLog.Logger) {
	// consume() evicts the entry so a duplicate response can't re-run the
	// download and the key material is freed on every path below.
	entry, ok := mediaRetryCache.consume(evt.MessageID)
	if !ok {
		logger.Warnf("media retry response for unknown message %s", evt.MessageID)
		return
	}

	retryData, err := whatsmeow.DecryptMediaRetryNotification(evt, entry.mediaKey)
	if err != nil {
		fmt.Printf("MEDIA RETRY %s: ERROR decrypt failed: %v\n", evt.MessageID, err)
		return
	}
	if retryData.GetResult() != waMmsRetry.MediaRetryNotification_SUCCESS {
		// Phone-side result (NOT_FOUND etc.) — the file is gone from the phone.
		fmt.Printf("MEDIA RETRY %s: NOTONPHONE %s\n", evt.MessageID, retryData.GetResult())
		return
	}

	var waMediaType whatsmeow.MediaType
	switch entry.mediaType {
	case "image":
		waMediaType = whatsmeow.MediaImage
	case "video":
		waMediaType = whatsmeow.MediaVideo
	case "audio":
		waMediaType = whatsmeow.MediaAudio
	case "document":
		waMediaType = whatsmeow.MediaDocument
	default:
		fmt.Printf("MEDIA RETRY %s: ERROR unsupported media type %q\n", evt.MessageID, entry.mediaType)
		return
	}

	newPath := retryData.GetDirectPath()
	// whatsmeow 2026-08-06 dropped the fileLength argument and added allowNoHash
	// as the last one. false keeps the hash check on, matching what the library
	// itself passes from Download/DownloadThumbnail/DownloadFB; only
	// DownloadMediaWithOnlyPath, which has no hash at all, passes true. The
	// retry entry carries fileSHA256 from the DB, so there is a hash to verify.
	data, err := client.DownloadMediaWithPath(context.Background(), newPath,
		entry.fileEncSHA256, entry.fileSHA256, entry.mediaKey,
		waMediaType, "", false)
	if err != nil {
		fmt.Printf("MEDIA RETRY %s: ERROR download with fresh path failed: %v\n", evt.MessageID, err)
		return
	}

	localPath, err := writeRecoveredMedia(messageStore, evt.MessageID, entry.chatJID, entry.filename, data)
	if err != nil {
		fmt.Printf("MEDIA RETRY %s: ERROR %v\n", evt.MessageID, err)
		return
	}
	fmt.Printf("MEDIA RETRY %s: SUCCESS recovered %d bytes -> %s\n", evt.MessageID, len(data), localPath)
}

// analyzeOggOpus tries to extract duration and generate a simple waveform from an Ogg Opus file
func analyzeOggOpus(data []byte) (duration uint32, waveform []byte, err error) {
	// Try to detect if this is a valid Ogg file by checking for the "OggS" signature
	// at the beginning of the file
	if len(data) < 4 || string(data[0:4]) != "OggS" {
		return 0, nil, fmt.Errorf("not a valid Ogg file (missing OggS signature)")
	}

	// Parse Ogg pages to find the last page with a valid granule position
	var lastGranule uint64
	var sampleRate uint32 = 48000 // Default Opus sample rate
	var preSkip uint16 = 0
	var foundOpusHead bool

	// Scan through the file looking for Ogg pages
	for i := 0; i < len(data); {
		// Check if we have enough data to read Ogg page header
		if i+27 >= len(data) {
			break
		}

		// Verify Ogg page signature
		if string(data[i:i+4]) != "OggS" {
			// Skip until next potential page
			i++
			continue
		}

		// Extract header fields
		granulePos := binary.LittleEndian.Uint64(data[i+6 : i+14])
		pageSeqNum := binary.LittleEndian.Uint32(data[i+18 : i+22])
		numSegments := int(data[i+26])

		// Extract segment table
		if i+27+numSegments >= len(data) {
			break
		}
		segmentTable := data[i+27 : i+27+numSegments]

		// Calculate page size
		pageSize := 27 + numSegments
		for _, segLen := range segmentTable {
			pageSize += int(segLen)
		}

		// Check if we're looking at an OpusHead packet (should be in first few pages)
		if !foundOpusHead && pageSeqNum <= 1 {
			// Look for "OpusHead" marker in this page
			pageData := data[i : i+pageSize]
			headPos := bytes.Index(pageData, []byte("OpusHead"))
			if headPos >= 0 && headPos+12 < len(pageData) {
				// Found OpusHead, extract sample rate and pre-skip
				// OpusHead format: Magic(8) + Version(1) + Channels(1) + PreSkip(2) + SampleRate(4) + ...
				headPos += 8 // Skip "OpusHead" marker
				// PreSkip is 2 bytes at offset 10
				if headPos+12 <= len(pageData) {
					preSkip = binary.LittleEndian.Uint16(pageData[headPos+10 : headPos+12])
					sampleRate = binary.LittleEndian.Uint32(pageData[headPos+12 : headPos+16])
					foundOpusHead = true
					fmt.Printf("Found OpusHead: sampleRate=%d, preSkip=%d\n", sampleRate, preSkip)
				}
			}
		}

		// Keep track of last valid granule position
		if granulePos != 0 {
			lastGranule = granulePos
		}

		// Move to next page
		i += pageSize
	}

	if !foundOpusHead {
		fmt.Println("Warning: OpusHead not found, using default values")
	}

	// Calculate duration based on granule position
	if lastGranule > 0 {
		// Formula for duration: (lastGranule - preSkip) / sampleRate
		durationSeconds := float64(lastGranule-uint64(preSkip)) / float64(sampleRate)
		duration = uint32(math.Ceil(durationSeconds))
		fmt.Printf("Calculated Opus duration from granule: %f seconds (lastGranule=%d)\n",
			durationSeconds, lastGranule)
	} else {
		// Fallback to rough estimation if granule position not found
		fmt.Println("Warning: No valid granule position found, using estimation")
		durationEstimate := float64(len(data)) / 2000.0 // Very rough approximation
		duration = uint32(durationEstimate)
	}

	// Make sure we have a reasonable duration (at least 1 second, at most 300 seconds)
	if duration < 1 {
		duration = 1
	} else if duration > 300 {
		duration = 300
	}

	// Generate waveform
	waveform = placeholderWaveform(duration)

	fmt.Printf("Ogg Opus analysis: size=%d bytes, calculated duration=%d sec, waveform=%d bytes\n",
		len(data), duration, len(waveform))

	return duration, waveform, nil
}

// min returns the smaller of x or y
func min(x, y int) int {
	if x < y {
		return x
	}
	return y
}

// placeholderWaveform generates a synthetic waveform for WhatsApp voice messages
// that appears natural with some variability based on the duration
func placeholderWaveform(duration uint32) []byte {
	// WhatsApp expects a 64-byte waveform for voice messages
	const waveformLength = 64
	waveform := make([]byte, waveformLength)

	// Seed the random number generator for consistent results with the same duration
	rand.Seed(int64(duration))

	// Create a more natural looking waveform with some patterns and variability
	// rather than completely random values

	// Base amplitude and frequency - longer messages get faster frequency
	baseAmplitude := 35.0
	frequencyFactor := float64(min(int(duration), 120)) / 30.0

	for i := range waveform {
		// Position in the waveform (normalized 0-1)
		pos := float64(i) / float64(waveformLength)

		// Create a wave pattern with some randomness
		// Use multiple sine waves of different frequencies for more natural look
		val := baseAmplitude * math.Sin(pos*math.Pi*frequencyFactor*8)
		val += (baseAmplitude / 2) * math.Sin(pos*math.Pi*frequencyFactor*16)

		// Add some randomness to make it look more natural
		val += (rand.Float64() - 0.5) * 15

		// Add some fade-in and fade-out effects
		fadeInOut := math.Sin(pos * math.Pi)
		val = val * (0.7 + 0.3*fadeInOut)

		// Center around 50 (typical voice baseline)
		val = val + 50

		// Ensure values stay within WhatsApp's expected range (0-100)
		if val < 0 {
			val = 0
		} else if val > 100 {
			val = 100
		}

		waveform[i] = byte(val)
	}

	return waveform
}
