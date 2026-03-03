# PATH: ingest-url-via-email-or-sms-channel

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from voice-assisted-session-ui-ux.md — sections 2, "Ingestion convenience", and "Ingestion observability requirements"

## Purpose

Covers the email-to-ingest and SMS-to-ingest ingestion channel flows that are missing from the existing session initialization paths. The existing path set (310, 312) handles URL paste and validation but assumes the URL arrives via direct paste. This path models the asynchronous channel where a user sends a URL by email or SMS, the system receives it, extracts the URL, and feeds it into the standard ingestion pipeline.

## Trigger

User sends a message (email or SMS) containing a job application URL to a system-provided inbox address or phone number.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `mq-a1b2` | email_receiver | Receives inbound email messages at the system-provided inbox address |
| `mq-c3d4` | sms_receiver | Receives inbound SMS messages at the system-provided phone number |
| `api-e5f6` | channel_router | Normalizes inbound messages from email or SMS into a common ingestion request |
| `api-n8k2` | request_handler | Validates the extracted URL and coordinates session creation (shared with existing paths) |
| `db-h2s4` | service | Constructs the session entity from ingested URL context (shared with existing paths) |
| `db-d3w8` | data_access_object | Persists the session entity to the database (shared with existing paths) |
| `db-l1c3` | backend_error_definitions | Defines standardized error types for channel and parsing failures |
| `cfg-g7h8` | url_extractor | Parses message body to extract and validate the target URL |
| `cfg-r3d7` | frontend_logging | Logs ingestion channel events for observability |

## Steps

1. **Receive inbound message**
   - Input: Inbound email at mq-a1b2 (email_receiver) or inbound SMS at mq-c3d4 (sms_receiver) containing a URL and optional sender context.
   - Process: The receiver accepts the message and extracts metadata: sender identity, channel type (email or sms), message body, and received timestamp.
   - Output: Raw inbound message with channel metadata forwarded to api-e5f6 (channel_router).
   - Error: If the inbound message is unparseable or the sender cannot be identified, log the failure via cfg-r3d7 (frontend_logging) and emit `ingestion_parse_failed` event with `channel` and `error_code`.

2. **Resolve sender to user account**
   - Input: Sender identity (email address or phone number) and channel metadata from api-e5f6 (channel_router).
   - Process: Look up the sender identity against registered user accounts. Match email address for email channel, phone number for SMS channel. If no match, check for pending onboarding invitations.
   - Output: Resolved user_id and session context for the sender.
   - Error: If the sender cannot be matched to any user account, send a reply on the same channel indicating the account is not recognized and log via cfg-r3d7. No session is created.

3. **Extract and validate URL from message body**
   - Input: Message body from api-e5f6 (channel_router), forwarded to cfg-g7h8 (url_extractor).
   - Process: Parse the message body to extract URLs. Apply validation: URL must be reachable, must match known job application domain patterns, and must not be a duplicate of an already-ingested URL for this user.
   - Output: Validated target URL with `source_domain` metadata, ready for ingestion. Emit `ingestion_url_submitted` event with `channel=email|sms`.
   - Error: If no valid URL is found, or the URL is unreachable, or it matches a duplicate, send an error reply on the same channel explaining the issue. Emit `ingestion_parse_failed` with `error_code`.

4. **Feed URL into standard ingestion pipeline**
   - Input: Validated target URL and resolved user_id, forwarded from api-e5f6 (channel_router) to api-n8k2 (request_handler).
   - Process: Construct a session initialization request equivalent to a URL paste, containing the extracted URL and user context. The request handler validates and processes using the same logic as path 310 (initialize-new-session-with-provided-objects).
   - Output: Ingested context (question prompts, role expectations, related signals) extracted from the URL. Emit `ingestion_parse_succeeded` and `ingestion_context_ready` events with `time_to_context_ready_ms`.
   - Error: If context extraction fails, emit `ingestion_parse_failed` and send a reply on the originating channel explaining that the URL could not be processed. Log via db-l1c3 (backend_error_definitions).

5. **Notify user of successful ingestion**
   - Input: Successfully ingested context and session identifier from db-h2s4 (service).
   - Process: Send a confirmation reply on the originating channel (email reply or SMS reply) containing a deep link to the session in the app. Include a brief summary of the detected question context.
   - Output: User receives confirmation with a link to continue in the app.
   - Error: If notification delivery fails, log the failure but do not block the session — the user can still find it in the app.

## Terminal Condition

User receives a reply on the originating channel (email or SMS) confirming that the URL has been ingested, with a deep link to the session. The session is in "initialized" state with extracted context, identical to a paste-ingested session.

## Feedback Loops

None — strictly linear. Retry semantics are handled at the message queue level (redelivery on transient failures), not within this path.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | Every inbound message resolves to exactly one channel type (email or sms) | spec:37-39 | TypeInvariant | channel_type is always "email" or "sms", never null |
| INV-2 | Unrecognized senders never create sessions | spec:37 | Reachability | No session record exists when sender lookup fails |
| INV-3 | Ingested sessions via email/SMS are identical in state to paste-ingested sessions | spec:34-40 | TypeInvariant | Session entity schema and state match regardless of channel |
| INV-4 | Every ingestion attempt emits at least one observability event | spec:173-186 | Reachability | `ingestion_url_submitted` or `ingestion_parse_failed` event exists for every inbound message |
| INV-5 | Duplicate URLs for the same user are rejected | spec:34 | ErrorConsistency | Duplicate URL produces rejection reply, no new session |
