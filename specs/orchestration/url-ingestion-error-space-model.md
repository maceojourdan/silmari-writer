# PATH: url-ingestion-error-space-model

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 2
**Source:** Extracted from existing code — InitializeSessionDAO.ts, GetSessionHandler.ts, SessionView.ts, ChannelIngestionPipelineAdapter.ts, sessions/[id]/route.ts, ingestion/url/route.ts

## Purpose

Behavioral model of the URL ingestion → session persistence → session page load error space. Version 1 captured the buggy baseline (5 violated invariants). Version 2 extends the model with the fixed behavior — each fix is modeled as an alternative transition gated by `mode = "fixed"`, allowing formal verification that all invariants hold after the changes.

The TLA+ spec (`UrlIngestionErrorSpace.tla`) is parameterized by a `mode` constant: `"buggy"` enables only current-code transitions, `"fixed"` enables only corrected transitions. Both can be verified independently.

## Trigger

User submits a URL via `POST /api/ingestion/url` (direct paste path) or via email/SMS channel adapter.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `api-e5f6` | channel_router | Normalizes inbound URL into ingestion request |
| `api-n8k2` | request_handler | Validates URL and coordinates session creation |
| `db-h2s4` | initialize_session_service | Validates objects, checks uniqueness, delegates persist |
| `db-d3w8` | initialize_session_dao | Persists session row to Supabase sessions table |
| `db-g9p1` | get_session_handler | Maps DB row to SessionView for page load |
| `cfg-v2t5` | session_view_schema | Zod schema validating SessionView response contract |
| `db-k4m7` | session_dao | Reads session rows and maps DB columns to domain objects |

## Steps

1. **Receive and validate URL submission**
   - Input: HTTP POST with `{ sourceUrl }` and auth header at `api-e5f6`.
   - Process: Authenticate via `AuthAndValidationFilter`. Parse JSON body. Validate against `StartSessionFromUrlRequestSchema`. Extract canonical URL via `ChannelIngestionService.extractCanonicalUrl()`.
   - Output: Validated `{ userId, sourceUrl, channel: 'direct' }` forwarded to `ChannelIngestionPipelineAdapter`.
   - Error: Invalid JSON → `VoiceUxError(INVALID_REQUEST, 400)`. Invalid URL → Zod validation error → `VoiceUxError(INVALID_REQUEST, 400)`. Auth failure → `VoiceUxError(401)`.

2. **Check active session uniqueness**
   - Input: Pipeline adapter calls `InitializeSessionService.createSession()` which calls `InitializeSessionDAO.getActiveSession()` at `db-d3w8`.
   - Process: BUGGY — query `sessions` for `state = 'initialized'` globally, matches any user. FIXED (Fix 3 + Fix 4) — query with `user_id = :currentUser`; if found and stale, supersede via step 2b; if found and fresh, throw `SESSION_ALREADY_ACTIVE`; if not found or different user, proceed.
   - Output: `null` → proceed to step 3. Non-null stale → step 2b. Non-null fresh own → error.
   - Error: BUGGY — any initialized session blocks all users (409). FIXED — only current user's fresh session blocks. DB failure → `SessionErrors.PersistenceFailure()` (500, retryable).

3. **Finalize stale zombie session (Fix 4 — new sub-step)**
   - Input: Stale initialized session identified in step 2 (fixed mode only).
   - Process: Transition the stale session to `ended` state via `SessionDAO.updateState(zombieId, 'ended')`. Clears uniqueness constraint for current user.
   - Output: Zombie session no longer active. Proceed to step 4 (persist new session).
   - Error: DB update failure → `SessionErrors.PersistenceFailure()` (500). User can retry — zombie is still stale.

4. **Persist session to database**
   - Input: Validated `{ resume, job, question, state: 'initialized', createdAt }` at `db-d3w8`.
   - Process: BUGGY — insert without `updated_at`, DB has no DEFAULT/trigger, result is NULL. FIXED (Fix 1) — insert with `updated_at: session.createdAt`. FIXED (Fix 3) — insert with `user_id: input.userId`.
   - Output: BUGGY — `InitializedSession` with `updated_at = NULL`. FIXED — `InitializedSession` with `updated_at` non-null.
   - Error: DB insert failure → `SessionErrors.PersistenceFailure()` (500).

5. **Return success response to client**
   - Input: Persisted session from step 4, wrapped by `ChannelIngestionPipelineAdapter` into `{ id, state: 'initialized', contextSummary }`.
   - Process: Route validates response against `StartSessionFromUrlResponseSchema`. Returns 200 JSON.
   - Output: Client receives `{ sessionId, state, canonicalUrl, contextSummary }`. Frontend navigates to `/session/[sessionId]`.
   - Error: Response schema validation failure → `VoiceUxError(INTERNAL_ERROR, 500)`.

6. **Load session page**
   - Input: `GET /api/sessions/[id]` with the session UUID from step 5.
   - Process: `GetSessionHandler.handle()` calls `SessionDAO.findById()`. `mapSession()` casts `data.updated_at as string`. BUGGY — no null guard, produces null typed as string. FIXED — `updated_at` always non-null (Fix 1) plus `data.updated_at ?? data.created_at` as defense.
   - Output: SessionView object with `updatedAt` field.
   - Error: None at this step — null propagates silently in buggy version.

7. **Validate session view response**
   - Input: SessionView object from step 6 at `cfg-v2t5`.
   - Process: BUGGY — `SessionViewSchema` requires `updatedAt: z.string()`, receives null, Zod fails. FIXED (Fix 2) — `updatedAt: z.string().nullable()` accepts null as defense-in-depth; Fix 1 ensures null never arrives here.
   - Output: BUGGY — never reached for fresh sessions. FIXED — valid SessionView returned, session page renders.
   - Error: BUGGY — schema validation failure → 500, session page shows error. FIXED — no schema failure possible.

8. **User retry — recovery or blocked**
   - Input: User resubmits URL after step 7 error.
   - Process: BUGGY — re-enters step 2, `getActiveSession()` finds zombie, throws `SESSION_ALREADY_ACTIVE` (409, not retryable), system permanently blocked. FIXED — re-enters step 1, zombie is now stale, step 2 detects staleness, step 3 supersedes, new session created, system recovers.
   - Output: BUGGY — never reached. FIXED — user reaches step 7 → done.
   - Error: BUGGY — permanent block. FIXED — only if DB fails in step 3, retryable.

## Terminal Condition

**Fixed happy path:** User sees session page with valid SessionView, proceeds to voice interrogation. Reachable for all fresh sessions.

**Fixed recovery path:** After any transient error, user retries and stale zombie is superseded. System always returns to operational state.

**Buggy terminal:** User sees error on session page. Retry produces 409. System blocked until manual DB intervention.

## Feedback Loops

**Buggy retry loop (livelock):** User retry → step 2 → SESSION_ALREADY_ACTIVE → no progress. System accepts retry but always rejects it.

**Fixed retry loop (convergent):** User retry → step 2 → zombie is stale → step 2b supersedes → step 3 creates new session → done. Bounded: converges in exactly one retry after staleness threshold.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle | Buggy | Fixed |
|----|-----------|--------|---------------|-------------|-------|-------|
| INV-1 | Every persisted session must be loadable via `GET /session/[id]` | UX contract (spec:42-43) | Reachability | `getSession(id)` returns valid `SessionView` after `initializeFromUrl()` succeeds | **VIOLATED** | HOLDS |
| INV-2 | `updated_at` must be non-null for any persisted session row | Schema integrity | TypeInvariant | `SELECT updated_at FROM sessions WHERE id = ?` returns non-null timestamp | **VIOLATED** | HOLDS |
| INV-3 | Active session uniqueness check must be user-scoped | Multi-user safety | TypeInvariant | `getActiveSession(userA)` does not return `userB`'s session | **VIOLATED** | HOLDS |
| INV-4 | No terminal error state may leave a zombie session that blocks future operations | Liveness | Reachability | After any error, either cleanup occurs or next `initializeFromUrl()` succeeds within one retry | **VIOLATED** | HOLDS |
| INV-5 | Error responses must not produce inconsistent system state (success-on-write + fail-on-read) | Safety | ErrorConsistency | If persist succeeds, all downstream reads of that entity also succeed | **VIOLATED** | HOLDS |
| INV-6 | All ingestion attempts emit at least one observability event | Observability (spec:173-186) | Reachability | `ingestion_url_submitted` or error event exists for every POST | Untested | Untested |

## Fix-to-Invariant Mapping

| Fix | Description | File:Line | Invariants Resolved | TLA+ Transition |
|-----|-------------|-----------|---------------------|-----------------|
| Fix 1 | Set `updated_at = createdAt` in insert payload | `InitializeSessionDAO.ts:86` | INV-1, INV-2, INV-5 | `Step3_Persist_Fixed` |
| Fix 2 | `updatedAt: z.string().nullable()` | `SessionView.ts:13` | INV-1 (defense-in-depth) | `Step6_Fixed_SchemaAcceptsNull` |
| Fix 3 | Add `user_id` to sessions table + scope `getActiveSession()` query | `InitializeSessionDAO.ts:42` + migration | INV-3 | `Step2_Fixed_NoActiveForUser` |
| Fix 4 | Supersede stale initialized sessions on retry | `InitializeSessionService.ts:109` | INV-4 | `Step2_Fixed_SupersedeStaleZombie` + `Step2b_FinalizeStaleZombie` |

## Change Impact Analysis

### Fix 1: Set `updated_at` at insert time (root cause — immediate)
- **Affected step:** 3
- **Files:** `InitializeSessionDAO.ts:86-91` — add `updated_at: session.createdAt` to insert payload
- **Risk:** Low. Additive. No code depends on `updated_at` being null.
- **Alternative:** `ALTER TABLE sessions ALTER COLUMN updated_at SET DEFAULT now()` — more robust, requires migration.
- **Test oracle:** After `persist()`, `SELECT updated_at FROM sessions WHERE id = ?` is non-null.

### Fix 2: Make `updatedAt` nullable in SessionViewSchema (defense-in-depth)
- **Affected step:** 6
- **Files:** `SessionView.ts:13` — change `z.string()` to `z.string().nullable()`
- **Risk:** Low. Frontend already handles nullable fields elsewhere.
- **Test oracle:** `SessionViewSchema.safeParse({ ..., updatedAt: null })` succeeds.

### Fix 3: Scope active session check to user
- **Affected step:** 2
- **Files:**
  - New migration: add `user_id uuid REFERENCES auth.users(id)` to `sessions` table
  - `InitializeSessionDAO.ts:42` — add `.eq('user_id', userId)`
  - `InitializeSessionDAO.ts:86` — add `user_id: userId` to insert
  - `InitializeSessionService.ts:109` — pass `userId` to `getActiveSession()`
  - `ChannelIngestionPipelineAdapter.ts:26` — pass `userId` through to `createSession()`
- **Risk:** Medium. Schema migration + 4 file changes + test updates.
- **Test oracle:** With user_a's session active, user_b's `initializeFromUrl()` succeeds.

### Fix 4: Supersede stale initialized sessions
- **Affected step:** 2 (new sub-step 2b)
- **Files:**
  - `InitializeSessionService.ts:109` — check `created_at` age before rejecting
  - `SessionDAO.ts` (or new method) — `updateState(zombieId, 'ended')`
  - Config: staleness threshold constant (e.g., 30 minutes)
- **Risk:** Medium. Must not supersede sessions that are legitimately being used.
- **Test oracle:** Session older than threshold → superseded on next `initializeFromUrl()`. Fresh session → still blocks.

### Recommended implementation order
1. **Fix 1** — immediate unblock, root cause, lowest risk
2. **Fix 2** — defense-in-depth, 1-line change
3. **Fix 4** — liveness recovery, prevents future zombie accumulation
4. **Fix 3** — multi-user correctness, requires migration
