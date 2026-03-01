# initiate-voice-assisted-answer-session TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/306-initiate-voice-assisted-answer-session.md`

Tech Stack (Gate 2 – Option 1):
- Frontend: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- Backend: Next.js API Routes, TypeScript, Zod
- Database: Supabase (PostgreSQL)

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/306-initiate-voice-assisted-answer-session.md`

Stdout excerpt:

- Result: ALL PROPERTIES PASSED  
- States: 30 found, 15 distinct  
- Exit code: 0  
- TLA+ spec: `frontend/artifacts/tlaplus/306-initiate-voice-assisted-answer-session/InitiateVoiceAssistedAnswerSession.tla`

This TDD plan reproduces those three properties at the code level.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-v3n6 | module | `frontend/modules/session/StartVoiceSessionModule.tsx` |
| ui-x1r9 | access_control | `frontend/access_controls/RequireAuth.tsx` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/createSession.ts` |
| api-m5g7 | endpoint | `app/api/sessions/route.ts` (POST) |
| api-p3e6 | filter | `backend/filters/AuthFilter.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/CreateSessionHandler.ts` |
| db-h2s4 | service | `backend/services/SessionInitializationService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/SessionDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/AnswerSession.ts`, `StoryRecord.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/SessionErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/HttpErrors.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/logger.ts` |

---

## Step 1: User initiates voice session ✅

**From path spec:**
- Input: User interaction in `ui-v3n6` while authenticated under `ui-x1r9`
- Process: Validate authentication and trigger request via `api-q7v1`
- Output: Typed API request to create session
- Error: If not authenticated → redirect to login; no request sent

### Test (`frontend/modules/session/StartVoiceSessionModule.test.tsx`)

- Reachability:
  - Mock authenticated user context
  - Click “Start Voice-Assisted Session”
  - Assert `createSession()` from `api-q7v1` called once
- TypeInvariant:
  - Assert request matches `CreateSessionRequest` Zod schema
- ErrorConsistency:
  - Mock unauthenticated context
  - Click button
  - Assert redirect to `/login`
  - Assert `createSession()` NOT called

### Implementation (`frontend/modules/session/StartVoiceSessionModule.tsx`)

- Wrap in `<RequireAuth>`
- On click:
  - If no user → router.push('/login')
  - Else call `createSession()` typed function
- Use Zod schema from API contract

---

## Step 2: API endpoint receives session creation request ✅

**From path spec:**
- Input: HTTP POST via `api-m5g7` with `api-p3e6` active
- Process: Validate authentication context and forward to handler
- Output: Validated command to request handler
- Error: If auth fails → authorization error from `cfg-j9w2`

### Test (`app/api/sessions/route.test.ts`)

- Reachability:
  - Mock valid auth header
  - POST request
  - Assert `CreateSessionHandler.handle()` called
- TypeInvariant:
  - Assert parsed body conforms to `CreateSessionRequest`
- ErrorConsistency:
  - No/invalid auth header
  - Assert 401 response with `AUTHORIZATION_ERROR` from `HttpErrors`

### Implementation (`app/api/sessions/route.ts`)

- Apply `AuthFilter`
- Validate body with Zod
- Forward to `CreateSessionHandler`
- Catch auth errors → map to `HttpErrors.authorization`

---

## Step 3: Request handler invokes session initialization logic ✅

**From path spec:**
- Input: Validated command
- Process: Delegate to `SessionInitializationService`
- Output: Service call with user context
- Error: Missing/malformed params → validation error (`cfg-j9w2`)

### Test (`backend/request_handlers/CreateSessionHandler.test.ts`)

- Reachability:
  - Provide valid command
  - Assert service `initializeSession(userId)` called
- TypeInvariant:
  - Assert service return type matches `SessionInitializationResult`
- ErrorConsistency:
  - Provide malformed command
  - Assert `VALIDATION_ERROR` from `HttpErrors`

### Implementation (`backend/request_handlers/CreateSessionHandler.ts`)

- Validate with Zod schema
- Extract `userId` from auth context
- Call `SessionInitializationService.initializeSession`

---

## Step 4: Service creates Answer Session in INIT state ✅

**From path spec:**
- Input: Initialization request
- Process: Construct AnswerSession with state INIT and persist via DAO
- Output: Persisted AnswerSession (INIT)
- Error: DAO raises storage error (`db-l1c3`)

### Test (`backend/services/SessionInitializationService.session.test.ts`)

- Reachability:
  - Mock DAO success
  - Assert returned session.state === 'INIT'
- TypeInvariant:
  - Assert persisted object matches `AnswerSession` schema
- ErrorConsistency:
  - Mock DAO throw `StorageError`
  - Assert propagated `SESSION_PERSISTENCE_ERROR`

### Implementation

- Define `AnswerSession` schema (`id`, `userId`, `state: 'INIT'`, timestamps)
- DAO `createSession()` using Supabase client
- Wrap and rethrow as `SessionErrors.PersistenceError`

---

## Step 5: Service creates corresponding StoryRecord in INIT status ✅

**From path spec:**
- Input: Persisted AnswerSession
- Process: Create StoryRecord with status INIT and persist
- Output: Persisted StoryRecord linked to session
- Error: On failure → backend error; mark session creation failed (transactional rollback proposed)

### Test (`backend/services/SessionInitializationService.story.test.ts`)

- Reachability:
  - Mock DAO createSession + createStory success
  - Assert story.status === 'INIT'
  - Assert story.sessionId === session.id
- TypeInvariant:
  - Assert StoryRecord matches schema
- ErrorConsistency:
  - Mock story creation failure
  - Assert:
    - Error `STORY_PERSISTENCE_ERROR`
    - Session insert rolled back (no session in DB)

### Implementation

- Define `StoryRecord` schema (`id`, `sessionId`, `status: 'INIT'`)
- Use Supabase transaction (or simulated transaction wrapper)
- If story creation fails → rollback session creation

---

## Step 6: Return session initialization response to frontend ✅

**From path spec:**
- Input: Persisted session + story
- Process: Service returns metadata → handler formats HTTP response
- Output: 200 response with session identifier and INIT state
- Error: Response transformation fails → internal error (`cfg-j9w2`)

### Test (`app/api/sessions/route.response.test.ts`)

- Reachability:
  - Mock service returning session + story
  - Assert HTTP 200
  - Body contains `{ sessionId, state: 'INIT' }`
- TypeInvariant:
  - Validate response against `CreateSessionResponse` schema
- ErrorConsistency:
  - Mock transformation throw
  - Assert 500 with `INTERNAL_ERROR`

### Implementation

- Map service result → response DTO
- Validate response via Zod before returning
- Catch errors → map to `HttpErrors.internal`

---

## Step 7: Frontend renders voice-assisted session interface ✅

**From path spec:**
- Input: Successful session creation response
- Process: Update UI state and navigate/render interface
- Output: Visible voice-assisted interface with session INIT
- Error: If UI update fails → log via `cfg-r3d7` and show user-facing error

### Test (`frontend/modules/session/VoiceSessionRender.test.tsx`)

- Reachability:
  - Mock successful API response
  - Assert navigation to `/session/[id]`
  - Assert UI displays state “INIT”
- TypeInvariant:
  - Assert session state in React context equals 'INIT'
- ErrorConsistency:
  - Mock state update throw
  - Assert logger.error called
  - Assert error message visible to user

### Implementation

- On success → set session context `{ id, state: 'INIT' }`
- Route to session page
- Wrap state update in try/catch → log via `logger.error`

---

## Terminal Condition ✅

### Integration Test (`tests/integration/initiateVoiceSession.test.ts`)

Exercise full path:

1. Render authenticated frontend
2. Click “Start Voice-Assisted Session”
3. Allow real API route + service + in-memory test DB
4. Assert:
   - HTTP 200
   - Session row exists with state INIT
   - StoryRecord row exists with status INIT
   - UI displays voice-assisted interface with INIT state

This proves:
- Reachability: Trigger → UI → API → Handler → Service → DAO → Response → UI
- TypeInvariant: All DTOs and DB entities validated via Zod schemas
- ErrorConsistency: Each failure branch returns defined error types

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/306-initiate-voice-assisted-answer-session.md`
- Gate 1: F-EPIC-SESSION (acceptance criterion #2)
- TLA+: `InitiateVoiceAssistedAnswerSession.tla`
