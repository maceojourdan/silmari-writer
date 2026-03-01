# edit-content-by-voice-from-review-screen TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/330-edit-content-by-voice-from-review-screen.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- **Reachability**
- **TypeInvariant**
- **ErrorConsistency**

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/330-edit-content-by-voice-from-review-screen.md
```

Verifier output:

- Result: **ALL PROPERTIES PASSED**
- States: 22 found, 11 distinct
- Exit code: 0
- TLA+ spec: `frontend/artifacts/tlaplus/330-edit-content-by-voice-from-review-screen/EditContentByVoiceFromReviewScreen.tla`

This TDD plan mirrors those three properties at code level.

---

## Tech Stack (Gate 2 – Option 1)

- **Frontend**: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- **Backend**: Next.js API Routes, TypeScript, Zod
- **Database**: Supabase (Postgres)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-v3n6 | module | `frontend/modules/review/ReviewModule.tsx` |
| ui-w8p2 | component | `frontend/components/review/EditByVoiceComponent.tsx` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/editByVoice.ts` |
| api-m5g7 | endpoint | `app/api/edit-by-voice/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/EditByVoiceRequestHandler.ts` |
| db-h2s4 | service | `backend/services/EditByVoiceService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/ContentDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Content.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/EditByVoiceErrors.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

---

# Step 1: Capture voice instruction from review screen ✅

**From path spec:**
- Input: User action via ui-w8p2 within ui-v3n6
- Process: Activate voice capture → convert speech to text → associate with content ID
- Output: Structured voice instruction text linked to current content ID
- Error: If audio capture/transcription fails, display shared error and allow retry up to 3 times

---

## Test (`frontend/components/review/__tests__/EditByVoiceComponent.test.tsx`)

**Reachability**
- Render `ReviewModule` with `contentId="c1"`
- Click "Edit by Voice"
- Mock successful transcription → assert structured payload `{ contentId: "c1", instructionText: string }`

**TypeInvariant**
- Assert payload matches TypeScript interface:
  ```ts
  type EditByVoicePayload = {
    contentId: string;
    instructionText: string;
  }
  ```

**ErrorConsistency**
- Mock microphone/transcription failure
- Assert error from `SharedErrors.VOICE_CAPTURE_FAILED`
- Assert retry counter increments
- After 3 failures → blocking error displayed, retry disabled

---

## Implementation

- Build `EditByVoiceComponent`:
  - Local state: `isRecording`, `retryCount`, `error`
  - Function `handleVoiceCapture()` returns `EditByVoicePayload`
  - Integrate mock ElevenLabs transcription client
- Use `SharedErrors.VOICE_CAPTURE_FAILED`
- Enforce max 3 retries

---

# Step 2: Send voice edit request to backend ✅

**From path spec:**
- Input: Voice instruction payload via api-q7v1
- Process: Typed API contract submits request
- Output: HTTP request delivered to api-m5g7
- Error: Network/validation failure → shared error, original content unchanged

---

## Test (`frontend/api_contracts/__tests__/editByVoice.test.ts`)

**Reachability**
- Call `editByVoice(payload)` with valid payload
- Assert `fetch` called with `/api/edit-by-voice`

**TypeInvariant**
- Validate payload via Zod schema before submission
- Assert response type:
  ```ts
  type EditByVoiceResponse = { updatedContent: Content }
  ```

**ErrorConsistency**
- Mock network failure → assert `SharedErrors.NETWORK_ERROR`
- Assert UI state preserves original content

---

## Implementation

- `frontend/api_contracts/editByVoice.ts`
  - Zod schema validation
  - `fetch('/api/edit-by-voice', { method: 'POST' })`
- Return typed response
- Surface shared error codes

---

# Step 3: Process voice instruction and generate revised content ✅

**From path spec:**
- Input: Validated request via endpoint + handler → service
- Process: Interpret instruction, apply modifications
- Output: Revised content entity
- Error: Semantic invalid → db-l1c3 structured error

---

## Test (`backend/services/__tests__/EditByVoiceService.test.ts`)

**Reachability**
- Provide existing `Content` + valid instruction
- Assert revised `Content` returned

**TypeInvariant**
- Assert returned object conforms to `Content` type

**ErrorConsistency**
- Provide semantically invalid instruction
- Assert `EditByVoiceErrors.INVALID_INSTRUCTION`
- Assert DAO `update()` not called

---

## Implementation

- `EditByVoiceService.ts`
  - Fetch existing content via DAO
  - Apply deterministic transformation (stub LLM)
  - Throw `INVALID_INSTRUCTION` if parse fails

---

# Step 4: Persist revised content ✅

**From path spec:**
- Input: Revised content entity
- Process: DAO updates db-f8n5 record
- Output: Persisted updated content record
- Error: DB update fails → log + persistence error

---

## Test (`backend/data_access_objects/__tests__/ContentDAO.test.ts`)

**Reachability**
- Call `update(content)` → assert record stored in test DB

**TypeInvariant**
- Assert stored row matches `Content` schema

**ErrorConsistency**
- Mock DB failure
- Assert:
  - `backend_logging.error()` called
  - `EditByVoiceErrors.PERSISTENCE_FAILURE` returned

---

## Implementation

- `ContentDAO.ts`
  - `update(content: Content): Promise<Content>`
  - Use Supabase client
- Wrap DB errors → structured error
- Log via `backend/logging`

---

# Step 5: Return updated content to review screen ✅

**From path spec:**
- Input: Persisted content → endpoint → frontend contract
- Process: Bind to component state
- Output: Review screen re-renders updated content
- Error: Frontend response mapping fails → log + recoverable error

---

## Test (`frontend/modules/review/__tests__/ReviewModule.integration.test.tsx`)

**Reachability**
- Mock full backend response
- Trigger voice edit
- Assert updated content rendered

**TypeInvariant**
- Assert component state matches `Content` type

**ErrorConsistency**
- Mock malformed backend response
- Assert:
  - `frontend_logging.error()` called
  - Error message displayed
  - Previous content preserved

---

## Implementation

- `app/api/edit-by-voice/route.ts`
  - POST handler → request handler → service
- `EditByVoiceRequestHandler.ts`
  - Validate input (Zod)
  - Map service result to HTTP JSON
- Frontend state update inside `ReviewModule`

---

# Terminal Condition ✅

## Integration Test (`e2e/edit-by-voice.spec.ts` – Playwright)

- Given review screen with draft content
- When user selects "Edit by Voice" and provides valid instruction
- Then:
  - Backend processes + persists content
  - Review screen displays updated content
  - No error state present

Asserts full path reachability from trigger → terminal condition.

---

# References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/330-edit-content-by-voice-from-review-screen.md`
- TLA+: `frontend/artifacts/tlaplus/330-edit-content-by-voice-from-review-screen/EditContentByVoiceFromReviewScreen.tla`
- Gate 2 Tech Stack: Option 1 – Fastest Path
