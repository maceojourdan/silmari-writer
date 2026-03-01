# prevent-edit-of-locked-answer TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/337-prevent-edit-of-locked-answer.md

---

## Verification (Phase 0)
The TLA+ model for this path passed: **Reachability, TypeInvariant, ErrorConsistency**.

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/337-prevent-edit-of-locked-answer.md
```

Result:
- Result: **ALL PROPERTIES PASSED**
- States: 22 found, 11 distinct
- Exit code: 0

This plan translates those three verified properties into executable tests per step.

---

## Tech Stack (Gate 2)
- Frontend: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- Backend: Next.js API Routes (Node.js, TypeScript), Zod
- Database: Supabase (Postgres)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/AnswerEditor.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/answerUpdateVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/updateAnswer.ts` |
| api-m5g7 | endpoint | `frontend/app/api/answers/[id]/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/UpdateAnswerRequestHandler.ts` |
| db-h2s4 | service | `backend/services/AnswerService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/AnswerDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Answer.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/AnswerErrors.ts` |

---

## Step 1: User submits edit request

**From path spec:**
- Input: User interaction in ui-w8p2 containing updated answer content and answer identifier
- Process: Component captures edit action and prepares API request via api-q7v1
- Output: Structured update request sent to backend endpoint
- Error: If required fields missing, ui-a4y1 blocks submission and displays validation errors

### Test (`frontend/components/__tests__/AnswerEditor.test.tsx`)

**Reachability**
- Render `AnswerEditor` with valid `answerId` and initial content
- Simulate user editing content and clicking “Save”
- Assert `updateAnswer()` (api-q7v1) called with `{ id, content }`

**TypeInvariant**
- Assert request matches Zod schema in `updateAnswer.ts`
- Ensure `id: string`, `content: string`

**ErrorConsistency**
- Leave content empty
- Click “Save”
- Assert verifier blocks submission
- Assert validation message rendered
- Assert API contract NOT called

### Implementation

- `answerUpdateVerifier.ts`: Zod schema requiring non-empty `id` and `content`
- `updateAnswer.ts`: typed function `updateAnswer(input: UpdateAnswerRequest)`
- `AnswerEditor.tsx`: 
  - On submit → run verifier
  - If valid → call API contract
  - If invalid → set local error state

---

## Step 2: Endpoint receives update request

**From path spec:**
- Input: HTTP update request handled by api-m5g7 and routed via api-n8k2
- Process: Validate structure and forward to service layer
- Output: Service-level update command
- Error: Malformed/unauthorized → error from db-l1c3

### Test (`frontend/app/api/answers/[id]/__tests__/route.test.ts`)

**Reachability**
- Send valid PUT request with `{ content }`
- Assert `UpdateAnswerRequestHandler.handle()` called
- Assert 200 or service result passed through

**TypeInvariant**
- Invalid body (missing content)
- Assert 400 with structured error shape `{ code, message }`

**ErrorConsistency**
- Simulate unauthorized request (mock auth failure)
- Assert response contains error from `AnswerErrors.UNAUTHORIZED`

### Implementation

- `AnswerErrors.ts`: define
  - `LOCKED_ANSWER_MODIFICATION_FORBIDDEN`
  - `ANSWER_NOT_FOUND`
  - `PERSISTENCE_ERROR`
  - `UNAUTHORIZED`
- `route.ts`: 
  - Parse JSON
  - Validate via Zod
  - Call request handler
  - Map thrown domain errors → HTTP responses

---

## Step 3: Service checks lock status

**From path spec:**
- Input: Update command with answer ID; retrieve via DAO from data_structure
- Process: Verify finalized/locked flag
- Output: Determination that answer is locked
- Error: Not found → ANSWER_NOT_FOUND; retrieval fail → PERSISTENCE_ERROR

### Test (`backend/services/__tests__/AnswerService.test.ts`)

**Reachability**
- Mock DAO returning `{ id, content, locked: true }`
- Call `updateAnswer()`
- Assert service detects locked state

**TypeInvariant**
- Ensure DAO returns `Answer` type
- Assert service accepts `UpdateAnswerCommand` and returns domain result or throws typed error

**ErrorConsistency**
- DAO returns null → expect `ANSWER_NOT_FOUND`
- DAO throws DB error → expect `PERSISTENCE_ERROR`

### Implementation

- `Answer.ts`: 
  ```ts
  export interface Answer {
    id: string;
    content: string;
    locked: boolean; // finalized/locked
  }
  ```
- `AnswerDAO.ts`: `findById(id)` and `updateContent(id, content)`
- `AnswerService.ts`:
  - Retrieve answer
  - If null → throw ANSWER_NOT_FOUND
  - If locked → throw LOCKED_ANSWER_MODIFICATION_FORBIDDEN
  - Otherwise proceed (not used in this path)

---

## Step 4: Reject update due to locked status

**From path spec:**
- Input: Locked status confirmation
- Process: Abort update and generate domain error
- Output: Error response with locked-answer error code
- Error: Define LOCKED_ANSWER_MODIFICATION_FORBIDDEN if absent

### Test (Service-level)

**Reachability**
- DAO returns locked answer
- Expect thrown error with code `LOCKED_ANSWER_MODIFICATION_FORBIDDEN`

**TypeInvariant**
- Error object matches shape:
  ```ts
  { code: string; message: string }
  ```

**ErrorConsistency**
- Ensure DAO `updateContent` is NOT called

### Implementation

- Add to `AnswerErrors.ts`:
  ```ts
  export const LOCKED_ANSWER_MODIFICATION_FORBIDDEN = {
    code: "LOCKED_ANSWER_MODIFICATION_FORBIDDEN",
    message: "This answer has been finalized and cannot be modified."
  };
  ```
- Throw this error from service when `locked === true`

---

## Step 5: Frontend displays locked message

**From path spec:**
- Input: Error response via api-q7v1
- Process: Interpret locked error code and display notification
- Output: Visible locked message; no content change
- Error: Unknown error → generic message

### Test (`frontend/components/__tests__/AnswerEditor.locked.test.tsx`)

**Reachability**
- Mock API contract to reject with `LOCKED_ANSWER_MODIFICATION_FORBIDDEN`
- Submit valid edit
- Assert locked message displayed

**TypeInvariant**
- Assert error response matches contract type

**ErrorConsistency**
- Mock API with unknown error code
- Assert generic error shown
- Assert original content remains unchanged

### Implementation

- In `AnswerEditor.tsx`:
  - Catch API errors
  - If `error.code === LOCKED_ANSWER_MODIFICATION_FORBIDDEN.code`
    → show locked message
  - Else → show generic error
  - Do not mutate local content state on error

---

## Terminal Condition

### Integration Test (`tests/integration/preventEditLockedAnswer.test.ts`)

- Seed DB with `Answer { locked: true }`
- Render editor
- Attempt edit
- Assert:
  - HTTP response contains `LOCKED_ANSWER_MODIFICATION_FORBIDDEN`
  - UI shows locked message
  - DB content unchanged

This proves:
- Reachability: Full trigger → UI error path is exercisable
- TypeInvariant: Types consistent across UI → API → service → DAO
- ErrorConsistency: Locked branch always results in correct domain + UI error state

---

## References
- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/337-prevent-edit-of-locked-answer.md
- Gate 1: F-FINALIZE-EXPORT (acceptance criterion 6)
- TLA+ artifacts: frontend/artifacts/tlaplus/337-prevent-edit-of-locked-answer/
