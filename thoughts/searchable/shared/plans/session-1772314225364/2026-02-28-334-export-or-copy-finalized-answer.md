# export-or-copy-finalized-answer TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/334-export-or-copy-finalized-answer.md

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/334-export-or-copy-finalized-answer.md
```

Stdout:
```
Path: export-or-copy-finalized-answer
TLA+ spec: .../ExportOrCopyFinalizedAnswer.tla
TLC config: .../ExportOrCopyFinalizedAnswer.cfg
Result: ALL PROPERTIES PASSED
States: 18 found, 9 distinct, depth 0
```

All three required properties were model-checked and satisfied.

---

## Tech Stack (Gate 2 – Option 1)

- Frontend: Next.js (App Router), React, TypeScript, Vitest + Testing Library
- Backend: Next.js API Routes, TypeScript, Zod
- Database: Supabase (Postgres)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-v3n6 | module | `frontend/modules/finalizedAnswer/FinalizedAnswerModule.tsx` |
| ui-w8p2 | component | `frontend/components/ExportCopyControls.tsx` |
| ui-y5t3 | data_loader | `frontend/data_loaders/loadFinalizedAnswer.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/exportFinalizedAnswer.ts` |
| api-m5g7 | endpoint | `frontend/app/api/answers/[id]/export/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/ExportFinalizedAnswerHandler.ts` |
| db-h2s4 | service | `backend/services/FinalizedAnswerExportService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/AnswerDAO.ts` |
| db-f8n5 | data_structure | `backend/data_structures/Answer.ts` |
| db-j6x9 | backend_verifier | `backend/verifiers/FinalizedAnswerVerifier.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/AnswerErrors.ts` |
| cfg-h5v9 | transformer | `shared/transformers/AnswerExportTransformer.ts` |
| cfg-f7s8 | data_type | `shared/data_types/ExportFormat.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/SharedErrors.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

---

## Step 1: Capture export or copy action

**From path spec:**
- Input: User interaction event from ui-w8p2 including answer ID and selected export format or copy action
- Process: Validate answer is finalized and locked in UI state and determine export vs copy
- Output: Validated export/copy request (answerId + format | copy flag)
- Error: If not finalized/locked, block and display error via cfg-j9w2

### Test (`frontend/components/__tests__/ExportCopyControls.test.tsx`)

- Reachability: Render component with finalized=true, locked=true; click “Export (markdown)” → assert handler called with `{ answerId, format: 'markdown' }`
- TypeInvariant: Assert emitted request satisfies `ExportFinalizedAnswerRequest` (TS type check + runtime Zod parse)
- ErrorConsistency: Render with finalized=false; click Export → assert shared error message from `SharedErrors.ANSWER_NOT_FINALIZED` is displayed

### Implementation

- Define `ExportFinalizedAnswerRequest` in `frontend/api_contracts/exportFinalizedAnswer.ts`
- Add UI state props: `{ answerId: string; finalized: boolean; locked: boolean }`
- On click:
  - If not finalized || not locked → set error from `SharedErrors`
  - Else build validated request object

---

## Step 2: Load finalized answer content

**From path spec:**
- Input: Validated request with answer ID via ui-y5t3 → api-q7v1 → api-m5g7
- Process: Route → handler → service → verifier → DAO → structure
- Output: Full finalized answer content (structured)
- Error: If not found or not locked → domain error from db-l1c3

### Test 2A (Backend happy path)
`backend/services/__tests__/FinalizedAnswerExportService.test.ts`

- Reachability: Call service with valid answerId; mock DAO to return Answer{ status: FINALIZED, locked: true }
- TypeInvariant: Assert returned object matches `Answer` type from `db-f8n5`
- ErrorConsistency: N/A (happy path)

### Test 2B (Backend error cases)

- DAO returns null → expect `AnswerErrors.ANSWER_NOT_FOUND`
- DAO returns status != FINALIZED or locked=false → expect `AnswerErrors.ANSWER_NOT_LOCKED`

### Test 2C (API route integration)
`frontend/app/api/answers/[id]/export/__tests__/route.test.ts`

- Reachability: HTTP GET `/api/answers/123/export` → 200 with structured content
- TypeInvariant: Response body matches Zod schema in `api-q7v1`
- ErrorConsistency: Not found → 404 with mapped shared error code

### Implementation

- `Answer` type with fields: `{ id, content, status, locked }`
- `FinalizedAnswerVerifier.ensureFinalizedLocked(answer)`
- `AnswerDAO.findById(id)` (Supabase query)
- `FinalizedAnswerExportService.getFinalizedAnswer(id)` orchestrates verifier + DAO
- API route calls handler → service and maps backend errors to HTTP + shared error

---

## Step 3: Transform content to selected export format

**From path spec:**
- Input: Structured finalized answer + selected format
- Process: Use cfg-h5v9 transformer + cfg-f7s8 serialization rules
- Output: Formatted export payload
- Error: Unsupported format → shared error

### Test (`shared/transformers/__tests__/AnswerExportTransformer.test.ts`)

- Reachability: Input Answer + format='markdown' → returns markdown string
- TypeInvariant: Output is string for text formats; matches `ExportFormat` enum
- ErrorConsistency: format='pdf' (unsupported) → throws `SharedErrors.UNSUPPORTED_EXPORT_FORMAT`

### Implementation

- `ExportFormat` enum: 'plain_text' | 'markdown'
- `AnswerExportTransformer.transform(answer, format)`
  - switch(format)
  - serialize accordingly
  - throw shared error if unsupported

---

## Step 4: Deliver export or copy result to user

**From path spec:**
- Input: Formatted export payload
- Process: If export → trigger file download; if copy → write to clipboard + update UI
- Output: Downloaded file OR success confirmation
- Error: If failure → shared error + log via cfg-r3d7

### Test (`frontend/components/__tests__/ExportCopyDelivery.test.tsx`)

- Reachability (export): Mock `URL.createObjectURL`; click Export → assert download link created and clicked
- Reachability (copy): Mock `navigator.clipboard.writeText`; click Copy → assert called with full content
- TypeInvariant: Clipboard receives string payload
- ErrorConsistency:
  - Mock clipboard rejection → UI shows shared error + logger called
  - Mock download failure → shared error displayed + logger called

### Implementation

- In `ExportCopyControls.tsx`:
  - If export → create Blob, temporary anchor, trigger click
  - If copy → await `navigator.clipboard.writeText`
  - catch errors → display `SharedErrors.EXPORT_FAILED` and log via `frontend/logging`

---

## Terminal Condition

### Integration Test
`frontend/modules/__tests__/exportOrCopyFinalizedAnswer.integration.test.tsx`

- Mock backend endpoint → returns structured finalized answer
- Render full module with finalized=true, locked=true
- Click Export (markdown)
- Assert:
  - API route invoked
  - Transformer applied
  - Download triggered
  - No error state present

Copy path:
- Click Copy
- Assert clipboard write success message shown

This proves:
- Reachability: Trigger → Step1 → Step2 → Step3 → Step4
- TypeInvariant: Types preserved across UI → API → Service → Transformer → UI
- ErrorConsistency: All error branches produce defined shared or backend errors

---

## References

- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/334-export-or-copy-finalized-answer.md
- Gate 1: F-FINALIZE-EXPORT
- Gate 2: Option 1 – Fastest Path (All Off-the-Shelf, Managed-First)
