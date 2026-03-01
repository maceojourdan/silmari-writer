# display-recall-state-with-record-button-and-progress-indicator TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/303-display-recall-state-with-record-button-and-progress-indicator.md`

Tech Stack (Gate 2 – Option 1):
- Frontend: Next.js (App Router), React, TypeScript, TailwindCSS
- Testing: Vitest + React Testing Library
- Backend: Next.js API Routes (not used directly in this path)

---

## Verification (Phase 0)
The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/303-display-recall-state-with-record-button-and-progress-indicator.md`

Verification output (excerpt):
- Result: ALL PROPERTIES PASSED  
- States: 22 found, 11 distinct, depth 0  
- Exit code: 0  

This TDD plan mirrors those guarantees at code level:
- Reachability → each step callable in sequence from trigger
- TypeInvariant → strict TypeScript types + runtime assertions
- ErrorConsistency → defined error states from shared_error_definitions

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-v3n6 | module | `frontend/modules/RecallModule.tsx` |
| ui-x1r9 | access_control | `frontend/access_controls/RecallAccessControl.ts` |
| ui-w8p2 | component | `frontend/components/RecallLayout.tsx`, `RecordButton.tsx`, `ProgressIndicator.tsx` |
| ui-y5t3 | data_loader | `frontend/data_loaders/RecallProgressLoader.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/frontendLogger.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/uiErrors.ts` |

---

## Step 1: Activate Recall Module - [x] DONE

**From path spec:**
- Input: User navigation event to main interface; ui-v3n6 (module)
- Process: Module initializes and determines current application state.
- Output: Initialized module context with current state value = RECALL.
- Error: If state cannot be determined, fallback to safe default state and log via cfg-r3d7; explicit state-not-found error.

### Test (`frontend/modules/__tests__/RecallModule.step1.test.tsx`)

- Reachability:
  - Render `<RecallModule initialState="RECALL" />`
  - Assert context.state === "RECALL"
- TypeInvariant:
  - Assert returned context satisfies `AppStateContext` type with `state: 'RECALL' | ...`
- ErrorConsistency:
  - Render with `initialState={undefined}`
  - Assert fallback state === "SAFE_DEFAULT"
  - Assert logger called with `UI_STATE_NOT_FOUND`

### Implementation (`frontend/modules/RecallModule.tsx`)

- Define `AppState = 'INIT' | 'ORIENT' | 'RECALL' | ... | 'SAFE_DEFAULT'`
- On mount, resolve state from prop or session store.
- If falsy/unknown:
  - log via `frontendLogger.error(UI_STATE_NOT_FOUND)`
  - set state = 'SAFE_DEFAULT'
- Provide React context with resolved state.

---

## Step 2: Validate Recall Access - [x] DONE

**From path spec:**
- Input: Initialized module context with state = RECALL; ui-x1r9
- Process: Access control verifies user allowed to view RECALL.
- Output: Authorization result permitting rendering.
- Error: If denied, redirect and log via cfg-r3d7.

### Test (`frontend/access_controls/__tests__/RecallAccessControl.step2.test.ts`)

- Reachability:
  - Call `validateRecallAccess({ state: 'RECALL', user })`
  - Assert result.authorized === true
- TypeInvariant:
  - Assert return type `AccessResult { authorized: boolean; redirect?: string }`
- ErrorConsistency:
  - Provide user without permission
  - Assert authorized === false
  - Assert redirect === '/dashboard'
  - Assert logger called with `UI_RECALL_ACCESS_DENIED`

### Implementation (`frontend/access_controls/RecallAccessControl.ts`)

- Function `validateRecallAccess(context): AccessResult`
- If state !== 'RECALL' → deny
- If user.role lacks permission →
  - log `UI_RECALL_ACCESS_DENIED`
  - return { authorized: false, redirect: '/dashboard' }
- Else return { authorized: true }

---

## Step 3: Compose Recall UI Components - [x] DONE

**From path spec:**
- Input: Authorized RECALL state context; ui-w8p2
- Process: Assemble RECALL layout with record button + progress indicator.
- Output: Rendered component tree containing record button and progress indicator placeholders.
- Error: If required component missing/fails, show fallback error component and log.

### Test (`frontend/modules/__tests__/RecallModule.step3.test.tsx`)

- Reachability:
  - Render `<RecallModule state="RECALL" authorized />`
  - Assert `getByTestId('record-button')` exists
  - Assert `getByTestId('progress-indicator')` exists
- TypeInvariant:
  - Assert props passed to `RecordButton` and `ProgressIndicator` satisfy defined TS interfaces
- ErrorConsistency:
  - Mock `RecordButton` to throw
  - Assert fallback error component rendered
  - Assert logger called with `UI_COMPONENT_INIT_ERROR`

### Implementation

- `RecallLayout.tsx` composes:
  - `<RecordButton data-testid="record-button" />`
  - `<ProgressIndicator data-testid="progress-indicator" />`
- Wrap in error boundary:
  - On error → render `<RecallFallbackError />`
  - Log `UI_COMPONENT_INIT_ERROR`

---

## Step 4: Populate Progress Indicator - [x] DONE

**From path spec:**
- Input: Rendered RECALL component tree; ui-y5t3
- Process: Retrieve progress state for Anchors, Actions, Outcomes; bind to indicator.
- Output: Indicator displays current completion status.
- Error: If retrieval fails, display neutral/empty state and log.

### Test (`frontend/data_loaders/__tests__/RecallProgressLoader.step4.test.ts`)

- Reachability:
  - Mock fetch `/api/recall/progress`
  - Call `loadRecallProgress(sessionId)`
  - Assert returned `{ anchors, actions, outcomes }`
- TypeInvariant:
  - Assert returned object matches `RecallProgress` type
- ErrorConsistency:
  - Mock fetch rejection
  - Assert returned `{ anchors: 0, actions: 0, outcomes: 0 }`
  - Assert logger called with `UI_PROGRESS_LOAD_FAILED`

Integration test in component:
- Render layout with mocked loader success
- Assert numbers rendered in indicator

### Implementation (`frontend/data_loaders/RecallProgressLoader.ts`)

- Export type `RecallProgress`
- Async function calling Next.js API route
- Try/catch:
  - On success → return parsed data
  - On error → log + return neutral state

---

## Step 5: Display Prominent Record Button - [x] DONE

**From path spec:**
- Input: Rendered RECALL component tree with state-bound properties; ui-w8p2
- Process: Style/configure record button prominently and enabled.
- Output: Large, enabled record button visible.
- Error: If styling/config fails, fallback to default styling but visible; log.

### Test (`frontend/components/__tests__/RecordButton.step5.test.tsx`)

- Reachability:
  - Render `<RecordButton prominent />`
  - Assert button has Tailwind classes: `text-4xl`, `rounded-full`, `w-32 h-32`
  - Assert button is enabled
- TypeInvariant:
  - Props satisfy `RecordButtonProps { prominent: boolean; disabled?: boolean }`
- ErrorConsistency:
  - Mock style computation to throw
  - Assert button rendered with default classes
  - Assert logger called with `UI_RECORD_BUTTON_STYLE_ERROR`

### Implementation (`frontend/components/RecordButton.tsx`)

- If `prominent`:
  - Apply large Tailwind classes
- Wrap style logic in try/catch
  - On error → apply default class set
  - Log style error

---

## Terminal Condition - [x] DONE

### Integration Test (`frontend/modules/__tests__/RecallModule.integration.test.tsx`)

Exercise full path:
- Render `<RecallModule initialState="RECALL" userWithAccess />`
- Mock progress loader success

Assert:
- State resolved to RECALL
- Access authorized
- Record button visible and enabled
- Progress indicator visible
- Anchors/Actions/Outcomes displayed

This proves:
- Reachability: Trigger → Step1→2→3→4→5
- TypeInvariant: All TS contracts satisfied end-to-end
- ErrorConsistency: Each failure branch produces defined UI error state and logs via cfg-r3d7

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/303-display-recall-state-with-record-button-and-progress-indicator.md`
- Gate 1 Requirement: `USAB-VOICE-UX`
- Gate 2 Tech Stack: Option 1 – Next.js (App Router) on Vercel
