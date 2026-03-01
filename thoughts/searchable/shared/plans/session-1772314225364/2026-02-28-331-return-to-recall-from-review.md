# return-to-recall-from-review TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/331-return-to-recall-from-review.md

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/331-return-to-recall-from-review.md`

Verification output:
- Result: ALL PROPERTIES PASSED
- States: 14 found, 7 distinct, depth 0
- Exit code: 0

This guarantees that every step (capture → update state → re-render) is reachable, type-consistent, and has valid error states at the model level. The following TDD plan reproduces those guarantees at the code level.

---

## Tech Stack (Gate 2 – Option 1)
- Frontend: Next.js (App Router) + React + TypeScript
- Testing: Vitest + React Testing Library
- Logging: frontend_logging (cfg-r3d7)

---

## Resource Mapping

| UUID     | Registry Name     | Concrete Implementation |
|----------|-------------------|-------------------------|
| ui-w8p2  | component         | `frontend/components/ReviewScreen.tsx` |
| ui-v3n6  | module            | `frontend/modules/WritingFlowModule.tsx` |
| cfg-r3d7 | frontend_logging  | `frontend/logging/logger.ts` |

---

## Step 1: Capture return action

**From path spec:**
- Input: User interaction event on the Review screen within frontend component (ui-w8p2)
- Process: Detect 'Return to Recall' selection and emit navigation intent
- Output: Navigation intent targeting Recall step
- Error: If click not bound or component unmounted → no intent emitted and error logged via cfg-r3d7

### Test
`frontend/components/__tests__/ReviewScreen.returnToRecall.test.tsx`

**Reachability**
- Render `ReviewScreen` with mock `onNavigate`.
- Fire click on "Return to Recall" button.
- Assert `onNavigate` called with `{ targetStep: 'RECALL' }`.

**TypeInvariant**
- Assert emitted object matches:
  ```ts
  type NavigationIntent = { targetStep: 'RECALL' | 'REVIEW' }
  ```
- Use TypeScript type assertion in test.

**ErrorConsistency**
- Render component, then unmount.
- Simulate click via stored handler reference (or call handler after unmount).
- Assert `logger.error` called with message containing "ReturnToRecall: component unmounted".
- Assert `onNavigate` not called.

### Implementation
`frontend/components/ReviewScreen.tsx`
- Props:
  ```ts
  type Props = {
    onNavigate: (intent: NavigationIntent) => void;
  }
  ```
- Button with `data-testid="return-to-recall"`.
- Click handler:
  - If mounted → call `onNavigate({ targetStep: 'RECALL' })`
  - If not mounted → `logger.error(...)`
- Track mounted state with `useEffect` cleanup flag.

---

## Step 2: Update writing flow state

**From path spec:**
- Input: Navigation intent to return to Recall; current step state (ui-v3n6)
- Process: Update internal state → activeStep = 'RECALL'; Review inactive
- Output: Updated module state with 'Recall' active
- Error: If current flow state invalid/missing → prevent transition and log via cfg-r3d7

### Test
`frontend/modules/__tests__/WritingFlowModule.returnToRecall.test.tsx`

**Reachability**
- Initialize module with state `{ activeStep: 'REVIEW' }`.
- Call `handleNavigation({ targetStep: 'RECALL' })`.
- Assert `activeStep === 'RECALL'`.

**TypeInvariant**
- Assert state type:
  ```ts
  type WritingFlowState = { activeStep: 'RECALL' | 'REVIEW' }
  ```
- Ensure transition preserves union type.

**ErrorConsistency**
- Initialize module with invalid state (e.g., `undefined` or malformed object via cast).
- Call `handleNavigation({ targetStep: 'RECALL' })`.
- Assert state unchanged.
- Assert `logger.error` called with "Invalid flow state".

### Implementation
`frontend/modules/WritingFlowModule.tsx`
- Internal state via `useState<WritingFlowState>`.
- `handleNavigation(intent: NavigationIntent)`:
  - Guard: if state invalid → log error + return.
  - If `intent.targetStep === 'RECALL'` → set state.
- Export context provider so components can consume.

---

## Step 3: Re-render Recall screen

**From path spec:**
- Input: Updated active step state
- Process: Conditionally render Recall component; remove Review component
- Output: Recall mounted and visible; Review unmounted
- Error: If Recall fails to mount → display fallback error state and log rendering failure

### Test
`frontend/modules/__tests__/WritingFlowModule.rendering.test.tsx`

**Reachability**
- Render `WritingFlowModule` with initial step 'REVIEW'.
- Trigger navigation to 'RECALL'.
- Assert Recall component present (`getByTestId('recall-screen')`).
- Assert Review component absent (`queryByTestId('review-screen')` is null).

**TypeInvariant**
- Assert rendered component corresponds exactly to `activeStep` union value.
- Use discriminated conditional rendering.

**ErrorConsistency**
- Mock Recall component to throw during render.
- Assert fallback UI displayed (`getByText('Unable to load Recall step')`).
- Assert `logger.error` called with "Recall render failure".

### Implementation
`frontend/modules/WritingFlowModule.tsx`
- Conditional JSX:
  ```tsx
  {state.activeStep === 'RECALL' && (
    <ErrorBoundary fallback={<FallbackRecallError />}>
      <RecallScreen data-testid="recall-screen" />
    </ErrorBoundary>
  )}
  ```
- `FallbackRecallError` component.
- ErrorBoundary logs via `frontend/logging/logger.ts`.

---

## Terminal Condition

**Integration test**
`frontend/modules/__tests__/returnToRecall.integration.test.tsx`

- Render full `WritingFlowModule` starting in 'REVIEW'.
- Simulate user clicking "Return to Recall".
- Assert:
  - Recall screen visible.
  - Review screen not visible.
  - Recall input interface active (e.g., record button present).

This test proves end-to-end reachability from trigger → state update → UI re-render.

---

## References
- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/331-return-to-recall-from-review.md
- Gate 2 Tech Stack (Option 1 – Next.js + TypeScript)
- Resource Registry entries: ui-w8p2, ui-v3n6, cfg-r3d7
