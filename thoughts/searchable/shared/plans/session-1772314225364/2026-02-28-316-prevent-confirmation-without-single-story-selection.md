# prevent-confirmation-without-single-story-selection TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/316-prevent-confirmation-without-single-story-selection.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/316-prevent-confirmation-without-single-story-selection.md
```

Stdout:
```
Path: prevent-confirmation-without-single-story-selection
TLA+ spec: .../PreventConfirmationWithoutSingleStorySelection.tla
TLC config: .../PreventConfirmationWithoutSingleStorySelection.cfg
Result: ALL PROPERTIES PASSED
States: 18 found, 9 distinct, depth 0
```

This plan translates those verified properties into executable Jest + React Testing Library tests in a Next.js (TypeScript) codebase.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|---------------|-------------------------|
| ui-w8p2 | component | `frontend/components/StorySelectionConfirm.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/singleStorySelectionVerifier.ts` |
| ui-y5t3 | data_loader | `frontend/data_loaders/confirmStorySelectionLoader.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/StoryErrors.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/logger.ts` |

Tech stack (Gate 2 – Option 1):
- Next.js (App Router)
- React + TypeScript
- Jest + React Testing Library

---

## Step 1: Capture confirm action

**From path spec:**
- Input: User interaction event delivered to frontend component (ui-w8p2 component)
- Process: Component receives Confirm click and gathers current selection state
- Output: Current story selection state (empty selection set) prepared for validation
- Error: If component state unavailable/corrupted, log via cfg-r3d7 and disable Confirm button

### Test (`frontend/components/__tests__/StorySelectionConfirm.step1.test.tsx`)

- Reachability:
  - Render component with `selectedStoryIds = []`
  - Simulate Confirm click
  - Assert internal handler receives `[]` as current selection state

- TypeInvariant:
  - Assert selection state passed to verifier is `string[]`

- ErrorConsistency:
  - Render with corrupted state (e.g., `selectedStoryIds = null as any`)
  - Click Confirm
  - Assert `logger.error` called
  - Assert Confirm button becomes disabled

### Implementation (`frontend/components/StorySelectionConfirm.tsx`)

- Props:
  ```ts
  type Props = {
    selectedStoryIds: string[] | null;
  }
  ```
- `handleConfirmClick()`:
  - If `!Array.isArray(selectedStoryIds)`:
    - `logger.error('Invalid selection state')`
    - set `isDisabled = true`
    - return
  - Else forward `selectedStoryIds` to Step 2 verifier

Minimal logic only to satisfy tests.

---

## Step 2: Validate single selection requirement

**From path spec:**
- Input: Current story selection state; validation rule from ui-a4y1
- Process: Check exactly one story selected
- Output: Validation result indicating failure (zero selected)
- Error: If verifier misconfigured, treat as failed; log via cfg-r3d7

### Test (`frontend/verifiers/__tests__/singleStorySelectionVerifier.test.ts`)

- Reachability:
  - Call `validateSingleStorySelection([])`
  - Expect `{ valid: false, reason: 'StorySelectionRequired' }`

- TypeInvariant:
  - Assert return type matches:
    ```ts
    type ValidationResult = { valid: boolean; reason?: string }
    ```

- ErrorConsistency:
  - Simulate misconfiguration (e.g., exported rule undefined via jest mock)
  - Expect:
    - `{ valid: false }`
    - `logger.error` called

### Implementation (`frontend/verifiers/singleStorySelectionVerifier.ts`)

```ts
export function validateSingleStorySelection(
  selected: string[]
): ValidationResult {
  if (!Array.isArray(selected)) {
    logger.error('Verifier misconfiguration');
    return { valid: false };
  }
  return selected.length === 1
    ? { valid: true }
    : { valid: false, reason: 'StorySelectionRequired' };
}
```

---

## Step 3: Block confirmation flow

**From path spec:**
- Input: Validation failure result
- Process: Prevent backend API contract invocation
- Output: No confirmation request sent; remain on selection screen
- Error: If backend call already initiated, cancel via ui-y5t3

### Test (`frontend/components/__tests__/StorySelectionConfirm.step3.test.tsx`)

- Reachability:
  - Mock `confirmStorySelectionLoader.confirm()`
  - Render with `[]`
  - Click Confirm
  - Assert `confirm` NOT called

- TypeInvariant:
  - Ensure validation result object passed through component unchanged

- ErrorConsistency (race condition):
  - Mock loader returning cancellable promise
  - Simulate in-flight request before validation resolves
  - Expect `loader.cancel()` called
  - Ignore resolution result

### Implementation (`frontend/data_loaders/confirmStorySelectionLoader.ts`)

```ts
export const confirmStorySelectionLoader = {
  confirm: async (storyId: string) => { /* API call */ },
  cancel: () => { /* abort controller */ }
};
```

In component:
- If `validation.valid === false`:
  - Do NOT call `confirm`
  - If inFlightRef exists → call `cancel()`

---

## Step 4: Display validation feedback

**From path spec:**
- Input: Validation failure + shared error definition
- Process: Render validation message
- Output: Visible prompt; Confirm remains disabled/blocked
- Error: If specific error not found, fallback message and log

### Test (`frontend/components/__tests__/StorySelectionConfirm.step4.test.tsx`)

- Reachability:
  - Render with `[]`
  - Click Confirm
  - Assert message:
    "Please select exactly one story before confirming."

- TypeInvariant:
  - Assert error message type is `string`

- ErrorConsistency:
  - Mock `StoryErrors.StorySelectionRequired` undefined
  - Click Confirm
  - Assert fallback message rendered
  - Assert `logger.error` called with `[PROPOSED: StorySelectionRequired error type]`

### Implementation

**`shared/error_definitions/StoryErrors.ts`**
```ts
export const StoryErrors = {
  StorySelectionRequired: {
    code: 'StorySelectionRequired',
    message: 'Please select exactly one story before confirming.'
  }
};
```

Component logic:
- On `reason === 'StorySelectionRequired'`:
  - Retrieve from `StoryErrors`
  - If missing → fallback string
  - Log missing definition

---

## Terminal Condition

### Integration Test
`frontend/components/__tests__/StorySelectionConfirm.integration.test.tsx`

- Render component with `selectedStoryIds = []`
- Click Confirm up to 5 times
- Assert:
  - Validation message visible
  - `confirmStorySelectionLoader.confirm` never called
  - Confirm action remains blocked

This proves:
- Reachability: Full path from trigger to terminal
- TypeInvariant: Selection state and validation result types preserved
- ErrorConsistency: All error branches produce stable UI state

---

## References
- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/316-prevent-confirmation-without-single-story-selection.md`
- Gate 1: F-ORIENT-STORY (AC #5)
- Verification artifacts under `frontend/artifacts/tlaplus/316-prevent-confirmation-without-single-story-selection/`
