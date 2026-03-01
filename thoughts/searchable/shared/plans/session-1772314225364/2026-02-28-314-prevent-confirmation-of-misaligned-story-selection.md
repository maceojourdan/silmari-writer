# prevent-confirmation-of-misaligned-story-selection TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/314-prevent-confirmation-of-misaligned-story-selection.md

---

## Verification (Phase 0)

The TLA+ model for this path passed the following properties:
- **Reachability**
- **TypeInvariant**
- **ErrorConsistency**

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/314-prevent-confirmation-of-misaligned-story-selection.md
```

Result (from verification_results_json):
- Result: **ALL PROPERTIES PASSED**
- States: 18 found, 9 distinct
- Exit code: 0

This TDD plan implements code-level tests that assert the same three guarantees.

---

## Tech Stack (Gate 2 – Option 1)
- **Frontend:** Next.js (App Router), React, TypeScript
- **Testing:** Vitest + React Testing Library
- **Backend:** Not involved (client-side validation only)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-v3n6 | module | `frontend/modules/orient/StorySelectionModule.tsx` |
| ui-w8p2 | component | `frontend/components/orient/ConfirmSelectionButton.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/AlignmentVerifier.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/AlignmentErrors.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

---

## Step 1: Capture confirm action ✅

**From path spec:**
- Input: User interaction event from ui-w8p2 within ui-v3n6, including selected story identifier and current question/job context.
- Process: Handle confirm click and package selected story + context into confirmation request payload.
- Output: Structured confirmation request payload ready for validation.
- Error: If required selection data is missing, ui-a4y1 flags issue and displays generic validation message without sending request.

### Test (`frontend/src/components/__tests__/StorySelection.step1-alignment.test.tsx`)

- [x] **Reachability:**
  - Render `StorySelection` with selectedStory + context.
  - Click Confirm.
  - Assert payload passed to `AlignmentVerifier.validate()`.

- [x] **TypeInvariant:**
  - Assert payload shape:
    ```ts
    type ConfirmationPayload = {
      storyId: string;
      questionId: string;
      jobId: string;
    }
    ```

- [x] **ErrorConsistency:**
  - Render without selectedStory.
  - Confirm button is disabled.
  - Assert: `AlignmentVerifier.validate` NOT called.

### Implementation

- [x] **`AlignmentVerifier.ts`** (`frontend/src/verifiers/AlignmentVerifier.ts`)
  - Export `validate(payload: ConfirmationPayload, rules: AlignmentRules)`.

- [x] **`StorySelection.tsx`** (`frontend/src/components/StorySelection.tsx`)
  - On click: construct `ConfirmationPayload` and call `AlignmentVerifier.validate()`.
  - Added `jobId` prop for alignment context.

---

## Step 2: Perform client-side alignment validation ✅

**From path spec:**
- Input: Confirmation request payload + alignment rules from ui-a4y1.
- Process: Evaluate alignment against question/job requirements.
- Output: Validation result: "aligned" | "misaligned" + message key.
- Error: If rules unavailable → treat as failure with error `[PROPOSED: ALIGNMENT_RULES_UNAVAILABLE]` from cfg-j9w2.

### Test (`frontend/src/verifiers/__tests__/AlignmentVerifier.step2.test.ts`)

- [x] **Reachability:**
  - Call `validate(validPayload)` with matching rules.
  - Assert result.status === "aligned".

- [x] **TypeInvariant:**
  - Assert return type: `AlignmentResult { status, messageKey? }`.

- [x] **ErrorConsistency (misaligned):**
  - Payload with wrong questionId → `STORY_MISALIGNED`.
  - Payload with EXCLUDED status → `STORY_MISALIGNED`.
  - Unknown storyId → `STORY_MISALIGNED`.

- [x] **ErrorConsistency (rules unavailable):**
  - rules = null → status "misaligned", messageKey `ALIGNMENT_RULES_UNAVAILABLE`.

### Implementation

- [x] **`AlignmentVerifier.ts`** (`frontend/src/verifiers/AlignmentVerifier.ts`)
  - Pure function accepting injected rules.
  - If rules null → `ALIGNMENT_RULES_UNAVAILABLE`.
  - If story not found / wrong questionId / non-AVAILABLE status → `STORY_MISALIGNED`.
  - Else → `aligned`.

- [x] **`AlignmentErrors.ts`** (`frontend/src/server/error_definitions/AlignmentErrors.ts`)
  - STORY_MISALIGNED, ALIGNMENT_RULES_UNAVAILABLE, GENERIC_SELECTION_REQUIRED defined.

---

## Step 3: Block confirmation on misalignment ✅

**From path spec:**
- Input: Validation result indicating misalignment + error metadata.
- Process: Prevent further confirmation, map validation failure to user-friendly message, update component state.
- Output: UI state updated with visible alignment error message and halted confirmation.
- Error: If error message mapping fails, fallback to default alignment error message.

### Test (`frontend/src/components/__tests__/StorySelection.step3-alignment.test.tsx`)

- [x] **Reachability:**
  - Mock verifier returning `{ status: "misaligned", messageKey: "STORY_MISALIGNED" }`.
  - Click Confirm → onConfirmed NOT called, API NOT called, error message visible.
  - Mock verifier returning `{ status: "aligned" }` → onConfirmed IS called.

- [x] **TypeInvariant:**
  - Component renders alignment error as string with `data-testid="alignment-error"`.

- [x] **ErrorConsistency (mapping fails):**
  - Unknown messageKey → fallback to STORY_MISALIGNED message.
  - Undefined messageKey → fallback to STORY_MISALIGNED message.
  - Selecting different story clears alignment error.

### Implementation

- [x] In `StorySelection.tsx`:
  - After `validate()`: if `aligned` → proceed to API call; if `misaligned` → resolve message, set `isBlocked = true`.
  - Fallback to `STORY_MISALIGNED` for unknown/undefined messageKey.
  - No backend call is made when misaligned.

---

## Step 4: Render validation feedback to user ✅

**From path spec:**
- Input: Updated component state with alignment error message.
- Process: Re-render confirmation section showing message and keep user on current screen.
- Output: Visible message indicating story does not meet alignment criteria.
- Error: If rendering fails, log via cfg-r3d7 and display minimal fallback banner.

### Test (`frontend/src/components/__tests__/StorySelection.step4-alignment.test.tsx`)

- [x] **Reachability:**
  - Force misaligned state → error banner rendered with `role="alert"`.
  - User remains on selection screen (stories and confirm button still visible).
  - ALIGNMENT_RULES_UNAVAILABLE message displayed correctly.

- [x] **TypeInvariant:**
  - Banner renders non-empty string message.

- [x] **ErrorConsistency (render failure):**
  - `_testForceRenderError` prop triggers throw in AlignmentErrorBanner.
  - `frontendLogger.error()` called.
  - Fallback banner rendered: "An error occurred while displaying validation feedback."

### Implementation

- [x] **`StorySelection.tsx`** (`frontend/src/components/StorySelection.tsx`)
  - `AlignmentErrorBanner` component conditionally rendered.
  - `AlignmentErrorBoundary` class component wraps banner.
  - On catch → `frontendLogger.error()` called, minimal fallback banner rendered.

- [x] **`frontend/logging/index.ts`** (existing, used as-is via `frontendLogger.error()`).

---

## Terminal Condition ✅

### Integration Test
`frontend/src/modules/orient-story/__tests__/preventConfirmation.integration.test.tsx`

- [x] Render full `OrientStoryModule`.
- [x] Select misaligned story (EXCLUDED status).
- [x] Click Confirm.
- [x] Assert:
  - Alignment error message visible.
  - Confirmation callback not invoked.
  - API not called.
  - User remains on selection screen.
- [x] Select aligned story → confirmation succeeds.
- [x] Error clears on re-selection, retry succeeds.

This proves:
- [x] **Reachability:** Full path exercised end-to-end.
- [x] **TypeInvariant:** Payload + result types enforced.
- [x] **ErrorConsistency:** All error branches yield valid UI error state.

---

## References

- Path: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/314-prevent-confirmation-of-misaligned-story-selection.md`
- Requirement: `F-ORIENT-STORY` (Acceptance Criterion #3)
- Shared errors: `cfg-j9w2`
- Frontend verifier: `ui-a4y1`
- Logging: `cfg-r3d7`
