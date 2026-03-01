# complete-required-slots-and-end-recall-loop TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/319-complete-required-slots-and-end-recall-loop.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
`silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/319-complete-required-slots-and-end-recall-loop.md`

Stdout:
```
Path: complete-required-slots-and-end-recall-loop
TLA+ spec: .../CompleteRequiredSlotsAndEndRecallLoop.tla
TLC config: .../CompleteRequiredSlotsAndEndRecallLoop.cfg
Result: ALL PROPERTIES PASSED
States: 22 found, 11 distinct, depth 0
```

All three required properties are satisfied at the model level and must now be enforced via code-level tests.

---

## Tech Stack (Gate 2)

Option 1 – Fastest Path:
- Next.js (App Router)
- TypeScript
- Next.js API Routes (Node runtime)
- Zod for schema validation
- Vitest (or Vitest) for unit tests

All implementation below assumes TypeScript + Vitest in a single Next.js repo.

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| cfg-d2q3 | common_structure | `frontend/src/server/data_structures/RecallSession.ts` ✅ |
| cfg-f7s8 | data_type | `frontend/src/server/data_structures/VoiceInteractionContext.ts` (existing QuestionTypeDefinitionSchema) ✅ |
| cfg-g1u4 | shared_verifier | `frontend/src/server/verifiers/RequiredSlotVerifier.ts` ✅ |
| cfg-j9w2 | shared_error_definitions | `frontend/src/server/error_definitions/RecallErrors.ts` ✅ |
| cfg-p4b8 | shared_logging | `frontend/src/server/logging/recallCompletionLogger.ts` ✅ |

Orchestration service:
- `frontend/src/server/services/RecallCompletionService.ts` ✅

API entry (if needed later):
- `backend/endpoints/completeRequiredSlots.ts`

---

# Step 1: Capture Additional Spoken Input ✅

**From path spec:**
- Input: Raw spoken utterance + active recall state (cfg-d2q3)
- Process: Accept spoken input and associate with active question_type recall session
- Output: Structured spoken input event linked to active session
- Error: If no active recall session exists → structured invalid recall state error (cfg-j9w2)

---

### Test ✅
`frontend/src/server/services/__tests__/RecallCompletionService.step1.test.ts`

**Reachability** ✅
- [x] Given: RecallSession.active = true
- [x] When: `captureAdditionalInput(session, "I increased revenue by 20%")`
- [x] Then: returns `{ sessionId, questionType, utterance }`

**TypeInvariant** ✅
- [x] Assert return type is `StructuredSpokenInputEvent`
- [x] Assert `utterance: string`, `sessionId: string`, `questionType: string`

**ErrorConsistency** ✅
- [x] Given: RecallSession.active = false
- [x] When: captureAdditionalInput
- [x] Then: throw `InvalidRecallStateError` from `RecallErrors.ts`

---

### Implementation ✅
`frontend/src/server/services/RecallCompletionService.ts`

- [x] Implement `captureAdditionalInput()`
- [x] Validate session.active === true
- [x] Return typed object
- [x] Throw `InvalidRecallStateError`

---

# Step 2: Transform Utterance Into Slot Values ✅

**From path spec:**
- Input: Structured spoken input event + slot schema (cfg-f7s8)
- Process: Convert utterance → candidate slot-value pairs aligned to required slots
- Output: Extracted slot-value pairs mapped to required slot identifiers
- Error: If no recognizable slots → structured parsing error (cfg-j9w2) and re-prompt within retry limit

---

### Test ✅
`frontend/src/server/services/__tests__/RecallCompletionService.step2.test.ts`

**Reachability** ✅
- [x] Given: StructuredSpokenInputEvent from Step 1
- [x] Given: QuestionTypeSchema with required slots: ["objective", "outcome"]
- [x] When: transformUtterance(event, schema)
- [x] Then: returns `{ objective: "...", outcome: "..." }`

**TypeInvariant** ✅
- [x] Assert keys are valid slot identifiers defined in QuestionTypeSchema
- [x] Assert values are strings

**ErrorConsistency** ✅
- [x] Given: utterance with no recognizable slot data
- [x] When: transformUtterance
- [x] Then: throw `SlotParsingError`
- [x] And: session.retryCount increments (≤ 3 enforced by RecallSession)

---

### Implementation ✅

- [x] Add `transformUtterance()`
- [x] Use simple deterministic extractor (regex or mock extractor service)
- [x] Validate slot ids exist in `QuestionTypeSchema`
- [x] If empty result → throw `SlotParsingError`

---

# Step 3: Merge With Existing Recall State ✅

**From path spec:**
- Input: Extracted slot-value pairs + existing partial slot state (cfg-d2q3)
- Process: Fill previously missing required slots
- Output: Updated slot state
- Error: If slot identifiers do not match schema → validation error (cfg-j9w2)

---

### Test ✅
`frontend/src/server/services/__tests__/RecallCompletionService.step3.test.ts`

**Reachability** ✅
- [x] Given: session.slots = { objective: null, outcome: null }
- [x] Given: extracted = { objective: "Increase revenue" }
- [x] When: mergeSlots(session, extracted)
- [x] Then: session.slots.objective = "Increase revenue"

**TypeInvariant** ✅
- [x] Assert session.slots matches QuestionTypeSchema shape
- [x] No unknown keys allowed

**ErrorConsistency** ✅
- [x] Given: extracted = { invalidSlot: "value" }
- [x] When: mergeSlots
- [x] Then: throw `SlotValidationError`

---

### Implementation ✅

- [x] Implement `mergeSlots()`
- [x] Check extracted keys ⊆ schema.requiredSlots
- [x] Mutate session.slots safely
- [x] Throw `SlotValidationError` if mismatch

---

# Step 4: Validate Required Slot Completion ✅

**From path spec:**
- Input: Updated slot state + required slot rules (cfg-g1u4)
- Process: Evaluate whether all required slots present and valid
- Output: Validation result (complete | incomplete)
- Error: If validation rules fail → emit validation error and continue recall

---

### Test ✅
`frontend/src/server/services/__tests__/RecallCompletionService.step4.test.ts`

**Reachability** ✅
- [x] Given: session.slots fully populated
- [x] When: validateRequiredSlots(session.slots)
- [x] Then: returns `{ complete: true }`

**TypeInvariant** ✅
- [x] Assert return type `ValidationResult`
- [x] Assert boolean `complete`

**ErrorConsistency** ✅
- [x] Given: slot value violates rule (e.g., actions < 3)
- [x] When: validateRequiredSlots
- [x] Then: throw `SlotValidationError`

---

### Implementation ✅

- [x] Implement `RequiredSlotVerifier.validate()`
- [x] Ensure:
  - [x] All required slots present
  - [x] Slot constraints satisfied
- [x] Return typed result

---

# Step 5: Confirm Completion And Terminate Recall Loop ✅

**From path spec:**
- Input: Validation result (complete) + active session state
- Process: Mark recall loop complete and generate confirmation message
- Output: Confirmation response + recall state inactive
- Error: If state update fails → structured state-transition error + log via shared logging

---

### Test ✅
`frontend/src/server/services/__tests__/RecallCompletionService.step5.test.ts`

**Reachability** ✅
- [x] Given: validation.complete = true
- [x] When: confirmCompletion(session)
- [x] Then:
  - [x] session.active = false
  - [x] returns confirmation message string

**TypeInvariant** ✅
- [x] Assert session.active is boolean
- [x] Assert confirmation is string

**ErrorConsistency** ✅
- [x] Mock: session state persistence throws error
- [x] When: confirmCompletion
- [x] Then:
  - [x] throw `RecallStateTransitionError`
  - [x] logger.error called (cfg-p4b8)

---

### Implementation ✅

- [x] Implement `confirmCompletion()`
- [x] Set session.active = false
- [x] Return confirmation string
- [x] Wrap state update in try/catch
- [x] Log error before rethrowing

---

# Feedback Loop Enforcement (Retry Limit) ✅

Add to `RecallSession` (cfg-d2q3):
- [x] `retryCount: number`
- [x] `maxRetries = 3`

### Test ✅
`frontend/src/server/services/__tests__/RecallCompletionService.retry.test.ts`

- [x] Given: retryCount = 2
- [x] When: parsing fails again
- [x] Then: emit `IncompleteInformationError`
- [x] And: session.active remains true until limit exceeded

---

# Terminal Condition ✅

### Integration Test ✅
`frontend/src/server/services/__tests__/RecallCompletionService.integration.test.ts`

Exercise full path:
1. [x] Active session with missing required slots
2. [x] Capture additional input
3. [x] Transform into slots
4. [x] Merge
5. [x] Validate complete
6. [x] Confirm completion

Assert:
- [x] Confirmation message returned
- [x] session.active = false
- [x] No further prompts triggered

This proves:
- [x] Reachability: trigger → terminal condition
- [x] TypeInvariant: types consistent across boundaries
- [x] ErrorConsistency: all error branches emit structured RecallErrors

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/319-complete-required-slots-and-end-recall-loop.md`
- Gate 1: F-RECALL-LOOP
- Gate 2: Option 1 – Next.js + TypeScript + Vitest

---

## Validation Report

**Validated at**: 2026-03-01T14:15:00Z

### Implementation Status
✓ Phase 0: Verification (TLA+ model) - Passed (pre-existing)
✓ Step 1: Capture Additional Spoken Input - Fully implemented
✓ Step 2: Transform Utterance Into Slot Values - Fully implemented
✓ Step 3: Merge With Existing Recall State - Fully implemented
✓ Step 4: Validate Required Slot Completion - Fully implemented
✓ Step 5: Confirm Completion And Terminate Recall Loop - Fully implemented
✓ Feedback Loop Enforcement (Retry Limit) - Fully implemented
✓ Terminal Condition (Integration Test) - Fully implemented

**Plan checklist completion**: 81/81 items (100%)

### Automated Verification Results
✓ All 44 RecallCompletionService tests pass (7 test files: step1–step5, retry, integration)
✓ TLA+ properties (Reachability, TypeInvariant, ErrorConsistency) enforced in every step
⚠️ 8 pre-existing test failures in `ButtonInteractions.test.tsx` (unrelated — `setVoiceSessionState` hook error)
⚠️ 1 lint warning: unused variable `utterance` in `RecallCompletionService.ts:30`
⚠️ Pre-existing TS errors in `behavioralQuestionVerifier.test.ts` (missing vitest type defs — unrelated)

**Test summary**: 2594 passed, 8 failed (pre-existing), 9 skipped across 245 test files

### Resource Mapping Verification
All 6 resource mappings verified present:

| UUID | File | Exists |
|------|------|--------|
| cfg-d2q3 | `RecallSession.ts` | ✓ |
| cfg-f7s8 | `VoiceInteractionContext.ts` (QuestionTypeDefinitionSchema) | ✓ |
| cfg-g1u4 | `RequiredSlotVerifier.ts` | ✓ |
| cfg-j9w2 | `RecallErrors.ts` | ✓ |
| cfg-p4b8 | `recallCompletionLogger.ts` | ✓ |
| service | `RecallCompletionService.ts` | ✓ |

### Code Review Findings

#### Matches Plan:
- `captureAdditionalInput()` validates `session.active === true`, returns typed `StructuredSpokenInputEvent`
- `transformUtterance()` extracts slot-value pairs using regex extractors, validates against schema
- `mergeSlots()` checks extracted keys ⊆ schema.requiredSlots, mutates session safely
- `confirmCompletion()` sets `session.active = false`, returns confirmation, logs errors via cfg-p4b8
- `RequiredSlotVerifier.validate()` checks presence + constraint satisfaction
- All 5 error types defined: `InvalidRecallStateError`, `SlotParsingError`, `SlotValidationError`, `RecallStateTransitionError`, `IncompleteInformationError`
- `RecallSession` has `active`, `slotState`, `retryCount`, `maxRetries = 3`
- Retry limit enforcement at `maxRetries = 3` with `IncompleteInformationError` on exceed

#### Deviations from Plan:
- **Slot state representation**: `RecallSession` uses structured `slotState: SlotState` (array of `{name, value, confirmed}`) rather than flat key-value object. Functionally richer; not a regression.
- **Extra method**: `validateRequiredSlots()` added as a convenience wrapper in `RecallCompletionService`. Additive, non-breaking.
- **Duplicate constant**: `BEHAVIORAL_QUESTION_TYPE_RECALL` in `RecallSession.ts` duplicates `BEHAVIORAL_QUESTION_TYPE` in `VoiceInteractionContext.ts`. Could drift if only one is updated.
- **Inconsistent maxRetries default**: `VoiceInteractionContext.ts` defaults `maxRetries` to 2, while `RecallSession.ts` defaults to 3. The plan specifies 3, so `RecallSession` is correct; the other value may be intentional for a different path (317).

#### Issues Found:
- **Files not committed**: All 12 path 319 files are untracked in git (not staged or committed). The implementation is complete but not persisted in version control.
- **Lint warning**: Unused destructured variable `utterance` at `RecallCompletionService.ts:30` — minor, should be prefixed with `_` or removed.
- **Hardcoded slot extractors**: `SLOT_EXTRACTORS` map in `RecallCompletionService.ts` uses regex patterns for 5 known slot names. New slot types added to `QuestionTypeDefinitionSchema` will need manual extractor additions.
- **Hidden side effect**: `transformUtterance()` mutates `session.retryCount` when extraction fails. While documented in JSDoc, callers may not expect a "transform" method to modify session state.

### Manual Testing Required:
- [ ] Verify end-to-end recall flow in the application UI (if wired to frontend)
- [ ] Confirm that the `BEHAVIORAL_QUESTION_TYPE_RECALL` constant stays in sync with `BEHAVIORAL_QUESTION_TYPE`
- [ ] Validate regex slot extractors against real spoken utterances for edge cases

### Recommendations:
1. **Commit the files**: `git add` and commit all 12 untracked path 319 files
2. **Fix lint warning**: Prefix unused `utterance` variable with `_` in `RecallCompletionService.ts:30`
3. **Deduplicate constant**: Import `BEHAVIORAL_QUESTION_TYPE` from `VoiceInteractionContext.ts` instead of duplicating in `RecallSession.ts`
4. **Document extraction strategy**: Add a note about the hardcoded `SLOT_EXTRACTORS` and future extensibility plan
5. **Consider extracting retry logic**: The `transformUtterance` side effect on `retryCount` could be moved to a dedicated method for clarity

VALIDATION_RESULT: PASS
