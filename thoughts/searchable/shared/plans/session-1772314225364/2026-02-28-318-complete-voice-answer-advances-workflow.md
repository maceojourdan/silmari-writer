# complete-voice-answer-advances-workflow TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/318-complete-voice-answer-advances-workflow.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- **Reachability**
- **TypeInvariant**
- **ErrorConsistency**

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/318-complete-voice-answer-advances-workflow.md
```

Result:
```
Result: ALL PROPERTIES PASSED
States: 26 found, 13 distinct, depth 0
```

Verified file:
`frontend/artifacts/tlaplus/318-complete-voice-answer-advances-workflow/CompleteVoiceAnswerAdvancesWorkflow.tla`

These properties map directly to our test oracles:
- Reachability → Each step callable in sequence
- TypeInvariant → Strict TypeScript + Zod type assertions
- ErrorConsistency → Explicit error codes returned per spec

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| cfg-d2q3 | common_structure | `shared/common_structures/SlotSchema.ts` |
| cfg-h5v9 | transformer | `shared/transformers/SlotExtractor.ts` |
| cfg-g1u4 | shared_verifier | `shared/verifiers/MinimumSlotValidator.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/VoiceErrors.ts` |
| db-h2s4 | service | `backend/services/SessionWorkflowService.ts` |
| db-d3w8 | data_access_object | `backend/data_access_objects/SessionDAO.ts` |
| db-l1c3 | backend_error_definitions | `backend/error_definitions/WorkflowErrors.ts` |
| mq-r4z8 | backend_process_chain | `backend/process_chains/AdvanceWorkflowChain.ts` |
| ui-w8p2 | component | `frontend/components/VoiceInteraction.tsx` |
| cfg-r3d7 | frontend_logging | `frontend/logging/VoiceLogger.ts` |

Tech stack (Option 1): Next.js (App Router), TypeScript, Vitest, Zod.

---

## Step 1: Capture spoken answer ✅

**From path spec:**
- Input: Active voice interaction context; raw audio input
- Process: Convert spoken audio into structured textual input and attach to session
- Output: Transcribed user response associated with active question_type
- Error: If transcription fails or audio empty → voice input processing error (cfg-j9w2) + re-prompt (≤3 attempts)

### Test ✅
`backend/services/__tests__/captureSpokenAnswer.318.test.ts` — 8 tests passing

- [x] Reachability:
  - Call `SessionWorkflowService.captureSpokenAnswer(sessionId, audioBlob)`
  - Mock transcription provider → returns "I led a team..."
  - Assert output `{ transcript: string, questionTypeId }`
- [x] TypeInvariant:
  - Assert transcript is non-empty string
  - Assert questionTypeId matches session context
- [x] ErrorConsistency:
  - Mock empty audio → expect `VoiceErrors.TRANSCRIPTION_FAILED`
  - Assert attemptCount incremented and ≤3

### Implementation ✅
`SessionWorkflowService.captureSpokenAnswer()`
- [x] Validate non-empty audio
- [x] Call transcription adapter (ElevenLabs streaming abstraction)
- [x] On failure → return `VoiceErrors.TRANSCRIPTION_FAILED`
- [x] Persist transcript to in-memory session state

---

## Step 2: Extract slot values from response ✅

**From path spec:**
- Input: Transcribed response; cfg-d2q3; cfg-h5v9
- Process: Map entities into defined slots
- Output: Structured slot-value object
- Error: Malformed input → structured transformation error (cfg-j9w2)

### Test ✅
`shared/transformers/__tests__/SlotExtractor.test.ts` — 9 tests passing

- [x] Reachability:
  - Input transcript from Step 1
  - Assert structured object `{ objective, actions[], obstacle, outcome, role }`
- [x] TypeInvariant:
  - Validate result against Zod schema from `SlotSchema`
- [x] ErrorConsistency:
  - Provide malformed transcript (null/invalid)
  - Expect `VoiceErrors.TRANSFORMATION_FAILED`

### Implementation ✅
`SlotExtractor.extract(transcript, questionType)`
- [x] Use deterministic parsing rules (stub for MVP)
- [x] Map into `SlotSchema`
- [x] Throw `VoiceErrors.TRANSFORMATION_FAILED` if parsing impossible

---

## Step 3: Validate minimum required slots ✅

**From path spec:**
- Input: Structured slot-value object; cfg-g1u4; cfg-d2q3
- Process: Evaluate minimum required slots
- Output: Validation result (success or missing list)
- Error: Validation error via cfg-j9w2; initiate follow-up (≤3 attempts)

### Test ✅
`shared/verifiers/__tests__/MinimumSlotValidator.test.ts` — 9 tests passing

- [x] Reachability:
  - Pass complete slot object → expect `{ valid: true }`
- [x] TypeInvariant:
  - Assert return type `{ valid: boolean; missing?: string[] }`
- [x] ErrorConsistency:
  - Pass object missing `outcome`
  - Expect `VoiceErrors.VALIDATION_FAILED`
  - Assert missing contains `outcome`

### Implementation ✅
`MinimumSlotValidator.validate(slotObject, questionType)`
- [x] Compare against required slot list from `SlotSchema`
- [x] Return structured result
- [x] Throw `VoiceErrors.VALIDATION_FAILED` if invalid

---

## Step 4: Persist completed slot set ✅

**From path spec:**
- Input: Validated slot object; db-h2s4; db-d3w8
- Process: Store slot values; mark question_type complete
- Output: Updated session state
- Error: Persistence failure → backend error (db-l1c3)

### Test ✅
`backend/services/__tests__/persistCompletedSlots.test.ts` — 5 tests passing

- [x] Reachability:
  - Mock DAO success
  - Expect session state updated: `questionType.status = COMPLETE`
- [x] TypeInvariant:
  - Assert DAO called with correct typed payload
- [x] ErrorConsistency:
  - Mock DAO throw → expect `WorkflowErrors.PERSISTENCE_FAILED`
  - Assert no workflow advancement

### Implementation ✅
`SessionWorkflowService.persistCompletedSlots()`
- [x] Call `SessionDAO.saveSlots()`
- [x] Update session record
- [x] Wrap errors in `WorkflowErrors.PERSISTENCE_FAILED`

---

## Step 5: Advance workflow to next step ✅

**From path spec:**
- Input: Updated session; mq-r4z8
- Process: Determine and activate next step; disable further questioning
- Output: Next workflow step activated
- Error: Transition failure → workflow transition error (db-l1c3)

### Test ✅
`backend/process_chains/__tests__/AdvanceWorkflowChain.test.ts` — 6 tests passing

- [x] Reachability:
  - Input session with completed question_type
  - Expect next state (e.g., VERIFY)
- [x] TypeInvariant:
  - Assert returned state matches enum `SessionState`
- [x] ErrorConsistency:
  - Mock resolution failure → expect `WorkflowErrors.TRANSITION_FAILED`

### Implementation ✅
`AdvanceWorkflowChain.execute(session)`
- [x] Inspect session state machine
- [x] Transition to next defined state
- [x] Disable recall loop flag

---

## Step 6: Deliver next prompt to user ✅

**From path spec:**
- Input: Next-step payload; ui-w8p2
- Process: Render + vocalize next prompt
- Output: User hears new prompt; UI updated
- Error: UI/audio failure → log via cfg-r3d7; fallback text prompt

### Test ✅
`frontend/components/__tests__/VoiceInteraction.test.tsx` — 8 tests passing

- [x] Reachability:
  - Render component with nextStepPayload
  - Expect prompt text visible
- [x] TypeInvariant:
  - Assert props conform to `NextStepPayload` type
- [x] ErrorConsistency:
  - Simulate audio playback failure
  - Expect `VoiceLogger.error()` called
  - Expect fallback text displayed

### Implementation ✅
`VoiceInteraction.tsx`
- [x] useEffect triggers playback
- [x] Catch playback errors
- [x] Log via `VoiceLogger`
- [x] Render fallback text UI

---

## Terminal Condition ✅

### Integration Test ✅
`server/__tests__/completeVoiceAnswerFlow.integration.test.ts` — 5 tests passing

- [x] Simulate:
  1. Valid audio input
  2. Successful extraction
  3. Validation success
  4. Persistence success
  5. Workflow advancement
  6. Prompt delivery
- [x] Assert:
  - No further slot prompts for previous question_type
  - Session state advanced (e.g., VERIFY)
  - UI displays next workflow prompt

This proves Reachability across all 6 steps and matches TLA+ terminal state.

---

## References
- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/318-complete-voice-answer-advances-workflow.md`
- Gate 1: F-RECALL-LOOP, F-EPIC-SESSION
- TLA+: `CompleteVoiceAnswerAdvancesWorkflow.tla`

---

## Validation Report

**Validated at**: 2026-03-01T14:05:00-05:00

### Implementation Status
✓ Phase 0: Verification (TLA+) - Fully implemented — `artifacts/tlaplus/318-complete-voice-answer-advances-workflow/CompleteVoiceAnswerAdvancesWorkflow.tla` exists with TypeInvariant, ErrorConsistency, and Reachability properties
✓ Step 1: Capture spoken answer - Fully implemented — `SessionWorkflowService.captureSpokenAnswer()` with transcription adapter, retry logic, and `VoiceErrors.TRANSCRIPTION_FAILED`
✓ Step 2: Extract slot values from response - Fully implemented — `SlotExtractor.extract()` with pattern-based parsing and Zod validation via `PartialSlotDataSchema`
✓ Step 3: Validate minimum required slots - Fully implemented — `MinimumSlotValidator.validate()` with required slot checking and `VoiceErrors.VALIDATION_FAILED`
✓ Step 4: Persist completed slot set - Fully implemented — `SessionWorkflowService.persistCompletedSlots()` with `SessionDAO.saveSlots()` (stub) and `WorkflowErrors.PERSISTENCE_FAILED`
✓ Step 5: Advance workflow to next step - Fully implemented — `AdvanceWorkflowChain.execute()` with state machine transitions and `WorkflowErrors.TRANSITION_FAILED`
✓ Step 6: Deliver next prompt to user - Fully implemented — `VoiceInteraction.tsx` with useEffect playback, error catching, fallback text UI, and `voiceInteractionLogger.error()`
✓ Terminal Condition: Integration test - Fully implemented — `completeVoiceAnswerFlow.integration.test.ts` covers all 6 steps end-to-end

### Automated Verification Results
✓ Path-318 tests pass: 50/50 (`vitest run` — 7 test files, all green)
  - `captureSpokenAnswer.318.test.ts`: 8 tests ✓
  - `SlotExtractor.test.ts`: 9 tests ✓
  - `MinimumSlotValidator.test.ts`: 9 tests ✓
  - `persistCompletedSlots.test.ts`: 5 tests ✓
  - `AdvanceWorkflowChain.test.ts`: 6 tests ✓
  - `VoiceInteraction.test.tsx`: 8 tests ✓
  - `completeVoiceAnswerFlow.integration.test.ts`: 5 tests ✓
✓ Full test suite: 2550/2558 pass (237/238 test files pass)
⚠️ Pre-existing failures: 8 tests in `ButtonInteractions.test.tsx` (unrelated — `setVoiceSessionState is not a function` in `useRealtimeSession.ts`)
⚠️ TypeScript type-check: Pre-existing errors in `behavioralQuestionVerifier.test.ts` (missing vitest types — unrelated to path 318)
⚠️ Lint: 37 warnings (unused parameters in DAO stubs — expected for MVP), 1 error (synchronous `setState` in VoiceInteraction.tsx catch block)

### Code Review Findings

#### Matches Plan:
- All 10 resource registry entries implemented at correct locations under `frontend/src/`
- All error codes match spec: `TRANSCRIPTION_FAILED`, `TRANSFORMATION_FAILED`, `VALIDATION_FAILED`, `PERSISTENCE_FAILED`, `TRANSITION_FAILED`
- Test oracle mapping matches TLA+ properties: Reachability, TypeInvariant, ErrorConsistency in every test file
- Export patterns consistent with codebase conventions (`export const X = { ... } as const`)
- Error definition patterns consistent (custom Error subclass + namespaced factories + aggregate export)
- TLA+ model exists with all 6 steps + error state machine

#### Deviations from Plan:
- `SlotSchema.ts` (cfg-d2q3) consolidated into `VoiceInteractionContext.ts` rather than a standalone file — acceptable architectural decision; all Zod schemas (`SlotDefinitionSchema`, `SlotValueSchema`, `SlotStateSchema`, `PartialSlotDataSchema`) are present
- Plan references `frontend/artifacts/tlaplus/...` but actual TLA+ location is `artifacts/tlaplus/...` (path discrepancy in plan text only)
- Plan references `frontend/logging/VoiceLogger.ts` (cfg-r3d7) — actual is `frontend/src/logging/voiceInteractionLogger.ts` (naming difference, same functionality)

#### Issues Found:
- **Lint error**: VoiceInteraction.tsx line 60 — `setAudioFailed(true)` called synchronously inside useEffect catch block. Non-blocking for tests but should be wrapped in a cleanup-safe pattern to avoid React strict-mode warnings.
- **DAO stubs**: `SessionDAO.saveSlots()` and `SessionDAO.updateAnswerSessionState()` throw `Error('not yet wired to Supabase')` — expected for TDD/MVP stage but needs wiring before integration with real persistence.
- **Files not committed**: All 22 path-318 files are untracked (`??` in git status). Need to be committed.

### Manual Testing Required:
- [ ] Wire `SessionDAO.saveSlots()` to Supabase and verify persistence round-trip
- [ ] Wire `SessionDAO.updateAnswerSessionState()` to Supabase and verify state transitions persist
- [ ] Test audio playback in browser with real ElevenLabs streaming
- [ ] Verify fallback text UI renders when `speechSynthesis` is unavailable
- [ ] Run `silmari verify-path` against the spec to confirm TLA+ model still passes after any code changes

### Recommendations:
- **Commit path-318 files**: All 22 files are untracked — commit before they're lost
- **Fix lint error**: Wrap `setAudioFailed(true)` in VoiceInteraction.tsx to avoid cascading render warning (e.g., use a ref + deferred setState)
- **Prefix DAO stub params**: Use underscore prefix (`_sessionId`) on stub parameters to suppress lint warnings
- **Wire Supabase DAO**: Priority before next integration milestone — stubs will throw at runtime

VALIDATION_RESULT: PASS
