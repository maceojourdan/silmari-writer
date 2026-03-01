# prompt-for-missing-slots-after-partial-voice-answer TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/317-prompt-for-missing-slots-after-partial-voice-answer.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- Reachability
- TypeInvariant
- ErrorConsistency

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/317-prompt-for-missing-slots-after-partial-voice-answer.md
```

Result (from verification_results_json):
- Result: **ALL PROPERTIES PASSED**
- States: 22 found, 11 distinct
- Exit code: 0

We will translate these properties directly into code-level tests per step.

---

## Tech Stack (Gate 2 – Option 1)
- Frontend/Backend: Next.js (App Router) + TypeScript
- Backend logic: Next.js API Routes / Server Actions
- Validation: Zod
- Voice: ElevenLabs SDK
- SMS (fallback channel reference only): Twilio SDK
- Testing: Vitest (or Vitest) + ts-Vitest

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation | Status |
|------|--------------|------------------------|--------|
| cfg-d2q3 | common_structure | `frontend/src/server/data_structures/VoiceInteractionContext.ts` | - [x] |
| cfg-g1u4 | shared_verifier | `frontend/src/server/verifiers/SlotVerifier.ts` | - [x] |
| cfg-j9w2 | shared_error_definitions | `frontend/src/server/error_definitions/VoiceErrors.ts` | - [x] |
| cfg-k3x7 | constant | `frontend/src/server/constants/VoicePromptTemplates.ts` | - [x] |
| cfg-p4b8 | shared_logging | `frontend/src/server/logging/recallVoiceLogger.ts` | - [x] |
| db-h2s4 | service | `frontend/src/server/services/VoiceRecallService.ts` | - [x] |
| api-m5g7 | endpoint | _(deferred — endpoint not yet needed for service layer)_ | |
| api-n8k2 | request_handler | _(deferred — handler not yet needed for service layer)_ | |

---

# Step 1: Capture spoken input - [x]

**From path spec:**
- Input: Active voice interaction context (cfg-d2q3) + raw audio stream.
- Process: Transform raw audio into structured partial answer payload for current question_type.
- Output: Structured partial slot data mapped to interaction context.
- Error: If speech recognition fails or empty output → recoverable error (cfg-j9w2) + clarification prompt (max 2 retries).

---

### Test - [x]
`frontend/src/server/services/__tests__/captureSpokenInput.test.ts` (8 tests passing)

**Reachability** - [x]
- Call `VoiceRecallService.captureSpokenInput(context, audioBlob)`
- Mock ElevenLabs transcript returning valid transcript.
- Assert returned `PartialSlotData`.

**TypeInvariant** - [x]
- Assert result conforms to `PartialSlotData` Zod schema.
- Assert slot keys belong to `question_type` definition.

**ErrorConsistency** - [x]
- Mock transcript = empty string.
- Expect `VoiceRecognitionError` from `VoiceErrors`.
- Assert retryCount incremented and `clarificationPrompt` returned.
- After 2 retries, assert escalation flag set.

---

### Implementation - [x]
`frontend/src/server/services/VoiceRecallService.ts`
- Method: `captureSpokenInput(context, audioBlob)`
- Use ElevenLabs SDK to transcribe.
- Map transcript → slot extraction (simple deterministic extractor for now).
- Validate with Zod schema from `VoiceInteractionContext`.
- Throw `VoiceRecognitionError` (cfg-j9w2) when empty.

---

# Step 2: Update slot state - [x]

**From path spec:**
- Input: Structured partial slot data + existing slot state.
- Process: Merge new values without overwriting confirmed slots.
- Output: Updated slot state.
- Error: Invalid slot value → validation error via cfg-g1u4.

---

### Test - [x]
`frontend/src/server/services/__tests__/updateSlotState.test.ts` (6 tests passing)

**Reachability** - [x]
- Provide existing state with confirmed `objective`.
- Provide partial with `actions`.
- Assert merged state contains both.

**TypeInvariant** - [x]
- Assert updated state matches `SlotState` schema.
- Confirm previously confirmed slot unchanged.

**ErrorConsistency** - [x]
- Provide invalid slot value (e.g., actions < 3 when minimum requires ≥3 at confirmation boundary).
- Mock `SlotVerifier.validateSlotValue` to throw.
- Expect `SlotValidationError`.

---

### Implementation - [x]
- Method: `updateSlotState(context, partialData)`
- Use `SlotVerifier` from `frontend/src/server/verifiers/SlotVerifier.ts`.
- Merge immutably.
- Do not overwrite `confirmed: true` slots.

---

# Step 3: Validate minimum required slots - [x]

**From path spec:**
- Input: Updated slot state + question_type definition.
- Process: Evaluate if minimum required slots filled.
- Output: Validation result with missing slots.
- Error: Missing required slot definitions → configuration error via cfg-j9w2.

---

### Test - [x]
`frontend/src/server/services/__tests__/validateMinimumSlots.test.ts` (4 tests passing)

**Reachability** - [x]
- Provide slot state missing `outcome`.
- Assert result `{ missingSlots: ['outcome'] }`.

**TypeInvariant** - [x]
- Assert output conforms to `MinimumSlotValidationResult` schema.

**ErrorConsistency** - [x]
- Provide question_type without `minimumRequiredSlots`.
- Expect `ConfigurationError` from `VoiceErrors`.

---

### Implementation - [x]
- Method: `validateMinimumRequiredSlots(context)`
- Compare slotState vs `question_type.minimumRequiredSlots`.
- Throw `ConfigurationError` if undefined.

---

# Step 4: Generate follow-up prompt - [x]

**From path spec:**
- Input: Missing slots + question_type metadata + prompt templates.
- Process: Construct context-aware follow-up question.
- Output: Textual follow-up prompt.
- Error: Missing template → fallback to generic clarification prompt.

---

### Test - [x]
`frontend/src/server/services/__tests__/generateFollowUpPrompt.test.ts` (6 tests passing)

**Reachability** - [x]
- Missing slot = `outcome`.
- Assert prompt includes slot-specific template from `VoicePromptTemplates`.

**TypeInvariant** - [x]
- Assert returned value is string.

**ErrorConsistency** - [x]
- Remove slot template from constants.
- Assert generic fallback prompt used.

---

### Implementation - [x]
- Method: `generateFollowUpPrompt(context, missingSlots)`
- Load templates from `frontend/src/server/constants/VoicePromptTemplates.ts`.
- If missing → use `GENERIC_CLARIFICATION_PROMPT`.

---

# Step 5: Deliver voice follow-up - [x]

**From path spec:**
- Input: Text prompt + active session context.
- Process: Synthesize speech + deliver via active voice channel.
- Output: Audible follow-up played.
- Error: If synthesis/playback fails → log via cfg-p4b8 + fallback text prompt.

---

### Test - [x]
`frontend/src/server/services/__tests__/deliverVoiceFollowUp.test.ts` (7 tests passing)

**Reachability** - [x]
- Mock ElevenLabs `speak()` success.
- Assert `deliveryStatus = 'played'`.

**TypeInvariant** - [x]
- Assert return type `VoiceDeliveryResult` schema.

**ErrorConsistency** - [x]
- Mock ElevenLabs throwing error.
- Assert logger called with error.
- Assert fallbackTextPrompt returned.

---

### Implementation - [x]
- Method: `deliverVoiceFollowUp(context, promptText)`
- Call ElevenLabs SDK.
- Wrap in try/catch.
- Log errors via `frontend/src/server/logging/recallVoiceLogger.ts`.
- Return fallback if failure.

---

# Terminal Condition - [x]

User hears a follow-up voice prompt explicitly requesting missing required slot information.

---

## Integration Test - [x]
`frontend/src/server/services/__tests__/promptForMissingSlots.integration.test.ts` (5 tests passing)

- [x] Start with context missing `outcome`.
- [x] Simulate partial answer filling only `objective`.
- [x] Run full flow:
  1. captureSpokenInput
  2. updateSlotState
  3. validateMinimumRequiredSlots
  4. generateFollowUpPrompt
  5. deliverVoiceFollowUp
- [x] Assert final result contains spoken follow-up referencing `outcome`.
- [x] Assert no state transition to VERIFY.

This proves:
- [x] Reachability: full path executable.
- [x] TypeInvariant: all step boundaries validated via schemas.
- [x] ErrorConsistency: forced transcript and synthesis failures behave as specified.

---

## References
- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/317-prompt-for-missing-slots-after-partial-voice-answer.md`
- Gate 1: F-RECALL-LOOP
- Gate 2: Option 1 – Next.js + Supabase + ElevenLabs
