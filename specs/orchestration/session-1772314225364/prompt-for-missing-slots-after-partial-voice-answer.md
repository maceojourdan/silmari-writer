# PATH: prompt-for-missing-slots-after-partial-voice-answer

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User provides a partial spoken answer during an active voice interaction for a specific question_type where not all minimum required slots are filled.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `cfg-d2q3` | common_structure | Stores interaction context, question_type definitions, and slot state. |
| `cfg-g1u4` | shared_verifier | Validates slot values and required slot completion rules. |
| `cfg-j9w2` | shared_error_definitions | Defines recoverable and configuration error types for voice interaction. |
| `cfg-k3x7` | constant | Provides prompt templates and constant strings for follow-up questions. |
| `cfg-p4b8` | shared_logging | Logs voice processing and delivery errors. |

## Steps

1. **Capture spoken input**
   - Input: Active voice interaction context containing question_type and current slot state from cfg-d2q3 (common_structure); raw audio stream from user.
   - Process: Transforms the raw spoken audio into a structured partial answer payload associated with the active question_type.
   - Output: Structured partial slot data mapped to the current interaction context.
   - Error: If speech recognition fails or produces empty output, return a recoverable error defined in cfg-j9w2 (shared_error_definitions) and trigger a clarification prompt (max 2 retries).

2. **Update slot state**
   - Input: Structured partial slot data and existing interaction slot state from cfg-d2q3 (common_structure).
   - Process: Merges newly extracted slot values into the existing slot state for the current question_type without overwriting previously confirmed slots.
   - Output: Updated slot state reflecting filled and unfilled required slots.
   - Error: If slot values violate validation rules, raise a validation error via cfg-g1u4 (shared_verifier) and prompt the user to restate the invalid slot value.

3. **Validate minimum required slots**
   - Input: Updated slot state and question_type definition including minimum required slots from cfg-d2q3 (common_structure).
   - Process: Evaluates whether all minimum required slots for the current question_type are filled.
   - Output: Validation result indicating missing required slots (if any).
   - Error: If question_type configuration is missing required slot definitions, raise a configuration error using cfg-j9w2 (shared_error_definitions) and terminate interaction with an apologetic message.

4. **Generate follow-up prompt**
   - Input: List of missing required slots and question_type metadata from cfg-d2q3 (common_structure); prompt templates from cfg-k3x7 (constant).
   - Process: Constructs a context-aware follow-up voice question that explicitly requests the missing required slot information.
   - Output: Textual follow-up prompt ready for voice synthesis.
   - Error: If no prompt template exists for the missing slot, mark as [PROPOSED: slot-specific voice prompt template resource] and fall back to a generic clarification prompt.

5. **Deliver voice follow-up**
   - Input: Textual follow-up prompt and active voice session context.
   - Process: Converts the follow-up prompt into synthesized speech and delivers it through the active voice channel.
   - Output: Audible follow-up question played to the user requesting the missing required slot information.
   - Error: If voice synthesis or playback fails, log via cfg-p4b8 (shared_logging) and present a fallback text-based prompt if supported by the channel.

## Terminal Condition

User hears a follow-up voice prompt explicitly requesting the missing required slot information for the current question_type.

## Feedback Loops

If speech recognition or slot extraction fails, the system re-prompts the user to clarify the last answer, with a maximum of 2 retries before escalating to a generic help prompt.
