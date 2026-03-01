# PATH: complete-required-slots-and-end-recall-loop

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User provides additional spoken input after being prompted for missing required slots for a question_type

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `cfg-d2q3` | common_structure | Stores and updates the recall session state and slot values for the question_type. |
| `cfg-f7s8` | data_type | Defines required slot schemas and constraints for the question_type. |
| `cfg-g1u4` | shared_verifier | Validates that all required slots are present and conform to rules. |
| `cfg-j9w2` | shared_error_definitions | Provides structured error types for parsing, validation, and state errors. |
| `cfg-p4b8` | shared_logging | Logs state transitions and errors during recall completion. |

## Steps

1. **Capture Additional Spoken Input**
   - Input: Raw spoken utterance from user and active recall state for the current question_type stored in common structure (cfg-d2q3)
   - Process: Accept the spoken input and associate it with the currently active question_type recall session.
   - Output: Structured spoken input event linked to the active question_type session.
   - Error: If no active recall session exists, return a structured error indicating invalid recall state (cfg-j9w2).

2. **Transform Utterance Into Slot Values**
   - Input: Structured spoken input event and slot schema definition from shared data type (cfg-f7s8)
   - Process: Convert the utterance into candidate slot-value pairs aligned with the required slot definitions for the question_type.
   - Output: Extracted slot-value pairs mapped to required slot identifiers.
   - Error: If transformation fails or produces no recognizable slots, return a structured parsing error (cfg-j9w2) and re-prompt within allowed retry limit.

3. **Merge With Existing Recall State**
   - Input: Extracted slot-value pairs and existing partial slot state stored in common structure (cfg-d2q3)
   - Process: Update the recall state by filling previously missing required slots with the newly extracted values.
   - Output: Updated slot state reflecting newly filled required slots.
   - Error: If slot identifiers do not match the question_type schema, reject the update and emit a validation error (cfg-j9w2).

4. **Validate Required Slot Completion**
   - Input: Updated slot state and required slot validation rules from shared verifier (cfg-g1u4)
   - Process: Evaluate whether all required slots for the question_type are now present and valid.
   - Output: Validation result indicating completion status.
   - Error: If validation rules fail for any slot value, emit a validation error (cfg-j9w2) and continue recall within retry limit.

5. **Confirm Completion And Terminate Recall Loop**
   - Input: Validation result confirming all required slots are complete and active recall session state (cfg-d2q3)
   - Process: Mark the recall loop for the question_type as completed and generate a user-facing confirmation message.
   - Output: Confirmation response delivered to the user and recall loop state set to inactive for the question_type.
   - Error: If state update fails, emit a structured state-transition error (cfg-j9w2) and log via shared logging (cfg-p4b8).

## Terminal Condition

User hears and/or sees a confirmation message that all required information for the question_type has been collected and the system stops prompting for additional slots

## Feedback Loops

If after merging new input required slots are still missing, the recall loop repeats with a maximum of 3 total prompt cycles per question_type before emitting a structured incomplete-information error (cfg-j9w2).
