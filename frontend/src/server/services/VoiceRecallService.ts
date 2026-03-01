/**
 * VoiceRecallService - Handles the voice recall loop for capturing spoken
 * answers, updating slot state, validating required slots, generating
 * follow-up prompts, and delivering voice follow-ups.
 *
 * Resource: db-h2s4 (service)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import {
  PartialSlotDataSchema,
  MinimumSlotValidationResultSchema,
  VoiceDeliveryResultSchema,
} from '@/server/data_structures/VoiceInteractionContext';
import type {
  VoiceInteractionContext,
  PartialSlotData,
  SlotState,
  SlotValue,
  MinimumSlotValidationResult,
  VoiceDeliveryResult,
} from '@/server/data_structures/VoiceInteractionContext';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';
import { SlotVerifier } from '@/server/verifiers/SlotVerifier';
import { buildFollowUpPrompt } from '@/server/constants/VoicePromptTemplates';
import { recallVoiceLogger } from '@/server/logging/recallVoiceLogger';

// ---------------------------------------------------------------------------
// Transcription Client Interface (mockable)
// ---------------------------------------------------------------------------

export interface TranscriptionClient {
  transcribe(audioBlob: Blob): Promise<{ transcript: string }>;
}

// ---------------------------------------------------------------------------
// Voice Synthesis Client Interface (mockable)
// ---------------------------------------------------------------------------

export interface VoiceSynthesisClient {
  speak(text: string, sessionId: string): Promise<{ played: boolean }>;
}

// ---------------------------------------------------------------------------
// Default clients (stubs — not yet wired to ElevenLabs)
// ---------------------------------------------------------------------------

const defaultTranscriptionClient: TranscriptionClient = {
  async transcribe(_audioBlob: Blob): Promise<{ transcript: string }> {
    throw new Error('TranscriptionClient.transcribe not yet wired to ElevenLabs SDK');
  },
};

const defaultVoiceSynthesisClient: VoiceSynthesisClient = {
  async speak(_text: string, _sessionId: string): Promise<{ played: boolean }> {
    throw new Error('VoiceSynthesisClient.speak not yet wired to ElevenLabs SDK');
  },
};

// ---------------------------------------------------------------------------
// Simple deterministic slot extractor
// ---------------------------------------------------------------------------

/**
 * Extracts slot values from transcript text using simple pattern matching.
 * This is a deterministic extractor for now — will be replaced with LLM-based
 * extraction in a future path.
 */
function extractSlotsFromTranscript(
  transcript: string,
  slotNames: string[],
): PartialSlotData {
  const slots: PartialSlotData['slots'] = [];
  const lowerTranscript = transcript.toLowerCase();

  for (const slotName of slotNames) {
    switch (slotName) {
      case 'objective': {
        // Look for objective-related patterns
        const objectivePatterns = [
          /(?:my )?(?:objective|goal|aim|purpose) (?:was|is) (?:to )?(.+?)(?:\.|$)/i,
          /(?:i )?(?:wanted|needed|tried) to (.+?)(?:\.|$)/i,
        ];
        for (const pattern of objectivePatterns) {
          const match = transcript.match(pattern);
          if (match?.[1]) {
            slots.push({ name: 'objective', value: match[1].trim() });
            break;
          }
        }
        break;
      }
      case 'actions': {
        // Look for action-related patterns
        const actionPatterns = [
          /(?:i )?(?:took|did|performed|made) (?:these |the following )?(?:actions?|steps?):?\s*(.+?)(?:\.|$)/i,
          /(?:actions?|steps?):?\s*(.+?)(?:\.|$)/i,
        ];
        for (const pattern of actionPatterns) {
          const match = transcript.match(pattern);
          if (match?.[1]) {
            const actions = match[1]
              .split(/,|;| and /)
              .map((a) => a.trim())
              .filter((a) => a.length > 0);
            if (actions.length > 0) {
              slots.push({ name: 'actions', value: actions });
              break;
            }
          }
        }
        break;
      }
      case 'obstacles': {
        const obstaclePatterns = [
          /(?:obstacle|challenge|difficulty|problem|issue)s? (?:was|were|included?):?\s*(.+?)(?:\.|$)/i,
          /(?:i )?(?:faced|encountered|dealt with):?\s*(.+?)(?:\.|$)/i,
        ];
        for (const pattern of obstaclePatterns) {
          const match = transcript.match(pattern);
          if (match?.[1]) {
            const obstacles = match[1]
              .split(/,|;| and /)
              .map((o) => o.trim())
              .filter((o) => o.length > 0);
            if (obstacles.length > 0) {
              slots.push({ name: 'obstacles', value: obstacles });
              break;
            }
          }
        }
        break;
      }
      case 'outcome': {
        const outcomePatterns = [
          /(?:the )?(?:outcome|result|end result) (?:was|is):?\s*(.+?)(?:\.|$)/i,
          /(?:we |i )?(?:achieved|accomplished|delivered|resulted in):?\s*(.+?)(?:\.|$)/i,
        ];
        for (const pattern of outcomePatterns) {
          const match = transcript.match(pattern);
          if (match?.[1]) {
            slots.push({ name: 'outcome', value: match[1].trim() });
            break;
          }
        }
        break;
      }
      case 'roleClarity': {
        const rolePatterns = [
          /(?:my )?(?:role|responsibility|position) (?:was|is):?\s*(.+?)(?:\.|$)/i,
          /(?:i was |i am )?(?:responsible for|in charge of|the lead on):?\s*(.+?)(?:\.|$)/i,
        ];
        for (const pattern of rolePatterns) {
          const match = transcript.match(pattern);
          if (match?.[1]) {
            slots.push({ name: 'roleClarity', value: match[1].trim() });
            break;
          }
        }
        break;
      }
      default: {
        // For unknown slot names, check if the transcript contains the slot name keyword
        if (lowerTranscript.includes(slotName.toLowerCase())) {
          slots.push({ name: slotName, value: transcript.trim() });
        }
        break;
      }
    }
  }

  return { slots };
}

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const VoiceRecallService = {
  // -------------------------------------------------------------------------
  // Step 1: Capture spoken input
  // -------------------------------------------------------------------------

  /**
   * Transforms raw spoken audio into structured partial answer payload.
   *
   * @param context - Active voice interaction context
   * @param audioBlob - Raw audio data from user
   * @param client - Transcription client (mockable)
   * @returns PartialSlotData with extracted slot values
   * @throws VoiceError(VOICE_RECOGNITION_FAILED) on empty/failed transcription
   */
  async captureSpokenInput(
    context: VoiceInteractionContext,
    audioBlob: Blob,
    client: TranscriptionClient = defaultTranscriptionClient,
  ): Promise<PartialSlotData> {
    let transcript: string;

    try {
      const result = await client.transcribe(audioBlob);
      transcript = result.transcript;
    } catch (error) {
      recallVoiceLogger.error('Transcription client failed', error, {
        sessionId: context.sessionId,
        retryCount: context.retryCount,
      });

      if (context.retryCount >= context.maxRetries) {
        throw VoiceErrors.VOICE_RECOGNITION_FAILED(
          'Speech recognition failed after maximum retries — escalating',
        );
      }

      const err = VoiceErrors.VOICE_RECOGNITION_FAILED(
        'Speech recognition failed',
      );
      throw err;
    }

    // Empty transcript → recoverable error with retry tracking
    if (!transcript || transcript.trim() === '') {
      recallVoiceLogger.warn('Empty transcript received', {
        sessionId: context.sessionId,
        retryCount: context.retryCount,
      });

      if (context.retryCount >= context.maxRetries) {
        // Escalation: max retries exceeded, non-retryable
        const err = VoiceErrors.VOICE_RECOGNITION_FAILED(
          'Speech recognition returned empty output after maximum retries — escalating',
        );
        err.retryable = false;
        throw err;
      }

      // Recoverable: can retry
      throw VoiceErrors.VOICE_RECOGNITION_FAILED(
        'Speech recognition returned empty output',
      );
    }

    // Extract slot values from transcript
    const slotNames = context.questionType.slots.map((s) => s.name);
    const partialData = extractSlotsFromTranscript(transcript, slotNames);

    // If no slots extracted, still return what we have — the transcript had content
    // but maybe the extractor couldn't parse it. Return at least a raw extraction.
    if (partialData.slots.length === 0) {
      // Fallback: assign the full transcript to the first unfilled required slot
      const filledSlotNames = context.slotState.slots.map((s) => s.name);
      const firstUnfilled = context.questionType.minimumRequiredSlots.find(
        (name) => !filledSlotNames.includes(name),
      );

      if (firstUnfilled) {
        const def = context.questionType.slots.find((s) => s.name === firstUnfilled);
        const value = def?.type === 'string_array'
          ? [transcript.trim()]
          : transcript.trim();

        partialData.slots.push({ name: firstUnfilled, value });
      }
    }

    // Validate against Zod schema
    const parsed = PartialSlotDataSchema.safeParse(partialData);
    if (!parsed.success) {
      recallVoiceLogger.error('Extracted slot data failed schema validation', parsed.error, {
        sessionId: context.sessionId,
      });
      throw VoiceErrors.VOICE_RECOGNITION_FAILED(
        'Could not extract valid slot data from transcript',
      );
    }

    recallVoiceLogger.info('Captured spoken input successfully', {
      sessionId: context.sessionId,
      extractedSlots: parsed.data.slots.map((s) => s.name),
    });

    return parsed.data;
  },

  // -------------------------------------------------------------------------
  // Step 2: Update slot state
  // -------------------------------------------------------------------------

  /**
   * Merges new slot values into existing slot state without overwriting
   * confirmed slots.
   *
   * @param context - Voice interaction context with current slot state
   * @param partialData - Newly extracted partial slot data
   * @returns Updated slot state
   * @throws VoiceError(SLOT_VALIDATION_FAILED) if values violate validation rules
   */
  updateSlotState(
    context: VoiceInteractionContext,
    partialData: PartialSlotData,
  ): SlotState {
    const existingSlots = [...context.slotState.slots];

    for (const newSlot of partialData.slots) {
      // Check if this slot is already confirmed — do not overwrite
      const existingIndex = existingSlots.findIndex((s) => s.name === newSlot.name);
      if (existingIndex !== -1 && existingSlots[existingIndex].confirmed) {
        recallVoiceLogger.info(`Skipping confirmed slot "${newSlot.name}"`, {
          sessionId: context.sessionId,
        });
        continue;
      }

      // Validate the new value
      const definition = context.questionType.slots.find((s) => s.name === newSlot.name);
      if (definition) {
        const slotValue: SlotValue = {
          name: newSlot.name,
          value: newSlot.value,
          confirmed: false,
        };

        const validationResult = SlotVerifier.validateSlotValue(slotValue, definition);
        if (!validationResult.valid) {
          throw VoiceErrors.SLOT_VALIDATION_FAILED(
            `Invalid value for slot "${newSlot.name}": ${Object.values(validationResult.errors).join('; ')}`,
          );
        }
      }

      // Merge immutably
      const updatedSlot: SlotValue = {
        name: newSlot.name,
        value: newSlot.value,
        confirmed: false,
      };

      if (existingIndex !== -1) {
        existingSlots[existingIndex] = updatedSlot;
      } else {
        existingSlots.push(updatedSlot);
      }
    }

    return { slots: existingSlots };
  },

  // -------------------------------------------------------------------------
  // Step 3: Validate minimum required slots
  // -------------------------------------------------------------------------

  /**
   * Evaluates whether all minimum required slots are filled.
   *
   * @param context - Voice interaction context with updated slot state
   * @returns Validation result with missing and filled slots
   * @throws VoiceError(CONFIGURATION_ERROR) if question_type lacks minimumRequiredSlots
   */
  validateMinimumRequiredSlots(
    context: VoiceInteractionContext,
  ): MinimumSlotValidationResult {
    if (
      !context.questionType.minimumRequiredSlots ||
      context.questionType.minimumRequiredSlots.length === 0
    ) {
      throw VoiceErrors.CONFIGURATION_ERROR(
        'Question type is missing minimumRequiredSlots definition',
      );
    }

    const filledSlotNames = context.slotState.slots
      .filter((s) => {
        if (typeof s.value === 'string') return s.value.trim() !== '';
        if (Array.isArray(s.value)) return s.value.length > 0;
        return false;
      })
      .map((s) => s.name);

    const missingSlots = context.questionType.minimumRequiredSlots.filter(
      (name) => !filledSlotNames.includes(name),
    );

    const result: MinimumSlotValidationResult = {
      valid: missingSlots.length === 0,
      missingSlots,
      filledSlots: filledSlotNames,
    };

    // Validate output schema
    MinimumSlotValidationResultSchema.parse(result);

    return result;
  },

  // -------------------------------------------------------------------------
  // Step 4: Generate follow-up prompt
  // -------------------------------------------------------------------------

  /**
   * Constructs a context-aware follow-up voice prompt for missing slots.
   *
   * @param context - Voice interaction context
   * @param missingSlots - List of missing slot names
   * @returns Textual follow-up prompt
   */
  generateFollowUpPrompt(
    _context: VoiceInteractionContext,
    missingSlots: string[],
  ): string {
    return buildFollowUpPrompt(missingSlots);
  },

  // -------------------------------------------------------------------------
  // Step 5: Deliver voice follow-up
  // -------------------------------------------------------------------------

  /**
   * Synthesizes and delivers a voice follow-up prompt.
   *
   * @param context - Voice interaction context
   * @param promptText - Text to synthesize and deliver
   * @param client - Voice synthesis client (mockable)
   * @returns VoiceDeliveryResult
   */
  async deliverVoiceFollowUp(
    context: VoiceInteractionContext,
    promptText: string,
    client: VoiceSynthesisClient = defaultVoiceSynthesisClient,
  ): Promise<VoiceDeliveryResult> {
    try {
      const result = await client.speak(promptText, context.sessionId);

      if (result.played) {
        const deliveryResult: VoiceDeliveryResult = {
          deliveryStatus: 'played',
          promptText,
        };

        VoiceDeliveryResultSchema.parse(deliveryResult);

        recallVoiceLogger.info('Voice follow-up delivered successfully', {
          sessionId: context.sessionId,
        });

        return deliveryResult;
      }

      // Synthesis returned but playback didn't happen — fallback
      const fallbackResult: VoiceDeliveryResult = {
        deliveryStatus: 'fallback_text',
        promptText,
        fallbackTextPrompt: promptText,
      };

      VoiceDeliveryResultSchema.parse(fallbackResult);
      return fallbackResult;
    } catch (error) {
      recallVoiceLogger.error('Voice follow-up delivery failed', error, {
        sessionId: context.sessionId,
      });

      const fallbackResult: VoiceDeliveryResult = {
        deliveryStatus: 'fallback_text',
        promptText,
        fallbackTextPrompt: promptText,
      };

      VoiceDeliveryResultSchema.parse(fallbackResult);
      return fallbackResult;
    }
  },
} as const;
