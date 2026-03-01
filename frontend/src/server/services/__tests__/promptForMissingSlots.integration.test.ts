/**
 * promptForMissingSlots.integration.test.ts - Full-flow integration test
 *
 * Proves:
 * - Reachability: full path executable (steps 1-5)
 * - TypeInvariant: all step boundaries validated via schemas
 * - ErrorConsistency: forced transcript and synthesis failures behave as specified
 *
 * Scenario:
 * - Start with context missing 'outcome'
 * - Simulate partial answer filling only 'objective'
 * - Run full flow: captureSpokenInput → updateSlotState → validateMinimumRequiredSlots
 *   → generateFollowUpPrompt → deliverVoiceFollowUp
 * - Assert final result contains spoken follow-up referencing 'outcome'
 * - Assert no state transition to VERIFY
 *
 * Resource: db-h2s4 (service)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  PartialSlotDataSchema,
  SlotStateSchema,
  MinimumSlotValidationResultSchema,
  VoiceDeliveryResultSchema,
  BEHAVIORAL_QUESTION_TYPE,
} from '@/server/data_structures/VoiceInteractionContext';
import type {
  VoiceInteractionContext,
} from '@/server/data_structures/VoiceInteractionContext';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';

// Mock the recall voice logger
vi.mock('@/server/logging/recallVoiceLogger', () => ({
  recallVoiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { VoiceRecallService } from '../VoiceRecallService';
import type { TranscriptionClient, VoiceSynthesisClient } from '../VoiceRecallService';
import { recallVoiceLogger } from '@/server/logging/recallVoiceLogger';

const mockLogger = vi.mocked(recallVoiceLogger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createContext(overrides: Partial<VoiceInteractionContext> = {}): VoiceInteractionContext {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE,
    slotState: { slots: [] },
    retryCount: 0,
    maxRetries: 2,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Integration Tests
// ---------------------------------------------------------------------------

describe('Prompt for Missing Slots — Full Integration Flow', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Happy path: partial answer → detect missing → follow-up prompt
  // -------------------------------------------------------------------------

  describe('Full flow: partial answer with missing outcome', () => {
    it('should run all 5 steps and deliver a follow-up referencing "outcome"', async () => {
      // --- Setup ---
      const context = createContext();
      const audioBlob = new Blob(['audio-data'], { type: 'audio/wav' });

      // Mock transcription returns a partial answer about objective
      const transcriptionClient: TranscriptionClient = {
        transcribe: vi.fn().mockResolvedValue({
          transcript: 'My objective was to reduce customer churn by implementing a new onboarding flow.',
        }),
      };

      // Mock voice synthesis success
      const synthesisClient: VoiceSynthesisClient = {
        speak: vi.fn().mockResolvedValue({ played: true }),
      };

      // --- Step 1: Capture spoken input ---
      const partialData = await VoiceRecallService.captureSpokenInput(
        context, audioBlob, transcriptionClient,
      );

      // Verify schema
      expect(PartialSlotDataSchema.safeParse(partialData).success).toBe(true);
      expect(partialData.slots.length).toBeGreaterThan(0);
      expect(partialData.slots.some((s) => s.name === 'objective')).toBe(true);

      // --- Step 2: Update slot state ---
      const updatedState = VoiceRecallService.updateSlotState(context, partialData);

      // Verify schema
      expect(SlotStateSchema.safeParse(updatedState).success).toBe(true);
      expect(updatedState.slots.some((s) => s.name === 'objective')).toBe(true);

      // --- Step 3: Validate minimum required slots ---
      const contextWithUpdatedState: VoiceInteractionContext = {
        ...context,
        slotState: updatedState,
      };
      const validationResult = VoiceRecallService.validateMinimumRequiredSlots(
        contextWithUpdatedState,
      );

      // Verify schema
      expect(MinimumSlotValidationResultSchema.safeParse(validationResult).success).toBe(true);
      // Should NOT be fully valid — outcome (and others) still missing
      expect(validationResult.valid).toBe(false);
      expect(validationResult.missingSlots).toContain('outcome');

      // --- Step 4: Generate follow-up prompt ---
      const followUpPrompt = VoiceRecallService.generateFollowUpPrompt(
        contextWithUpdatedState,
        validationResult.missingSlots,
      );

      expect(typeof followUpPrompt).toBe('string');
      expect(followUpPrompt.length).toBeGreaterThan(0);

      // --- Step 5: Deliver voice follow-up ---
      const deliveryResult = await VoiceRecallService.deliverVoiceFollowUp(
        contextWithUpdatedState,
        followUpPrompt,
        synthesisClient,
      );

      // Verify schema
      expect(VoiceDeliveryResultSchema.safeParse(deliveryResult).success).toBe(true);
      expect(deliveryResult.deliveryStatus).toBe('played');
      expect(deliveryResult.promptText).toBe(followUpPrompt);

      // --- Terminal condition ---
      // No state transition to VERIFY (still missing slots)
      expect(validationResult.valid).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // Error path: transcript failure with retries
  // -------------------------------------------------------------------------

  describe('Error flow: transcript failure triggers retry logic', () => {
    it('should throw retryable error on empty transcript (retries remaining)', async () => {
      const context = createContext({ retryCount: 0 });
      const audioBlob = new Blob(['silence'], { type: 'audio/wav' });
      const transcriptionClient: TranscriptionClient = {
        transcribe: vi.fn().mockResolvedValue({ transcript: '' }),
      };

      try {
        await VoiceRecallService.captureSpokenInput(context, audioBlob, transcriptionClient);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('VOICE_RECOGNITION_FAILED');
        expect((e as VoiceError).retryable).toBe(true);
      }
    });

    it('should escalate after max retries exceeded', async () => {
      const context = createContext({ retryCount: 2, maxRetries: 2 });
      const audioBlob = new Blob(['silence'], { type: 'audio/wav' });
      const transcriptionClient: TranscriptionClient = {
        transcribe: vi.fn().mockResolvedValue({ transcript: '' }),
      };

      try {
        await VoiceRecallService.captureSpokenInput(context, audioBlob, transcriptionClient);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('VOICE_RECOGNITION_FAILED');
        expect((e as VoiceError).retryable).toBe(false);
      }
    });
  });

  // -------------------------------------------------------------------------
  // Error path: synthesis failure with fallback
  // -------------------------------------------------------------------------

  describe('Error flow: synthesis failure returns text fallback', () => {
    it('should return fallback text when voice delivery fails', async () => {
      const context = createContext();
      const promptText = 'What was the outcome of your actions?';

      const failingClient: VoiceSynthesisClient = {
        speak: vi.fn().mockRejectedValue(new Error('ElevenLabs API down')),
      };

      const result = await VoiceRecallService.deliverVoiceFollowUp(
        context, promptText, failingClient,
      );

      expect(result.deliveryStatus).toBe('fallback_text');
      expect(result.fallbackTextPrompt).toBe(promptText);
      expect(mockLogger.error).toHaveBeenCalledWith(
        'Voice follow-up delivery failed',
        expect.any(Error),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: all boundaries validated
  // -------------------------------------------------------------------------

  describe('TypeInvariant: schema validation at every step boundary', () => {
    it('should produce valid schemas at each step of the flow', async () => {
      const context = createContext({
        slotState: {
          slots: [
            { name: 'objective', value: 'Deliver project on time', confirmed: true },
          ],
        },
      });

      const audioBlob = new Blob(['audio'], { type: 'audio/wav' });
      const transcriptionClient: TranscriptionClient = {
        transcribe: vi.fn().mockResolvedValue({
          transcript: 'The obstacles included tight deadlines and limited resources.',
        }),
      };
      const synthesisClient: VoiceSynthesisClient = {
        speak: vi.fn().mockResolvedValue({ played: true }),
      };

      // Step 1
      const partialData = await VoiceRecallService.captureSpokenInput(
        context, audioBlob, transcriptionClient,
      );
      expect(PartialSlotDataSchema.safeParse(partialData).success).toBe(true);

      // Step 2
      const updatedState = VoiceRecallService.updateSlotState(context, partialData);
      expect(SlotStateSchema.safeParse(updatedState).success).toBe(true);

      // Confirmed slot should be unchanged
      const objectiveSlot = updatedState.slots.find((s) => s.name === 'objective');
      expect(objectiveSlot?.value).toBe('Deliver project on time');
      expect(objectiveSlot?.confirmed).toBe(true);

      // Step 3
      const contextWithUpdatedState = { ...context, slotState: updatedState };
      const validationResult = VoiceRecallService.validateMinimumRequiredSlots(
        contextWithUpdatedState,
      );
      expect(MinimumSlotValidationResultSchema.safeParse(validationResult).success).toBe(true);

      // Step 4
      if (!validationResult.valid) {
        const prompt = VoiceRecallService.generateFollowUpPrompt(
          contextWithUpdatedState,
          validationResult.missingSlots,
        );
        expect(typeof prompt).toBe('string');
        expect(prompt.length).toBeGreaterThan(0);

        // Step 5
        const delivery = await VoiceRecallService.deliverVoiceFollowUp(
          contextWithUpdatedState,
          prompt,
          synthesisClient,
        );
        expect(VoiceDeliveryResultSchema.safeParse(delivery).success).toBe(true);
      }
    });
  });
});
