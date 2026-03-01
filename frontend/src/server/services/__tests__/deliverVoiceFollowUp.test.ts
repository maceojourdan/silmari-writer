/**
 * deliverVoiceFollowUp.test.ts - Step 5: Deliver voice follow-up
 *
 * TLA+ Properties:
 * - Reachability: Mock speak() success → deliveryStatus = 'played'
 * - TypeInvariant: Return type conforms to VoiceDeliveryResult schema
 * - ErrorConsistency: Mock speak() failure → logger called, fallbackTextPrompt returned
 *
 * Resource: db-h2s4 (service)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  VoiceDeliveryResultSchema,
  BEHAVIORAL_QUESTION_TYPE,
} from '@/server/data_structures/VoiceInteractionContext';
import type { VoiceInteractionContext } from '@/server/data_structures/VoiceInteractionContext';

// Mock the recall voice logger
vi.mock('@/server/logging/recallVoiceLogger', () => ({
  recallVoiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { VoiceRecallService } from '../VoiceRecallService';
import type { VoiceSynthesisClient } from '../VoiceRecallService';
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
// Tests
// ---------------------------------------------------------------------------

describe('VoiceRecallService.deliverVoiceFollowUp — Step 5: Deliver voice follow-up', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return deliveryStatus "played" on successful synthesis', async () => {
      const context = createContext();
      const promptText = 'What was the outcome?';
      const client: VoiceSynthesisClient = {
        speak: vi.fn().mockResolvedValue({ played: true }),
      };

      const result = await VoiceRecallService.deliverVoiceFollowUp(context, promptText, client);

      expect(result.deliveryStatus).toBe('played');
    });

    it('should call speak with prompt text and session ID', async () => {
      const context = createContext();
      const promptText = 'Tell me about the obstacles.';
      const speakSpy = vi.fn().mockResolvedValue({ played: true });
      const client: VoiceSynthesisClient = { speak: speakSpy };

      await VoiceRecallService.deliverVoiceFollowUp(context, promptText, client);

      expect(speakSpy).toHaveBeenCalledOnce();
      expect(speakSpy).toHaveBeenCalledWith(promptText, context.sessionId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result conforming to VoiceDeliveryResult schema on success', async () => {
      const context = createContext();
      const client: VoiceSynthesisClient = {
        speak: vi.fn().mockResolvedValue({ played: true }),
      };

      const result = await VoiceRecallService.deliverVoiceFollowUp(
        context, 'What was the outcome?', client,
      );

      const parsed = VoiceDeliveryResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return result conforming to VoiceDeliveryResult schema on failure', async () => {
      const context = createContext();
      const client: VoiceSynthesisClient = {
        speak: vi.fn().mockRejectedValue(new Error('Synthesis failed')),
      };

      const result = await VoiceRecallService.deliverVoiceFollowUp(
        context, 'What was the outcome?', client,
      );

      const parsed = VoiceDeliveryResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log error when speak() throws', async () => {
      const context = createContext();
      const client: VoiceSynthesisClient = {
        speak: vi.fn().mockRejectedValue(new Error('Synthesis engine down')),
      };

      await VoiceRecallService.deliverVoiceFollowUp(
        context, 'What was the outcome?', client,
      );

      expect(mockLogger.error).toHaveBeenCalledWith(
        'Voice follow-up delivery failed',
        expect.any(Error),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });

    it('should return fallbackTextPrompt when speak() fails', async () => {
      const context = createContext();
      const promptText = 'What was the outcome?';
      const client: VoiceSynthesisClient = {
        speak: vi.fn().mockRejectedValue(new Error('Network error')),
      };

      const result = await VoiceRecallService.deliverVoiceFollowUp(
        context, promptText, client,
      );

      expect(result.deliveryStatus).toBe('fallback_text');
      expect(result.fallbackTextPrompt).toBe(promptText);
    });

    it('should not log error on successful delivery', async () => {
      const context = createContext();
      const client: VoiceSynthesisClient = {
        speak: vi.fn().mockResolvedValue({ played: true }),
      };

      await VoiceRecallService.deliverVoiceFollowUp(
        context, 'What was the outcome?', client,
      );

      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });
});
