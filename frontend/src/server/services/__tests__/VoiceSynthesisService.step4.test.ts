/**
 * VoiceSynthesisService.step4.test.ts - Step 4: Synthesize and stream audio
 *
 * TLA+ Properties:
 * - Reachability: mock voice client success → streamAudio called once, transcript captured
 * - TypeInvariant: transcript returned as string
 * - ErrorConsistency:
 *     - mock failure twice then success → success after retry
 *     - mock failure 3 times → VoiceErrors.SYNTHESIS_FAILED
 *     - logger called each failure
 *
 * Resource: (service)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import type { SpeechSynthesisRequest } from '@/server/data_structures/VoiceEvent';

// Mock the voice logger
vi.mock('@/server/logging/voiceLogger', () => ({
  voiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { VoiceSynthesisService } from '../VoiceSynthesisService';
import type { VoiceClient } from '../VoiceSynthesisService';
import { voiceLogger } from '@/server/logging/voiceLogger';

const mockLogger = vi.mocked(voiceLogger);

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const validRequest: SpeechSynthesisRequest = {
  text: 'Hello world',
  voiceId: 'alloy',
  sessionId: validSessionId,
};

function createMockClient(responses: Array<{ transcript: string } | Error>): VoiceClient {
  let callCount = 0;
  return {
    async synthesize(_request: SpeechSynthesisRequest): Promise<{ transcript: string }> {
      const response = responses[callCount++];
      if (response instanceof Error) {
        throw response;
      }
      return response;
    },
  };
}

describe('VoiceSynthesisService.synthesizeAndStream — Step 4: Synthesize and stream audio', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return transcript on successful synthesis', async () => {
      const client = createMockClient([{ transcript: 'Hello world' }]);

      const result = await VoiceSynthesisService.synthesizeAndStream(validRequest, client);

      expect(result).toBe('Hello world');
    });

    it('should call voice client synthesize method', async () => {
      const synthesizeSpy = vi.fn().mockResolvedValue({ transcript: 'Hello world' });
      const client: VoiceClient = { synthesize: synthesizeSpy };

      await VoiceSynthesisService.synthesizeAndStream(validRequest, client);

      expect(synthesizeSpy).toHaveBeenCalledOnce();
      expect(synthesizeSpy).toHaveBeenCalledWith(validRequest);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return transcript as a string', async () => {
      const client = createMockClient([{ transcript: 'Synthesized text output' }]);

      const result = await VoiceSynthesisService.synthesizeAndStream(validRequest, client);

      expect(typeof result).toBe('string');
    });

    it('should return non-empty transcript', async () => {
      const client = createMockClient([{ transcript: 'Non-empty result' }]);

      const result = await VoiceSynthesisService.synthesizeAndStream(validRequest, client);

      expect(result.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should succeed after 2 failures followed by success (retry works)', async () => {
      const client = createMockClient([
        new Error('Attempt 1 failed'),
        new Error('Attempt 2 failed'),
        { transcript: 'Recovered transcript' },
      ]);

      const result = await VoiceSynthesisService.synthesizeAndStream(validRequest, client);

      expect(result).toBe('Recovered transcript');
    });

    it('should throw SYNTHESIS_FAILED after 3 consecutive failures', async () => {
      const client = createMockClient([
        new Error('Attempt 1 failed'),
        new Error('Attempt 2 failed'),
        new Error('Attempt 3 failed'),
      ]);

      try {
        await VoiceSynthesisService.synthesizeAndStream(validRequest, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('SYNTHESIS_FAILED');
        expect((e as VoiceError).statusCode).toBe(502);
        expect((e as VoiceError).retryable).toBe(true);
      }
    });

    it('should log each failure attempt', async () => {
      const client = createMockClient([
        new Error('Attempt 1 failed'),
        new Error('Attempt 2 failed'),
        new Error('Attempt 3 failed'),
      ]);

      try {
        await VoiceSynthesisService.synthesizeAndStream(validRequest, client);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(3);
    });

    it('should log with session context on each failure', async () => {
      const client = createMockClient([
        new Error('Failed'),
        { transcript: 'OK' },
      ]);

      await VoiceSynthesisService.synthesizeAndStream(validRequest, client);

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('attempt 1'),
        expect.any(Error),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });

    it('should succeed on first attempt without logging errors', async () => {
      const client = createMockClient([{ transcript: 'First try success' }]);

      await VoiceSynthesisService.synthesizeAndStream(validRequest, client);

      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });
});
