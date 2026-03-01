/**
 * SayEventProcessChain.step5.test.ts - Step 5: Emit TRANSCRIPT_FINAL event
 *
 * TLA+ Properties:
 * - Reachability: call emitTranscriptFinal(transcript) → dispatch called with { type: 'TRANSCRIPT_FINAL', text }
 * - TypeInvariant: event matches TranscriptFinalEvent type
 * - ErrorConsistency:
 *     - mock dispatch fail twice then success → eventual success
 *     - mock fail 3 times → VoiceErrors.TRANSCRIPT_DISPATCH_FAILED
 *     - logger called
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import { TranscriptFinalEventSchema } from '@/server/data_structures/VoiceEvent';
import type { TranscriptFinalEvent } from '@/server/data_structures/VoiceEvent';

// Mock the voice logger
vi.mock('@/server/logging/voiceLogger', () => ({
  voiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SayEventProcessChain } from '../SayEventProcessChain';
import { voiceLogger } from '@/server/logging/voiceLogger';

const mockLogger = vi.mocked(voiceLogger);

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';
const sampleTranscript = 'Hello world transcript text';

describe('SayEventProcessChain.emitTranscriptFinal — Step 5: Emit TRANSCRIPT_FINAL event', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should dispatch TRANSCRIPT_FINAL event with correct payload', async () => {
      const dispatcher = vi.fn().mockResolvedValue(undefined);

      const result = await SayEventProcessChain.emitTranscriptFinal(
        sampleTranscript,
        validSessionId,
        dispatcher,
      );

      expect(dispatcher).toHaveBeenCalledOnce();
      expect(dispatcher).toHaveBeenCalledWith({
        type: 'TRANSCRIPT_FINAL',
        text: sampleTranscript,
        sessionId: validSessionId,
      });
      expect(result).toBeDefined();
    });

    it('should return the dispatched event', async () => {
      const dispatcher = vi.fn().mockResolvedValue(undefined);

      const result = await SayEventProcessChain.emitTranscriptFinal(
        sampleTranscript,
        validSessionId,
        dispatcher,
      );

      expect(result.type).toBe('TRANSCRIPT_FINAL');
      expect(result.text).toBe(sampleTranscript);
      expect(result.sessionId).toBe(validSessionId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return event matching TranscriptFinalEvent schema', async () => {
      const dispatcher = vi.fn().mockResolvedValue(undefined);

      const result = await SayEventProcessChain.emitTranscriptFinal(
        sampleTranscript,
        validSessionId,
        dispatcher,
      );

      const parseResult = TranscriptFinalEventSchema.safeParse(result);
      expect(parseResult.success).toBe(true);
    });

    it('should have type as literal TRANSCRIPT_FINAL', async () => {
      const dispatcher = vi.fn().mockResolvedValue(undefined);

      const result = await SayEventProcessChain.emitTranscriptFinal(
        sampleTranscript,
        validSessionId,
        dispatcher,
      );

      expect(result.type).toBe('TRANSCRIPT_FINAL');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should succeed after 2 dispatch failures followed by success', async () => {
      const dispatcher = vi.fn()
        .mockRejectedValueOnce(new Error('Dispatch attempt 1 failed'))
        .mockRejectedValueOnce(new Error('Dispatch attempt 2 failed'))
        .mockResolvedValueOnce(undefined);

      const result = await SayEventProcessChain.emitTranscriptFinal(
        sampleTranscript,
        validSessionId,
        dispatcher,
      );

      expect(result.text).toBe(sampleTranscript);
      expect(dispatcher).toHaveBeenCalledTimes(3);
    });

    it('should throw TRANSCRIPT_DISPATCH_FAILED after 3 consecutive failures', async () => {
      const dispatcher = vi.fn()
        .mockRejectedValueOnce(new Error('Fail 1'))
        .mockRejectedValueOnce(new Error('Fail 2'))
        .mockRejectedValueOnce(new Error('Fail 3'));

      try {
        await SayEventProcessChain.emitTranscriptFinal(
          sampleTranscript,
          validSessionId,
          dispatcher,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSCRIPT_DISPATCH_FAILED');
        expect((e as VoiceError).statusCode).toBe(502);
        expect((e as VoiceError).retryable).toBe(true);
      }
    });

    it('should log each dispatch failure', async () => {
      const dispatcher = vi.fn()
        .mockRejectedValueOnce(new Error('Fail 1'))
        .mockRejectedValueOnce(new Error('Fail 2'))
        .mockRejectedValueOnce(new Error('Fail 3'));

      try {
        await SayEventProcessChain.emitTranscriptFinal(
          sampleTranscript,
          validSessionId,
          dispatcher,
        );
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(3);
    });

    it('should log with session context on each failure', async () => {
      const dispatcher = vi.fn()
        .mockRejectedValueOnce(new Error('Failed'))
        .mockResolvedValueOnce(undefined);

      await SayEventProcessChain.emitTranscriptFinal(
        sampleTranscript,
        validSessionId,
        dispatcher,
      );

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('attempt 1'),
        expect.any(Error),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });

    it('should not log errors on first-attempt success', async () => {
      const dispatcher = vi.fn().mockResolvedValue(undefined);

      await SayEventProcessChain.emitTranscriptFinal(
        sampleTranscript,
        validSessionId,
        dispatcher,
      );

      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });
});
