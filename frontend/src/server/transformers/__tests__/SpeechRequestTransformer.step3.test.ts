/**
 * SpeechRequestTransformer.step3.test.ts - Step 3: Transform prompt to speech request
 *
 * TLA+ Properties:
 * - Reachability: call toSpeechRequest(validatedCommand) → structured payload { text, voiceId, sessionId }
 * - TypeInvariant: payload satisfies SpeechSynthesisRequest type
 * - ErrorConsistency: call with invalid text (empty string) → VoiceErrors.TRANSFORMATION_FAILED + logger called
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import { SpeechSynthesisRequestSchema } from '@/server/data_structures/VoiceEvent';
import type { ValidatedSayCommand } from '@/server/data_structures/VoiceEvent';

// Mock the voice logger
vi.mock('@/server/logging/voiceLogger', () => ({
  voiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SpeechRequestTransformer } from '../SpeechRequestTransformer';
import { voiceLogger } from '@/server/logging/voiceLogger';

const mockLogger = vi.mocked(voiceLogger);

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const validCommand: ValidatedSayCommand = {
  sessionId: validSessionId,
  text: 'Hello world',
  validatedAt: new Date().toISOString(),
};

describe('SpeechRequestTransformer.toSpeechRequest — Step 3: Transform prompt to speech request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return structured speech request payload', () => {
      const result = SpeechRequestTransformer.toSpeechRequest(validCommand);

      expect(result).toBeDefined();
      expect(result.text).toBe('Hello world');
      expect(result.voiceId).toBeDefined();
      expect(typeof result.voiceId).toBe('string');
      expect(result.sessionId).toBe(validSessionId);
    });

    it('should preserve original text in the request', () => {
      const command: ValidatedSayCommand = {
        ...validCommand,
        text: 'A longer speech text with special chars: 123!',
      };

      const result = SpeechRequestTransformer.toSpeechRequest(command);

      expect(result.text).toBe('A longer speech text with special chars: 123!');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should satisfy SpeechSynthesisRequest schema', () => {
      const result = SpeechRequestTransformer.toSpeechRequest(validCommand);

      const parseResult = SpeechSynthesisRequestSchema.safeParse(result);
      expect(parseResult.success).toBe(true);
    });

    it('should have voiceId as a non-empty string', () => {
      const result = SpeechRequestTransformer.toSpeechRequest(validCommand);

      expect(typeof result.voiceId).toBe('string');
      expect(result.voiceId.length).toBeGreaterThan(0);
    });

    it('should have sessionId as a UUID string', () => {
      const result = SpeechRequestTransformer.toSpeechRequest(validCommand);

      expect(result.sessionId).toMatch(
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i,
      );
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw TRANSFORMATION_FAILED when text is empty string', () => {
      const command: ValidatedSayCommand = {
        ...validCommand,
        text: '',
      };

      try {
        SpeechRequestTransformer.toSpeechRequest(command);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSFORMATION_FAILED');
        expect((e as VoiceError).statusCode).toBe(422);
      }
    });

    it('should throw TRANSFORMATION_FAILED when text is whitespace only', () => {
      const command: ValidatedSayCommand = {
        ...validCommand,
        text: '   ',
      };

      try {
        SpeechRequestTransformer.toSpeechRequest(command);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSFORMATION_FAILED');
      }
    });

    it('should log error when transformation fails', () => {
      const command: ValidatedSayCommand = {
        ...validCommand,
        text: '',
      };

      try {
        SpeechRequestTransformer.toSpeechRequest(command);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('TRANSFORMATION_FAILED'),
        expect.any(VoiceError),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });
  });
});
