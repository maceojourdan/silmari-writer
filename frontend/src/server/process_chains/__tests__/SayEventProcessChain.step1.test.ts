/**
 * SayEventProcessChain.step1.test.ts - Step 1: Intercept SAY event
 *
 * TLA+ Properties:
 * - Reachability: call handleEvent({ type: 'SAY', sessionId, text }) → forwarded to voice chain mock
 * - TypeInvariant: forwarded object matches SayEventWithSessionContext type
 * - ErrorConsistency: call with { type: 'SAY', text: null } →
 *     VoiceErrors.INVALID_SAY_PAYLOAD thrown, logger called, voice chain NOT invoked
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import type { SayEventWithSessionContext } from '@/server/data_structures/VoiceEvent';
import { SayEventWithSessionContextSchema } from '@/server/data_structures/VoiceEvent';

// Mock the voice logger
vi.mock('@/server/logging/voiceLogger', () => ({
  voiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock the voice chain handler (step 2+)
vi.mock('@/server/verifiers/SaySessionVerifier', () => ({
  SaySessionVerifier: {
    validateActiveSession: vi.fn().mockResolvedValue({
      sessionId: 'a1b2c3d4-e5f6-7890-abcd-ef1234567890',
      text: 'Hello world',
      validatedAt: new Date().toISOString(),
    }),
  },
}));

import { SayEventProcessChain } from '../SayEventProcessChain';
import { voiceLogger } from '@/server/logging/voiceLogger';
import { SaySessionVerifier } from '@/server/verifiers/SaySessionVerifier';

const mockLogger = vi.mocked(voiceLogger);
const mockVerifier = vi.mocked(SaySessionVerifier);

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

describe('SayEventProcessChain.handleEvent — Step 1: Intercept SAY event', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should forward valid SAY event to voice processing chain', async () => {
      const event = { type: 'SAY' as const, sessionId: validSessionId, text: 'Hello world' };

      const result = await SayEventProcessChain.handleEvent(event);

      expect(result).toBeDefined();
      expect(result.type).toBe('SAY');
      expect(result.sessionId).toBe(validSessionId);
      expect(result.text).toBe('Hello world');
      expect(result.sessionContext).toBeDefined();
    });

    it('should attach session context to forwarded event', async () => {
      const event = { type: 'SAY' as const, sessionId: validSessionId, text: 'Hello world' };

      const result = await SayEventProcessChain.handleEvent(event);

      expect(result.sessionContext).toEqual({
        sessionId: validSessionId,
        isActive: true,
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching SayEventWithSessionContext schema', async () => {
      const event = { type: 'SAY' as const, sessionId: validSessionId, text: 'Hello world' };

      const result = await SayEventProcessChain.handleEvent(event);

      // Validate against Zod schema
      const parseResult = SayEventWithSessionContextSchema.safeParse(result);
      expect(parseResult.success).toBe(true);
    });

    it('should have sessionId as a UUID string', async () => {
      const event = { type: 'SAY' as const, sessionId: validSessionId, text: 'Hello world' };

      const result = await SayEventProcessChain.handleEvent(event);

      expect(typeof result.sessionId).toBe('string');
      expect(result.sessionId).toMatch(
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i,
      );
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw INVALID_SAY_PAYLOAD when text is null', async () => {
      const event = { type: 'SAY', sessionId: validSessionId, text: null };

      try {
        await SayEventProcessChain.handleEvent(event as any);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('INVALID_SAY_PAYLOAD');
        expect((e as VoiceError).statusCode).toBe(400);
      }
    });

    it('should throw INVALID_SAY_PAYLOAD when sessionId is missing', async () => {
      const event = { type: 'SAY', text: 'Hello' };

      try {
        await SayEventProcessChain.handleEvent(event as any);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('INVALID_SAY_PAYLOAD');
      }
    });

    it('should throw INVALID_SAY_PAYLOAD when sessionId is not a UUID', async () => {
      const event = { type: 'SAY', sessionId: 'not-a-uuid', text: 'Hello' };

      try {
        await SayEventProcessChain.handleEvent(event as any);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('INVALID_SAY_PAYLOAD');
      }
    });

    it('should throw INVALID_SAY_PAYLOAD when text is empty string', async () => {
      const event = { type: 'SAY', sessionId: validSessionId, text: '' };

      try {
        await SayEventProcessChain.handleEvent(event as any);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('INVALID_SAY_PAYLOAD');
      }
    });

    it('should log error when payload is invalid', async () => {
      const event = { type: 'SAY', text: null };

      try {
        await SayEventProcessChain.handleEvent(event as any);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('INVALID_SAY_PAYLOAD'),
        expect.any(VoiceError),
        expect.any(Object),
      );
    });

    it('should NOT invoke voice chain when payload is invalid', async () => {
      const event = { type: 'SAY', text: null };

      try {
        await SayEventProcessChain.handleEvent(event as any);
      } catch {
        // expected
      }

      expect(mockVerifier.validateActiveSession).not.toHaveBeenCalled();
    });
  });
});
