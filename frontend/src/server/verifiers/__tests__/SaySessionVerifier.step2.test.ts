/**
 * SaySessionVerifier.step2.test.ts - Step 2: Validate session context
 *
 * TLA+ Properties:
 * - Reachability: call validateActiveSession(event) with active mock session → returns validated command
 * - TypeInvariant: return type matches ValidatedSayCommand
 * - ErrorConsistency:
 *     - inactive session → VoiceErrors.SESSION_INACTIVE
 *     - malformed schema → VoiceErrors.INVALID_SAY_PAYLOAD (via step 1 guard)
 *     - logger called in both
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SaySessionVerifier } from '../SaySessionVerifier';
import type { SessionStore } from '../SaySessionVerifier';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import { ValidatedSayCommandSchema } from '@/server/data_structures/VoiceEvent';
import type { SayEventWithSessionContext } from '@/server/data_structures/VoiceEvent';

// Mock the voice logger
vi.mock('@/server/logging/voiceLogger', () => ({
  voiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { voiceLogger } from '@/server/logging/voiceLogger';

const mockLogger = vi.mocked(voiceLogger);

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const validEvent: SayEventWithSessionContext = {
  type: 'SAY',
  sessionId: validSessionId,
  text: 'Hello world',
  sessionContext: {
    sessionId: validSessionId,
    isActive: true,
  },
};

const activeSessionStore: SessionStore = {
  async isActive(_sessionId: string): Promise<boolean> {
    return true;
  },
};

const inactiveSessionStore: SessionStore = {
  async isActive(_sessionId: string): Promise<boolean> {
    return false;
  },
};

const failingSessionStore: SessionStore = {
  async isActive(_sessionId: string): Promise<boolean> {
    throw new Error('Database connection lost');
  },
};

describe('SaySessionVerifier.validateActiveSession — Step 2: Validate session context', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return validated command when session is active', async () => {
      const result = await SaySessionVerifier.validateActiveSession(validEvent, activeSessionStore);

      expect(result).toBeDefined();
      expect(result.sessionId).toBe(validSessionId);
      expect(result.text).toBe('Hello world');
      expect(result.validatedAt).toBeDefined();
    });

    it('should include validatedAt timestamp in ISO format', async () => {
      const result = await SaySessionVerifier.validateActiveSession(validEvent, activeSessionStore);

      // Validate ISO 8601 format
      expect(new Date(result.validatedAt).toISOString()).toBe(result.validatedAt);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching ValidatedSayCommand schema', async () => {
      const result = await SaySessionVerifier.validateActiveSession(validEvent, activeSessionStore);

      const parseResult = ValidatedSayCommandSchema.safeParse(result);
      expect(parseResult.success).toBe(true);
    });

    it('should have sessionId as a UUID string', async () => {
      const result = await SaySessionVerifier.validateActiveSession(validEvent, activeSessionStore);

      expect(typeof result.sessionId).toBe('string');
      expect(result.sessionId).toMatch(
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i,
      );
    });

    it('should have text as a non-empty string', async () => {
      const result = await SaySessionVerifier.validateActiveSession(validEvent, activeSessionStore);

      expect(typeof result.text).toBe('string');
      expect(result.text.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SESSION_INACTIVE when session is not active', async () => {
      try {
        await SaySessionVerifier.validateActiveSession(validEvent, inactiveSessionStore);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('SESSION_INACTIVE');
        expect((e as VoiceError).statusCode).toBe(422);
      }
    });

    it('should log error when session is inactive', async () => {
      try {
        await SaySessionVerifier.validateActiveSession(validEvent, inactiveSessionStore);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        'SESSION_INACTIVE',
        expect.any(VoiceError),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });

    it('should throw SESSION_INACTIVE when session store fails', async () => {
      try {
        await SaySessionVerifier.validateActiveSession(validEvent, failingSessionStore);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('SESSION_INACTIVE');
      }
    });

    it('should log error when session store lookup fails', async () => {
      try {
        await SaySessionVerifier.validateActiveSession(validEvent, failingSessionStore);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Session store lookup failed'),
        expect.any(Error),
        expect.objectContaining({ sessionId: validSessionId }),
      );
    });
  });
});
