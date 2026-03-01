/**
 * StartVoiceSessionHandler.test.ts - Step 5a: Request Handler
 *
 * TLA+ Properties:
 * - Reachability: valid consent → service returns { authorized: true, sessionStatus: 'INIT' }
 * - TypeInvariant: response conforms to { sessionStatus: 'INIT' }
 * - ErrorConsistency:
 *   - consent: false → ConsentError rethrown
 *   - unexpected error → logged via backend logger, wrapped in GenericError
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ConsentError } from '@/server/error_definitions/ConsentErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// Mock the backend logger
vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { logger } from '../../logging/logger';
import { StartVoiceSessionHandler } from '../StartVoiceSessionHandler';

const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StartVoiceSessionHandler.handle — Step 5a: Request Handler', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return { sessionStatus: INIT } for valid consent', async () => {
      const result = await StartVoiceSessionHandler.handle({ consent: true });

      expect(result).toBeDefined();
      expect(result.sessionStatus).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object with sessionStatus string', async () => {
      const result = await StartVoiceSessionHandler.handle({ consent: true });

      expect(typeof result.sessionStatus).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow ConsentError when consent is false', async () => {
      try {
        await StartVoiceSessionHandler.handle({ consent: false });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
      }
    });

    it('should log and wrap unexpected errors in GenericError', async () => {
      // Force an unexpected error by passing a payload that causes internal failure
      // We'll mock the service for this specific test
      const { VoiceSessionService } = await import('../../services/VoiceSessionService');
      const originalValidate = VoiceSessionService.validateConsent;

      // Temporarily override
      (VoiceSessionService as any).validateConsent = () => {
        throw new Error('Unexpected DB failure');
      };

      try {
        await StartVoiceSessionHandler.handle({ consent: true });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
        expect((e as GenericError).statusCode).toBe(500);
      }

      // Verify logger was called
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Unexpected error during voice session start'),
        expect.any(Error),
        expect.objectContaining({
          path: '302-enforce-affirmative-consent-before-voice-session',
          resource: 'api-n8k2',
        }),
      );

      // Restore original
      (VoiceSessionService as any).validateConsent = originalValidate;
    });
  });
});
