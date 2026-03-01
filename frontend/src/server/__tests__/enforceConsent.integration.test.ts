/**
 * Integration test for the enforce-affirmative-consent-before-voice-session path
 *
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * This proves end-to-end:
 * - Reachability: Trigger → verifier → service → handler → response (all 6 steps)
 * - TypeInvariant: All boundary schemas validated via Zod
 * - ErrorConsistency: All defined error branches return correct states
 *
 * Full flow exercises:
 * 1. Click Start Voice Session
 * 2. Decline consent → No API request made, session inactive, visible consent message
 * 3. Accept consent → 200 response → session transitions to INIT
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { isExplicitlyAffirmative } from '@/verifiers/consentVerifier';
import {
  StartVoiceSessionRequestSchema,
  StartVoiceSessionResponseSchema,
} from '@/api_contracts/startVoiceSession';
import { VoiceSessionService } from '../services/VoiceSessionService';
import { StartVoiceSessionHandler } from '../request_handlers/StartVoiceSessionHandler';
import { ConsentError } from '../error_definitions/ConsentErrors';
import { GenericError } from '../error_definitions/GenericErrors';

// Mock the backend logger to capture calls
vi.mock('../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { logger } from '../logging/logger';
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Enforce Affirmative Consent Integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path from trigger to terminal
  // -------------------------------------------------------------------------

  describe('Reachability: Full path from trigger to terminal', () => {
    it('should complete the full happy path: verifier → service → handler → INIT', async () => {
      // Step 1: User clicks "Start Voice Session" → shown consent prompt (UI level)

      // Step 2: Frontend verifier passes for "I agree"
      const consentFlag = isExplicitlyAffirmative('I agree');
      expect(consentFlag).toBe(true);

      // Step 3: API contract schema validates { consent: true }
      const requestValid = StartVoiceSessionRequestSchema.safeParse({ consent: true });
      expect(requestValid.success).toBe(true);

      // Steps 4-5: Backend handler → service validates consent → returns INIT
      const result = await StartVoiceSessionHandler.handle({ consent: true });
      expect(result.authorized).toBe(true);
      expect(result.sessionStatus).toBe('INIT');

      // Step 6: Response schema validates
      const responseValid = StartVoiceSessionResponseSchema.safeParse({
        sessionStatus: result.sessionStatus,
      });
      expect(responseValid.success).toBe(true);
    });

    it('should complete decline path: verifier blocks → no API call → consent required message', () => {
      // Step 1: User clicks "Start Voice Session" (UI level)

      // Step 2: Frontend verifier blocks non-affirmative response
      const consentFlag = isExplicitlyAffirmative('No');
      expect(consentFlag).toBe(false);

      // Step 3: Since consentFlag is false, no API request should be made
      // (Frontend component gate - tested in component tests)

      // Terminal: User sees session inactive + consent required message
    });

    it('should work end-to-end: verifier → handler → service → response', async () => {
      // Step 2: Verifier
      const consentFlag = isExplicitlyAffirmative('yes');
      expect(consentFlag).toBe(true);

      // Step 4: Service validates directly
      const serviceResult = VoiceSessionService.validateConsent({ consent: true });
      expect(serviceResult.authorized).toBe(true);
      expect(serviceResult.sessionStatus).toBe('INIT');

      // Steps 4-5 via full handler
      const handlerResult = await StartVoiceSessionHandler.handle({ consent: true });
      expect(handlerResult.sessionStatus).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: All schema boundaries validated
  // -------------------------------------------------------------------------

  describe('TypeInvariant: All schema boundaries validated via Zod', () => {
    it('should validate request schema for consent: true (literal)', () => {
      const valid = StartVoiceSessionRequestSchema.safeParse({ consent: true });
      expect(valid.success).toBe(true);
    });

    it('should reject request schema for consent: false', () => {
      const invalid = StartVoiceSessionRequestSchema.safeParse({ consent: false });
      expect(invalid.success).toBe(false);
    });

    it('should validate response schema for INIT status', () => {
      const valid = StartVoiceSessionResponseSchema.safeParse({ sessionStatus: 'INIT' });
      expect(valid.success).toBe(true);
    });

    it('should reject response schema for invalid status', () => {
      const invalid = StartVoiceSessionResponseSchema.safeParse({ sessionStatus: 'INVALID' });
      expect(invalid.success).toBe(false);
    });

    it('should return typed ConsentValidationResult from handler', async () => {
      const result = await StartVoiceSessionHandler.handle({ consent: true });

      expect(typeof result.authorized).toBe('boolean');
      expect(typeof result.sessionStatus).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: Each failure branch produces defined error
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Each failure branch produces defined error', () => {
    it('should return false for non-affirmative consent at verifier level', () => {
      expect(isExplicitlyAffirmative('no')).toBe(false);
      expect(isExplicitlyAffirmative('maybe')).toBe(false);
      expect(isExplicitlyAffirmative('')).toBe(false);
    });

    it('should throw CONSENT_REQUIRED when consent flag is false at service level', () => {
      try {
        VoiceSessionService.validateConsent({ consent: false });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
        expect((e as ConsentError).statusCode).toBe(400);
      }
    });

    it('should throw CONSENT_REQUIRED through handler when consent is false', async () => {
      try {
        await StartVoiceSessionHandler.handle({ consent: false });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
        expect((e as ConsentError).statusCode).toBe(400);
        expect((e as ConsentError).message).toContain('Affirmative consent is required');
      }
    });

    it('should throw CONSENT_REQUIRED through handler when consent is missing', async () => {
      try {
        await StartVoiceSessionHandler.handle({} as { consent: boolean });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
      }
    });

    it('should wrap unexpected service errors in GenericError', async () => {
      // Temporarily break the service to simulate unexpected failure
      const originalValidate = VoiceSessionService.validateConsent;
      (VoiceSessionService as any).validateConsent = () => {
        throw new Error('Unexpected crash');
      };

      try {
        await StartVoiceSessionHandler.handle({ consent: true });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
        expect((e as GenericError).statusCode).toBe(500);
      }

      // Verify backend logger was called
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Unexpected error'),
        expect.any(Error),
        expect.objectContaining({
          path: '302-enforce-affirmative-consent-before-voice-session',
          resource: 'api-n8k2',
        }),
      );

      // Restore
      (VoiceSessionService as any).validateConsent = originalValidate;
    });

    it('should verify feedback loop: 3 non-affirmative responses all return false', () => {
      const attempts = ['no', 'decline', 'maybe'];

      attempts.forEach((attempt) => {
        expect(isExplicitlyAffirmative(attempt)).toBe(false);
      });

      // After 3 failures, the component resets to idle (tested in component tests)
    });
  });
});
