/**
 * VoiceSessionService.test.ts - Step 4: Validate Consent on Backend
 *
 * TLA+ Properties:
 * - Reachability: pass { consent: true } → expect { authorized: true }
 * - TypeInvariant: response matches union type Success | ConsentError
 * - ErrorConsistency:
 *   - { consent: false } → expect CONSENT_REQUIRED error code
 *   - Missing consent → same error
 *
 * Resource: db-h2s4 (service)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 */

import { describe, it, expect } from 'vitest';
import { ConsentError } from '@/server/error_definitions/ConsentErrors';
import { VoiceSessionService } from '../VoiceSessionService';

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VoiceSessionService.validateConsent — Step 4: Validate Consent on Backend', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return { authorized: true, sessionStatus: INIT } for consent: true', () => {
      const result = VoiceSessionService.validateConsent({ consent: true });

      expect(result).toBeDefined();
      expect(result.authorized).toBe(true);
      expect(result.sessionStatus).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object with authorized boolean and sessionStatus string', () => {
      const result = VoiceSessionService.validateConsent({ consent: true });

      expect(typeof result.authorized).toBe('boolean');
      expect(typeof result.sessionStatus).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw CONSENT_REQUIRED when consent is false', () => {
      try {
        VoiceSessionService.validateConsent({ consent: false });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
        expect((e as ConsentError).statusCode).toBe(400);
      }
    });

    it('should throw CONSENT_REQUIRED when consent is missing', () => {
      try {
        VoiceSessionService.validateConsent({} as { consent: boolean });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
      }
    });

    it('should throw CONSENT_REQUIRED when consent is undefined', () => {
      try {
        VoiceSessionService.validateConsent({ consent: undefined } as unknown as { consent: boolean });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
      }
    });

    it('should throw CONSENT_REQUIRED when consent is string "true"', () => {
      try {
        VoiceSessionService.validateConsent({ consent: 'true' } as unknown as { consent: boolean });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ConsentError);
        expect((e as ConsentError).code).toBe('CONSENT_REQUIRED');
      }
    });
  });
});
