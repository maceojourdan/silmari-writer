/**
 * ContactMethodVerifier.test.ts - Step 3: Validate Contact Method Availability
 *
 * TLA+ Properties:
 * - Reachability: Claimant with phone=null, smsOptIn=false → { hasContactMethod: false }
 * - TypeInvariant: Return type is { hasContactMethod: boolean }
 * - ErrorConsistency: Malformed claimant → INTERNAL_VALIDATION_ERROR + logger.error called
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 323-fail-verification-when-no-contact-method
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import type { Claimant } from '@/server/data_structures/Claimant';

// Mock the logger
vi.mock('@/server/logging/verificationLogger', () => ({
  verificationLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ContactMethodVerifier } from '../ContactMethodVerifier';
import { verificationLogger } from '@/server/logging/verificationLogger';

const mockLogger = vi.mocked(verificationLogger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

function claimantNoContact(): Claimant {
  return {
    id: 'c-no-contact',
    keyClaims: [{ id: 'kc-1', category: 'metrics', content: 'Revenue +40%' }],
    phone: null,
    smsOptIn: false,
  };
}

function claimantWithPhoneNoSms(): Claimant {
  return {
    id: 'c-phone-only',
    keyClaims: [{ id: 'kc-1', category: 'metrics', content: 'Revenue +40%' }],
    phone: '+15551234567',
    smsOptIn: false,
  };
}

function claimantWithPhoneAndSms(): Claimant {
  return {
    id: 'c-phone-sms',
    keyClaims: [{ id: 'kc-1', category: 'metrics', content: 'Revenue +40%' }],
    phone: '+15551234567',
    smsOptIn: true,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ContactMethodVerifier — Step 3: Validate Contact Method Availability', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return hasContactMethod=false when phone is null and smsOptIn is false', () => {
      const result = ContactMethodVerifier.validate(claimantNoContact());
      expect(result.hasContactMethod).toBe(false);
    });

    it('should return hasContactMethod=true when phone is present (voice available)', () => {
      const result = ContactMethodVerifier.validate(claimantWithPhoneNoSms());
      expect(result.hasContactMethod).toBe(true);
    });

    it('should return hasContactMethod=true when phone is present and smsOptIn is true', () => {
      const result = ContactMethodVerifier.validate(claimantWithPhoneAndSms());
      expect(result.hasContactMethod).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object with boolean hasContactMethod field', () => {
      const result = ContactMethodVerifier.validate(claimantNoContact());
      expect(typeof result.hasContactMethod).toBe('boolean');
    });

    it('should return an object with only hasContactMethod property', () => {
      const result = ContactMethodVerifier.validate(claimantNoContact());
      expect(Object.keys(result)).toEqual(['hasContactMethod']);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw INTERNAL_VALIDATION_ERROR for undefined input', () => {
      try {
        ContactMethodVerifier.validate(undefined as unknown as Claimant);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('INTERNAL_VALIDATION_ERROR');
      }
    });

    it('should throw INTERNAL_VALIDATION_ERROR for null input', () => {
      try {
        ContactMethodVerifier.validate(null as unknown as Claimant);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('INTERNAL_VALIDATION_ERROR');
      }
    });

    it('should log error via verificationLogger when validation throws', () => {
      try {
        ContactMethodVerifier.validate(undefined as unknown as Claimant);
      } catch {
        // expected
      }
      expect(mockLogger.error).toHaveBeenCalled();
    });
  });
});
