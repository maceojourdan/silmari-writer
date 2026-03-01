/**
 * InitiateVerificationHandler.test.ts - Step 1: Receive Verification Initiation Request
 *
 * TLA+ Properties:
 * - Reachability: Valid claimantId → handler calls VerificationService.initiateContactVerification
 * - TypeInvariant: Parsed body matches Zod schema { claimantId: uuid }; response shape { status }
 * - ErrorConsistency: Empty body → VERIFICATION_REQUEST_INVALID
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 323-fail-verification-when-no-contact-method
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import { InitiateVerificationRequestSchema } from '@/server/data_structures/VerificationAttempt';

// Mock the VerificationService
vi.mock('@/server/services/VerificationService', () => ({
  VerificationService: {
    initiateContactVerification: vi.fn(),
    detectEligibility: vi.fn(),
    initiateVerification: vi.fn(),
    handleInboundConfirmation: vi.fn(),
    markClaimsVerified: vi.fn(),
    enableDrafting: vi.fn(),
    startDrafting: vi.fn(),
  },
}));

vi.mock('@/server/logging/verificationLogger', () => ({
  verificationLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { InitiateVerificationHandler } from '../InitiateVerificationHandler';
import { VerificationService } from '@/server/services/VerificationService';

const mockService = vi.mocked(VerificationService);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('InitiateVerificationHandler — Step 1: Receive Verification Initiation Request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call VerificationService.initiateContactVerification with claimantId', async () => {
      mockService.initiateContactVerification.mockResolvedValue({
        verificationStatus: 'FAILED',
        reason: 'MISSING_CONTACT_METHOD',
        draftingAllowed: false,
      });

      await InitiateVerificationHandler.handle({ claimantId: '550e8400-e29b-41d4-a716-446655440000' });

      expect(mockService.initiateContactVerification).toHaveBeenCalledWith(
        '550e8400-e29b-41d4-a716-446655440000',
      );
    });

    it('should return the service result', async () => {
      const expected = {
        verificationStatus: 'FAILED' as const,
        reason: 'MISSING_CONTACT_METHOD',
        draftingAllowed: false,
      };
      mockService.initiateContactVerification.mockResolvedValue(expected);

      const result = await InitiateVerificationHandler.handle({
        claimantId: '550e8400-e29b-41d4-a716-446655440000',
      });

      expect(result).toEqual(expected);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate input against InitiateVerificationRequestSchema', () => {
      const valid = InitiateVerificationRequestSchema.safeParse({
        claimantId: '550e8400-e29b-41d4-a716-446655440000',
      });
      expect(valid.success).toBe(true);
    });

    it('should reject non-UUID claimantId', () => {
      const invalid = InitiateVerificationRequestSchema.safeParse({
        claimantId: 'not-a-uuid',
      });
      expect(invalid.success).toBe(false);
    });

    it('should reject missing claimantId', () => {
      const invalid = InitiateVerificationRequestSchema.safeParse({});
      expect(invalid.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow known VerificationErrors', async () => {
      const knownError = new VerificationError(
        'Not found',
        'CLAIMANT_NOT_FOUND',
        404,
        false,
      );
      mockService.initiateContactVerification.mockRejectedValue(knownError);

      try {
        await InitiateVerificationHandler.handle({
          claimantId: '550e8400-e29b-41d4-a716-446655440000',
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('CLAIMANT_NOT_FOUND');
      }
    });

    it('should wrap unknown errors in GENERIC_VERIFICATION_FAILURE', async () => {
      mockService.initiateContactVerification.mockRejectedValue(
        new Error('something unexpected'),
      );

      try {
        await InitiateVerificationHandler.handle({
          claimantId: '550e8400-e29b-41d4-a716-446655440000',
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('GENERIC_VERIFICATION_FAILURE');
      }
    });
  });
});
