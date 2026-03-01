/**
 * FollowupSmsProcessChain.step2.test.ts - Step 2: Validate claim eligibility
 *
 * TLA+ Properties:
 * - Reachability: Given valid claim in DB (UNCERTAIN + opt-in true) → returns { eligible: true, claim }
 * - TypeInvariant: Assert returned object matches EligibleClaimContext type
 * - ErrorConsistency (DAO fail): Mock DAO throw → expect BackendErrors.CLAIM_LOAD_FAILED
 * - ErrorConsistency (ineligible): Claim with smsOptIn=false → result { eligible: false }
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 305-followup-sms-for-uncertain-claim
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimSchema } from '@/server/data_structures/Claim';
import type { Claim } from '@/server/data_structures/Claim';
import { SmsError } from '@/server/error_definitions/SmsErrors';

// Mock the ClaimDAO
vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
  },
}));

// Mock the SmsFollowupService (not used in this step, but imported by chain)
vi.mock('@/server/services/SmsFollowupService', () => ({
  SmsFollowupService: {
    sendFollowup: vi.fn(),
    composeMessage: vi.fn(),
  },
}));

// Mock the smsLogger
vi.mock('@/server/logging/smsLogger', () => ({
  smsLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FollowupSmsProcessChain } from '../FollowupSmsProcessChain';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { smsLogger } from '@/server/logging/smsLogger';

const mockDAO = vi.mocked(ClaimDAO);
const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const eligibleClaim: Claim = {
  id: 'claim-001',
  content: 'I increased sales by 40%',
  status: 'UNCERTAIN',
  smsOptIn: true,
  phoneNumber: '+15551234567',
  truth_checks: [],
  created_at: now,
  updated_at: now,
};

const ineligibleOptOutClaim: Claim = {
  ...eligibleClaim,
  id: 'claim-002',
  smsOptIn: false,
};

const confirmedClaim: Claim = {
  ...eligibleClaim,
  id: 'claim-003',
  status: 'CONFIRMED',
};

describe('FollowupSmsProcessChain.validateEligibility — Step 2: Validate claim eligibility', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return eligible: true with claim when claim is UNCERTAIN and smsOptIn is true', async () => {
      mockDAO.findById.mockResolvedValue(eligibleClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-001');

      expect(result.eligible).toBe(true);
      if (result.eligible) {
        expect(result.claim.id).toBe('claim-001');
        expect(result.claim.status).toBe('UNCERTAIN');
        expect(result.claim.smsOptIn).toBe(true);
      }
    });

    it('should call ClaimDAO.findById with the provided claimId', async () => {
      mockDAO.findById.mockResolvedValue(eligibleClaim);

      await FollowupSmsProcessChain.validateEligibility('claim-xyz');

      expect(mockDAO.findById).toHaveBeenCalledOnce();
      expect(mockDAO.findById).toHaveBeenCalledWith('claim-xyz');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching EligibleClaimContext when eligible', async () => {
      mockDAO.findById.mockResolvedValue(eligibleClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-001');

      expect(result).toHaveProperty('eligible', true);
      if (result.eligible) {
        expect(result).toHaveProperty('claim');
        // Verify claim matches the Zod schema
        const parsed = ClaimSchema.safeParse(result.claim);
        expect(parsed.success).toBe(true);
      }
    });

    it('should return object matching IneligibleClaimContext when ineligible', async () => {
      mockDAO.findById.mockResolvedValue(ineligibleOptOutClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-002');

      expect(result).toHaveProperty('eligible', false);
      if (!result.eligible) {
        expect(result).toHaveProperty('reason');
        expect(typeof result.reason).toBe('string');
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw CLAIM_LOAD_FAILED when DAO throws', async () => {
      mockDAO.findById.mockRejectedValue(new Error('Database connection failed'));

      try {
        await FollowupSmsProcessChain.validateEligibility('claim-fail');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('CLAIM_LOAD_FAILED');
        expect((e as SmsError).statusCode).toBe(500);
      }
    });

    it('should throw CLAIM_LOAD_FAILED when claim not found', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await FollowupSmsProcessChain.validateEligibility('claim-missing');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('CLAIM_LOAD_FAILED');
      }
    });

    it('should return eligible: false when smsOptIn is false', async () => {
      mockDAO.findById.mockResolvedValue(ineligibleOptOutClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-002');

      expect(result.eligible).toBe(false);
      if (!result.eligible) {
        expect(result.reason).toContain('opted in');
      }
    });

    it('should return eligible: false when claim status is not UNCERTAIN', async () => {
      mockDAO.findById.mockResolvedValue(confirmedClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-003');

      expect(result.eligible).toBe(false);
      if (!result.eligible) {
        expect(result.reason).toContain('CONFIRMED');
      }
    });

    it('should log error via smsLogger when DAO throws', async () => {
      mockDAO.findById.mockRejectedValue(new Error('DB error'));

      try {
        await FollowupSmsProcessChain.validateEligibility('claim-fail');
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Failed to load claim'),
        expect.any(Error),
        expect.objectContaining({ claimId: 'claim-fail' }),
      );
    });

    it('should not send SMS when claim is ineligible', async () => {
      mockDAO.findById.mockResolvedValue(ineligibleOptOutClaim);

      const result = await FollowupSmsProcessChain.validateEligibility('claim-002');

      // The validateEligibility method should return ineligible, not trigger SMS
      expect(result.eligible).toBe(false);
    });
  });
});
