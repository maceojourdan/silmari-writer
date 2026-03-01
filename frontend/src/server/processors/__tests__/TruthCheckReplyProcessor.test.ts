/**
 * TruthCheckReplyProcessor.test.ts - Step 5: Update truth_checks record
 *
 * TLA+ Properties:
 * - Reachability: Given structured update → DAO updates claim → returns updated claim with modified truth_checks
 * - TypeInvariant: Assert updated claim matches Claim type and truth_checks reflects verdict
 * - ErrorConsistency: DAO throws → expect BackendErrors.TRUTH_CHECK_PERSIST_FAILED and backend logger invoked
 *
 * Resource: db-b7r2 (processor)
 * Path: 305-followup-sms-for-uncertain-claim
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimSchema } from '@/server/data_structures/Claim';
import type { Claim, TruthCheckUpdateRequest } from '@/server/data_structures/Claim';
import { SmsError } from '@/server/error_definitions/SmsErrors';

// Mock the ClaimDAO
vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
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

import { TruthCheckReplyProcessor } from '../TruthCheckReplyProcessor';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { smsLogger } from '@/server/logging/smsLogger';

const mockDAO = vi.mocked(ClaimDAO);
const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();

const confirmUpdate: TruthCheckUpdateRequest = {
  claimId: 'claim-001',
  verdict: 'confirmed',
  source: 'sms:SM-abc123',
};

const denyUpdate: TruthCheckUpdateRequest = {
  claimId: 'claim-002',
  verdict: 'denied',
  source: 'sms:SM-def456',
};

const confirmedClaim: Claim = {
  id: 'claim-001',
  content: 'I increased sales by 40%',
  status: 'CONFIRMED',
  smsOptIn: true,
  phoneNumber: '+15551234567',
  truth_checks: [
    {
      id: 'tc-001',
      verdict: 'confirmed',
      source: 'sms:SM-abc123',
      created_at: now,
    },
  ],
  created_at: now,
  updated_at: now,
};

const deniedClaim: Claim = {
  id: 'claim-002',
  content: 'I managed a team of 50',
  status: 'DENIED',
  smsOptIn: true,
  phoneNumber: '+15559876543',
  truth_checks: [
    {
      id: 'tc-002',
      verdict: 'denied',
      source: 'sms:SM-def456',
      created_at: now,
    },
  ],
  created_at: now,
  updated_at: now,
};

describe('TruthCheckReplyProcessor.process — Step 5: Update truth_checks record', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return updated claim with modified truth_checks on confirm', async () => {
      mockDAO.updateTruthCheck.mockResolvedValue(confirmedClaim);

      const result = await TruthCheckReplyProcessor.process(confirmUpdate);

      expect(result.id).toBe('claim-001');
      expect(result.status).toBe('CONFIRMED');
      expect(result.truth_checks).toHaveLength(1);
      expect(result.truth_checks[0].verdict).toBe('confirmed');
    });

    it('should call ClaimDAO.updateTruthCheck with correct args', async () => {
      mockDAO.updateTruthCheck.mockResolvedValue(confirmedClaim);

      await TruthCheckReplyProcessor.process(confirmUpdate);

      expect(mockDAO.updateTruthCheck).toHaveBeenCalledOnce();
      expect(mockDAO.updateTruthCheck).toHaveBeenCalledWith(
        'claim-001',
        'confirmed',
        'sms:SM-abc123',
      );
    });

    it('should return updated claim with DENIED status on deny', async () => {
      mockDAO.updateTruthCheck.mockResolvedValue(deniedClaim);

      const result = await TruthCheckReplyProcessor.process(denyUpdate);

      expect(result.status).toBe('DENIED');
      expect(result.truth_checks[0].verdict).toBe('denied');
    });

    it('should log success after update', async () => {
      mockDAO.updateTruthCheck.mockResolvedValue(confirmedClaim);

      await TruthCheckReplyProcessor.process(confirmUpdate);

      expect(mockLogger.info).toHaveBeenCalledWith(
        expect.stringContaining('Truth check updated'),
        expect.objectContaining({
          claimId: 'claim-001',
          verdict: 'confirmed',
        }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching Claim schema', async () => {
      mockDAO.updateTruthCheck.mockResolvedValue(confirmedClaim);

      const result = await TruthCheckReplyProcessor.process(confirmUpdate);

      const parsed = ClaimSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should include truth_checks array reflecting the verdict', async () => {
      mockDAO.updateTruthCheck.mockResolvedValue(confirmedClaim);

      const result = await TruthCheckReplyProcessor.process(confirmUpdate);

      expect(Array.isArray(result.truth_checks)).toBe(true);
      const matchingCheck = result.truth_checks.find(tc => tc.source === 'sms:SM-abc123');
      expect(matchingCheck).toBeDefined();
      expect(matchingCheck!.verdict).toBe('confirmed');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw TRUTH_CHECK_PERSIST_FAILED when DAO throws', async () => {
      mockDAO.updateTruthCheck.mockRejectedValue(new Error('DB connection failed'));

      try {
        await TruthCheckReplyProcessor.process(confirmUpdate);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SmsError);
        expect((e as SmsError).code).toBe('TRUTH_CHECK_PERSIST_FAILED');
        expect((e as SmsError).statusCode).toBe(500);
        expect((e as SmsError).retryable).toBe(true);
      }
    });

    it('should log error via smsLogger when DAO throws', async () => {
      mockDAO.updateTruthCheck.mockRejectedValue(new Error('Timeout'));

      try {
        await TruthCheckReplyProcessor.process(confirmUpdate);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Failed to persist'),
        expect.any(Error),
        expect.objectContaining({
          claimId: 'claim-001',
          verdict: 'confirmed',
        }),
      );
    });

    it('should include error details in thrown error message', async () => {
      mockDAO.updateTruthCheck.mockRejectedValue(new Error('Row locked'));

      try {
        await TruthCheckReplyProcessor.process(confirmUpdate);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as SmsError).message).toContain('Row locked');
        expect((e as SmsError).message).toContain('claim-001');
      }
    });
  });
});
