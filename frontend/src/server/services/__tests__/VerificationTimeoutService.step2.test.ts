/**
 * Step 2 Tests: Update verification status to timed-out
 *
 * Resource: db-h2s4 (service)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * TLA+ Properties tested:
 * - Reachability: expired records updated to 'Timed Out'
 * - TypeInvariant: result is VerificationRequest[] with correct status
 * - ErrorConsistency: concurrent update → log conflict; DAO failure → PersistenceError
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationTimeoutService } from '@/server/services/VerificationTimeoutService';
import { DomainError } from '@/server/error_definitions/DomainErrors';

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

vi.mock('@/server/settings/verificationTimeout', () => ({
  getVerificationTimeoutMs: vi.fn(),
}));

vi.mock('@/server/data_access_objects/VerificationRequestDAO', () => ({
  VerificationRequestDAO: {
    findPendingUnresponded: vi.fn(),
    updateStatusIfUnresponded: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: { findById: vi.fn(), updateStatus: vi.fn() },
}));

vi.mock('@/server/data_access_objects/DraftingWorkflowDAO', () => ({
  DraftingWorkflowDAO: { findByClaimId: vi.fn(), updateStatus: vi.fn() },
}));

vi.mock('@/server/verifiers/ClaimDraftingStateVerifier', () => ({
  ClaimDraftingStateVerifier: { validate: vi.fn() },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';
import { logger } from '@/server/logging/logger';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';

const mockUpdateIfUnresponded = vi.mocked(VerificationRequestDAO.updateStatusIfUnresponded);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

function makeExpiredRequest(overrides: Partial<VerificationRequest> = {}): VerificationRequest {
  return {
    id: 'vr-001',
    sessionId: 'session-001',
    status: 'pending',
    attemptCount: 1,
    token: 'token-abc',
    claimIds: ['claim-001'],
    contactPhone: '+15551234567',
    contactMethod: 'sms',
    respondedAt: null,
    createdAt: new Date(Date.now() - 10 * 60 * 1000).toISOString(),
    updatedAt: new Date(Date.now() - 10 * 60 * 1000).toISOString(),
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationTimeoutService.markAsTimedOut', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -----------------------------------------------------------------------
  // Reachability
  // -----------------------------------------------------------------------

  describe('Reachability', () => {
    it('should update expired record to timed_out status', async () => {
      const expiredRecord = makeExpiredRequest();
      mockUpdateIfUnresponded.mockResolvedValue(1); // 1 row affected

      const result = await VerificationTimeoutService.markAsTimedOut([expiredRecord]);

      expect(result).toHaveLength(1);
      expect(result[0].status).toBe('timed_out');
      expect(mockUpdateIfUnresponded).toHaveBeenCalledWith('vr-001', 'timed_out');
    });

    it('should update multiple expired records', async () => {
      const record1 = makeExpiredRequest({ id: 'vr-001' });
      const record2 = makeExpiredRequest({ id: 'vr-002', contactMethod: 'voice' });
      mockUpdateIfUnresponded.mockResolvedValue(1);

      const result = await VerificationTimeoutService.markAsTimedOut([record1, record2]);

      expect(result).toHaveLength(2);
      expect(mockUpdateIfUnresponded).toHaveBeenCalledTimes(2);
    });
  });

  // -----------------------------------------------------------------------
  // TypeInvariant
  // -----------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return VerificationRequest[] typed result', async () => {
      const expiredRecord = makeExpiredRequest();
      mockUpdateIfUnresponded.mockResolvedValue(1);

      const result = await VerificationTimeoutService.markAsTimedOut([expiredRecord]);

      expect(Array.isArray(result)).toBe(true);
    });

    it('should return items with status=timed_out and respondedAt=null', async () => {
      const expiredRecord = makeExpiredRequest();
      mockUpdateIfUnresponded.mockResolvedValue(1);

      const result = await VerificationTimeoutService.markAsTimedOut([expiredRecord]);

      for (const item of result) {
        expect(item.status).toBe('timed_out');
        expect(item.respondedAt).toBeNull();
      }
    });
  });

  // -----------------------------------------------------------------------
  // ErrorConsistency
  // -----------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log conflict and skip record when concurrent update occurs (0 rows)', async () => {
      const expiredRecord = makeExpiredRequest();
      mockUpdateIfUnresponded.mockResolvedValue(0); // concurrent response

      const result = await VerificationTimeoutService.markAsTimedOut([expiredRecord]);

      expect(result).toHaveLength(0);
      expect(mockLogger.warn).toHaveBeenCalledWith(
        expect.stringContaining('Concurrency conflict'),
        expect.objectContaining({ requestId: 'vr-001' }),
      );
    });

    it('should propagate DAO failure as PersistenceError', async () => {
      const expiredRecord = makeExpiredRequest();
      mockUpdateIfUnresponded.mockRejectedValue(new Error('DB write failed'));

      await expect(
        VerificationTimeoutService.markAsTimedOut([expiredRecord]),
      ).rejects.toThrow(DomainError);

      await expect(
        VerificationTimeoutService.markAsTimedOut([expiredRecord]),
      ).rejects.toMatchObject({
        code: 'PERSISTENCE_ERROR',
      });
    });
  });
});
