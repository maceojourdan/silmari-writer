/**
 * Step 1 Tests: Detect verification timeout event
 *
 * Resource: db-h2s4 (service)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * TLA+ Properties tested:
 * - Reachability: expired verification requests are detected
 * - TypeInvariant: result is VerificationRequest[] with correct shape
 * - ErrorConsistency: config failures → log + empty; DAO failures → PersistenceError
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
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { getVerificationTimeoutMs } from '@/server/settings/verificationTimeout';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';
import { logger } from '@/server/logging/logger';
import type { VerificationRequest } from '@/server/data_structures/VerificationRequest';

const mockGetTimeout = vi.mocked(getVerificationTimeoutMs);
const mockFindPending = vi.mocked(VerificationRequestDAO.findPendingUnresponded);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

function makePendingRequest(overrides: Partial<VerificationRequest> = {}): VerificationRequest {
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
    createdAt: new Date(Date.now() - 10 * 60 * 1000).toISOString(), // 10 min ago
    updatedAt: new Date(Date.now() - 10 * 60 * 1000).toISOString(),
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationTimeoutService.detectExpiredVerifications', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -----------------------------------------------------------------------
  // Reachability
  // -----------------------------------------------------------------------

  describe('Reachability', () => {
    it('should detect a pending SMS request older than timeout', async () => {
      // Arrange: 5-minute timeout, request created 10 minutes ago
      mockGetTimeout.mockReturnValue(5 * 60 * 1000);
      const expiredRequest = makePendingRequest({
        createdAt: new Date(Date.now() - 10 * 60 * 1000).toISOString(),
      });
      mockFindPending.mockResolvedValue([expiredRequest]);

      // Act
      const now = new Date();
      const result = await VerificationTimeoutService.detectExpiredVerifications(now);

      // Assert
      expect(result).toHaveLength(1);
      expect(result[0].id).toBe('vr-001');
    });

    it('should not include requests within the timeout window', async () => {
      // Arrange: 5-minute timeout, request created 2 minutes ago
      mockGetTimeout.mockReturnValue(5 * 60 * 1000);
      const recentRequest = makePendingRequest({
        createdAt: new Date(Date.now() - 2 * 60 * 1000).toISOString(),
      });
      mockFindPending.mockResolvedValue([recentRequest]);

      // Act
      const now = new Date();
      const result = await VerificationTimeoutService.detectExpiredVerifications(now);

      // Assert
      expect(result).toHaveLength(0);
    });

    it('should return multiple expired requests', async () => {
      mockGetTimeout.mockReturnValue(5 * 60 * 1000);
      const expired1 = makePendingRequest({
        id: 'vr-001',
        createdAt: new Date(Date.now() - 10 * 60 * 1000).toISOString(),
      });
      const expired2 = makePendingRequest({
        id: 'vr-002',
        contactMethod: 'voice',
        createdAt: new Date(Date.now() - 15 * 60 * 1000).toISOString(),
      });
      mockFindPending.mockResolvedValue([expired1, expired2]);

      const now = new Date();
      const result = await VerificationTimeoutService.detectExpiredVerifications(now);

      expect(result).toHaveLength(2);
      expect(result.map(r => r.id)).toEqual(['vr-001', 'vr-002']);
    });
  });

  // -----------------------------------------------------------------------
  // TypeInvariant
  // -----------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return VerificationRequest[] typed result', async () => {
      mockGetTimeout.mockReturnValue(5 * 60 * 1000);
      const expiredRequest = makePendingRequest();
      mockFindPending.mockResolvedValue([expiredRequest]);

      const result = await VerificationTimeoutService.detectExpiredVerifications(new Date());

      expect(Array.isArray(result)).toBe(true);
    });

    it('should return items with status=pending and respondedAt=null', async () => {
      mockGetTimeout.mockReturnValue(5 * 60 * 1000);
      const expiredRequest = makePendingRequest();
      mockFindPending.mockResolvedValue([expiredRequest]);

      const result = await VerificationTimeoutService.detectExpiredVerifications(new Date());

      for (const item of result) {
        expect(item.status).toBe('pending');
        expect(item.respondedAt).toBeNull();
      }
    });
  });

  // -----------------------------------------------------------------------
  // ErrorConsistency
  // -----------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log and return empty list when config loading fails', async () => {
      mockGetTimeout.mockImplementation(() => {
        throw new Error('Config load failure');
      });

      const result = await VerificationTimeoutService.detectExpiredVerifications(new Date());

      expect(result).toEqual([]);
      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('config'),
        expect.any(Error),
        expect.objectContaining({ path: '324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold' }),
      );
    });

    it('should propagate DAO failures as PersistenceError', async () => {
      mockGetTimeout.mockReturnValue(5 * 60 * 1000);
      mockFindPending.mockRejectedValue(new Error('DB connection failed'));

      await expect(
        VerificationTimeoutService.detectExpiredVerifications(new Date()),
      ).rejects.toThrow(DomainError);

      await expect(
        VerificationTimeoutService.detectExpiredVerifications(new Date()),
      ).rejects.toMatchObject({
        code: 'PERSISTENCE_ERROR',
      });
    });
  });
});
