/**
 * Integration test for the finalize-approved-draft-and-log-metrics path
 *
 * Path: 300-finalize-approved-draft-and-log-metrics
 *
 * This proves end-to-end:
 * - Reachability: Full path reachable from trigger to terminal state
 * - TypeInvariant: Types consistent across API → handler → processor → DAO
 * - ErrorConsistency: Error branches isolated and do not corrupt FINALIZED state
 *
 * Note: Mocks only the DAO layer (database boundary). Everything above
 * runs with real implementations: processor, handler, logger.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  DraftSchema,
  ExportArtifactSchema,
  FinalizeMetricsSchema,
} from '@/server/data_structures/Draft';
import { FinalizeResponseSchema } from '@/api_contracts/finalize';

// Only mock the DAO — everything else is real
vi.mock('../data_access_objects/DraftDAO', () => ({
  DraftDAO: {
    getDraftById: vi.fn(),
    updateStatus: vi.fn(),
    insertMetrics: vi.fn(),
  },
}));

// Mock loggers to capture calls (but let everything else be real)
vi.mock('../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { DraftDAO } from '../data_access_objects/DraftDAO';
import { FinalizeRequestHandler } from '../request_handlers/FinalizeRequestHandler';
import { FinalizeProcessor } from '../processors/FinalizeProcessor';
import { logger } from '../logging/logger';
import { frontendLogger } from '../../logging/index';

const mockDAO = vi.mocked(DraftDAO);
const mockBackendLogger = vi.mocked(logger);
const mockSharedLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Test Data — Seed DB with draft in APPROVED state
// ---------------------------------------------------------------------------

const draftId = '660e8400-e29b-41d4-a716-446655440001';
const userId = '770e8400-e29b-41d4-a716-446655440002';

const approvedDraft = {
  id: draftId,
  status: 'APPROVED' as const,
  content: 'This is the approved draft content for integration testing.',
  title: 'Integration Test Story',
  userId,
  createdAt: '2026-02-28T10:00:00.000Z',
  updatedAt: '2026-02-28T11:00:00.000Z',
  approvedAt: '2026-02-28T11:00:00.000Z',
  interactionData: {
    editsCount: 5,
    revisionsCount: 2,
    claimsVerified: 3,
    totalClaims: 4,
    signalEvents: 10,
  },
};

const finalizedDraft = {
  ...approvedDraft,
  status: 'FINALIZED' as const,
  finalizedAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Finalize Integration — Full Path 300', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Seed: DAO returns APPROVED draft initially, then FINALIZED after update
    mockDAO.getDraftById
      .mockResolvedValueOnce(approvedDraft)    // First call: validateApprovedDraft
      .mockResolvedValueOnce(finalizedDraft);    // Second call: re-fetch for metrics

    mockDAO.updateStatus.mockResolvedValue(finalizedDraft);
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path from trigger to terminal state
  // -------------------------------------------------------------------------

  describe('Reachability: Full path from FINALIZE trigger to terminal state', () => {
    it('should finalize draft end-to-end: validate → transform → persist → metrics → response', async () => {
      const result = await FinalizeRequestHandler.handle(draftId, userId);

      // Terminal condition: Response 200 equivalent
      expect(result.finalized).toBe(true);

      // Terminal condition: Draft status = FINALIZED (via DAO.updateStatus call)
      expect(mockDAO.updateStatus).toHaveBeenCalledWith(
        draftId,
        'FINALIZED',
        expect.objectContaining({ finalizedAt: expect.any(String) }),
      );

      // Terminal condition: Export artifact present
      expect(result.artifact).toBeDefined();
      expect(result.artifact.draftId).toBe(draftId);
      expect(result.artifact.content).toBe(approvedDraft.content);

      // Terminal condition: Metrics log entry recorded
      expect(result.metricsLogged).toBe(true);
      expect(mockSharedLogger.info).toHaveBeenCalledWith(
        'Finalize metrics computed',
        expect.objectContaining({
          draftId,
          module: 'FinalizeProcessor',
        }),
      );
    });

    it('should call each layer in correct order: processor → DAO → logger', async () => {
      await FinalizeRequestHandler.handle(draftId, userId);

      // DAO.getDraftById called for validation (first) and metrics (second)
      expect(mockDAO.getDraftById).toHaveBeenCalledTimes(2);

      // DAO.updateStatus called once with FINALIZED
      expect(mockDAO.updateStatus).toHaveBeenCalledTimes(1);
      expect(mockDAO.updateStatus).toHaveBeenCalledWith(
        draftId,
        'FINALIZED',
        expect.any(Object),
      );

      // Shared logger called for metrics
      expect(mockSharedLogger.info).toHaveBeenCalledTimes(1);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Types consistent across all layers
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Types consistent across API → handler → processor → DAO', () => {
    it('should return response conforming to FinalizeResponse schema', async () => {
      const result = await FinalizeRequestHandler.handle(draftId, userId);
      const parsed = FinalizeResponseSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });

    it('should produce artifact conforming to ExportArtifact schema', async () => {
      const result = await FinalizeRequestHandler.handle(draftId, userId);
      const parsed = ExportArtifactSchema.safeParse(result.artifact);

      expect(parsed.success).toBe(true);
    });

    it('should compute metrics conforming to FinalizeMetrics schema', () => {
      const metrics = FinalizeProcessor.computeMetrics(approvedDraft);
      const parsed = FinalizeMetricsSchema.safeParse(metrics);

      expect(parsed.success).toBe(true);
    });

    it('should validate draft against DraftSchema', () => {
      const parsed = DraftSchema.safeParse(approvedDraft);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: Errors isolated and don't corrupt FINALIZED state
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Error branches isolated', () => {
    it('should throw DRAFT_NOT_FOUND when draft does not exist', async () => {
      mockDAO.getDraftById.mockReset();
      mockDAO.getDraftById.mockResolvedValue(null);

      try {
        await FinalizeRequestHandler.handle(draftId, userId);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('DRAFT_NOT_FOUND');
        expect(e.statusCode).toBe(404);
      }

      // No status update should have occurred
      expect(mockDAO.updateStatus).not.toHaveBeenCalled();
    });

    it('should throw INVALID_DRAFT_STATE when draft is not APPROVED', async () => {
      mockDAO.getDraftById.mockReset();
      mockDAO.getDraftById.mockResolvedValue({
        ...approvedDraft,
        status: 'DRAFT' as const,
      });

      try {
        await FinalizeRequestHandler.handle(draftId, userId);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('INVALID_DRAFT_STATE');
        expect(e.statusCode).toBe(422);
      }

      // No status update should have occurred
      expect(mockDAO.updateStatus).not.toHaveBeenCalled();
    });

    it('should throw PERSISTENCE_FAILURE when DAO update fails', async () => {
      mockDAO.updateStatus.mockRejectedValue(new Error('DB connection failed'));

      try {
        await FinalizeRequestHandler.handle(draftId, userId);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('PERSISTENCE_FAILURE');
        expect(e.statusCode).toBe(500);
        expect(e.retryable).toBe(true);
      }

      // Backend logger should have recorded the error
      expect(mockBackendLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Failed to persist finalized status'),
        expect.any(Error),
        expect.objectContaining({ draftId }),
      );
    });

    it('should still return finalized: true when metrics logging fails', async () => {
      // Override second getDraftById to return null (simulating metrics fetch failure)
      mockDAO.getDraftById.mockReset();
      mockDAO.getDraftById
        .mockResolvedValueOnce(approvedDraft)    // validation succeeds
        .mockResolvedValueOnce(null);              // metrics fetch returns null

      const result = await FinalizeRequestHandler.handle(draftId, userId);

      // FINALIZED state remains valid
      expect(result.finalized).toBe(true);

      // Metrics were not logged because draft couldn't be re-fetched
      expect(result.metricsLogged).toBe(false);

      // But updateStatus was still called
      expect(mockDAO.updateStatus).toHaveBeenCalledTimes(1);
    });
  });
});
