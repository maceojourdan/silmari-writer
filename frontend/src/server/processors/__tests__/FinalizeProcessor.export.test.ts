/**
 * FinalizeProcessor.export.test.ts - Step 3: Generate Exportable Answer Artifact
 *
 * TLA+ Properties:
 * - Reachability: Mock draft APPROVED → finalizeDraft → returns { artifact, status: "FINALIZED" }
 * - TypeInvariant: Artifact matches ExportArtifact type; DAO.updateStatus called with "FINALIZED"
 * - ErrorConsistency: DAO failure on update → PersistenceFailure; draft status remains APPROVED; backend_logging.error called
 *
 * Resource: db-b7r2 (processor)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ExportArtifactSchema } from '@/server/data_structures/Draft';
import { FinalizeError } from '@/server/error_definitions/FinalizeErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/DraftDAO', () => ({
  DraftDAO: {
    getDraftById: vi.fn(),
    updateStatus: vi.fn(),
    insertMetrics: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('../../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FinalizeProcessor } from '../FinalizeProcessor';
import { DraftDAO } from '../../data_access_objects/DraftDAO';
import { logger } from '../../logging/logger';

const mockDAO = vi.mocked(DraftDAO);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const draftId = '660e8400-e29b-41d4-a716-446655440001';
const userId = '770e8400-e29b-41d4-a716-446655440002';

const approvedDraft = {
  id: draftId,
  status: 'APPROVED' as const,
  content: 'This is an approved draft content.',
  title: 'My Story',
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
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeProcessor.finalizeDraft — Step 3: Generate Exportable Answer Artifact', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.getDraftById.mockResolvedValue(approvedDraft);
    mockDAO.updateStatus.mockResolvedValue(finalizedDraft);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return artifact and FINALIZED status', async () => {
      const result = await FinalizeProcessor.finalizeDraft(draftId);

      expect(result.status).toBe('FINALIZED');
      expect(result.artifact).toBeDefined();
      expect(result.artifact.draftId).toBe(draftId);
      expect(result.artifact.content).toBe('This is an approved draft content.');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return artifact conforming to ExportArtifact schema', async () => {
      const result = await FinalizeProcessor.finalizeDraft(draftId);
      const parsed = ExportArtifactSchema.safeParse(result.artifact);

      expect(parsed.success).toBe(true);
    });

    it('should call DAO.updateStatus with FINALIZED', async () => {
      await FinalizeProcessor.finalizeDraft(draftId);

      expect(mockDAO.updateStatus).toHaveBeenCalledWith(
        draftId,
        'FINALIZED',
        expect.objectContaining({ finalizedAt: expect.any(String) }),
      );
    });

    it('should include correct metadata in artifact', async () => {
      const result = await FinalizeProcessor.finalizeDraft(draftId);

      expect(result.artifact.metadata.userId).toBe(userId);
      expect(result.artifact.metadata.originalCreatedAt).toBe('2026-02-28T10:00:00.000Z');
      expect(result.artifact.metadata.finalizedAt).toBeDefined();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw PersistenceFailure on DAO update failure', async () => {
      mockDAO.updateStatus.mockRejectedValue(new Error('DB connection failed'));

      try {
        await FinalizeProcessor.finalizeDraft(draftId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeError);
        expect((e as FinalizeError).code).toBe('PERSISTENCE_FAILURE');
      }
    });

    it('should log error via backend_logging on persistence failure', async () => {
      mockDAO.updateStatus.mockRejectedValue(new Error('DB connection failed'));

      try {
        await FinalizeProcessor.finalizeDraft(draftId);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Failed to persist finalized status'),
        expect.any(Error),
        expect.objectContaining({
          path: '300-finalize-approved-draft-and-log-metrics',
          resource: 'db-b7r2',
          draftId,
        }),
      );
    });

    it('should not update status if validation fails (draft stays APPROVED)', async () => {
      mockDAO.getDraftById.mockResolvedValue(null);

      try {
        await FinalizeProcessor.finalizeDraft(draftId);
      } catch {
        // expected
      }

      expect(mockDAO.updateStatus).not.toHaveBeenCalled();
    });
  });
});
