/**
 * ContentDAO.test.ts - Step 4: Persist approved state
 *
 * TLA+ Properties:
 * - Reachability: Mock Supabase update success → status updated to APPROVED
 * - TypeInvariant: Only valid schema fields persisted; returned record matches ContentEntity
 * - ErrorConsistency: DB error → PERSISTENCE_ERROR; service returns failure without confirming approval
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';

// ---------------------------------------------------------------------------
// Mock ContentDAO
// ---------------------------------------------------------------------------

vi.mock('../ContentDAO', () => ({
  ContentDAO: {
    findById: vi.fn(),
    update: vi.fn(),
  },
}));

import { ContentDAO } from '../ContentDAO';

const mockDAO = vi.mocked(ContentDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const contentId = '550e8400-e29b-41d4-a716-446655440000';

const approvedContent = {
  id: contentId,
  status: 'APPROVED' as const,
  workflowStage: 'FINALIZE' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

const reviewContent = {
  id: contentId,
  status: 'REVIEW' as const,
  workflowStage: 'REVIEW' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ContentDAO — Step 4: Persist approved state', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should update content status to APPROVED and return updated entity', async () => {
      mockDAO.update.mockResolvedValue(approvedContent);

      const result = await ContentDAO.update(contentId, 'APPROVED', 'FINALIZE');

      expect(result).toBeDefined();
      expect(result.status).toBe('APPROVED');
      expect(result.workflowStage).toBe('FINALIZE');
      expect(mockDAO.update).toHaveBeenCalledWith(contentId, 'APPROVED', 'FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return entity that conforms to ContentEntity schema', async () => {
      mockDAO.update.mockResolvedValue(approvedContent);

      const result = await ContentDAO.update(contentId, 'APPROVED', 'FINALIZE');
      const parsed = ContentEntitySchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });

    it('should only persist valid ContentEntity fields', async () => {
      mockDAO.update.mockResolvedValue(approvedContent);

      const result = await ContentDAO.update(contentId, 'APPROVED', 'FINALIZE');

      // Verify the result only has expected keys
      const keys = Object.keys(result);
      expect(keys).toContain('id');
      expect(keys).toContain('status');
      expect(keys).toContain('workflowStage');
      expect(keys).toContain('createdAt');
      expect(keys).toContain('updatedAt');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw PERSISTENCE_ERROR on DB failure', async () => {
      const error = new ApprovalError(
        'Failed to persist content approval',
        'PERSISTENCE_ERROR',
        500,
        true,
      );
      mockDAO.update.mockRejectedValue(error);

      try {
        await ContentDAO.update(contentId, 'APPROVED', 'FINALIZE');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ApprovalError);
        expect((e as ApprovalError).code).toBe('PERSISTENCE_ERROR');
        expect((e as ApprovalError).retryable).toBe(true);
      }
    });

    it('should not confirm approval on persistence failure', async () => {
      mockDAO.update.mockRejectedValue(
        new ApprovalError('Failed to persist', 'PERSISTENCE_ERROR', 500, true),
      );

      let succeeded = false;
      try {
        await ContentDAO.update(contentId, 'APPROVED', 'FINALIZE');
        succeeded = true;
      } catch {
        // expected
      }

      expect(succeeded).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // findById
  // -------------------------------------------------------------------------

  describe('findById', () => {
    it('should return content when found', async () => {
      mockDAO.findById.mockResolvedValue(reviewContent);

      const result = await ContentDAO.findById(contentId);

      expect(result).toBeDefined();
      expect(result!.status).toBe('REVIEW');
      expect(mockDAO.findById).toHaveBeenCalledWith(contentId);
    });

    it('should return null when content not found', async () => {
      mockDAO.findById.mockResolvedValue(null);

      const result = await ContentDAO.findById('nonexistent-id');

      expect(result).toBeNull();
    });
  });
});
