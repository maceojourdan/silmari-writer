/**
 * Integration Test: approve-reviewed-content-and-advance-workflow
 *
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Exercises the full path:
 * 1. Validate approval request at endpoint (Zod schema)
 * 2. Service retrieves content entity (DAO)
 * 3. Verifier checks eligibility (REVIEW status)
 * 4. Service updates status to APPROVED and workflow to FINALIZE
 * 5. Workflow chain triggered
 * 6. Response returned with updated workflow stage
 *
 * Terminal Condition:
 * - DB row now APPROVED
 * - Workflow stage advanced to FINALIZE
 * - Full Reachability from trigger → terminal state
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// ---------------------------------------------------------------------------
// Mock the DAO (only boundary that touches external systems)
// ---------------------------------------------------------------------------

vi.mock('@/server/data_access_objects/ContentDAO', () => ({
  ContentDAO: {
    findById: vi.fn(),
    update: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ContentDAO } from '@/server/data_access_objects/ContentDAO';
import { ApproveContentHandler } from '@/server/request_handlers/ApproveContentHandler';

const mockDAO = vi.mocked(ContentDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const contentId = '550e8400-e29b-41d4-a716-446655440000';

const reviewContent = {
  id: contentId,
  status: 'REVIEW' as const,
  workflowStage: 'REVIEW' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const approvedContent = {
  id: contentId,
  status: 'APPROVED' as const,
  workflowStage: 'FINALIZE' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Integration: approve-reviewed-content-and-advance-workflow', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Full Reachability: trigger → terminal state
  // -------------------------------------------------------------------------

  describe('Full Reachability', () => {
    it('should execute complete approval flow: DAO → verifier → update → workflow chain', async () => {
      // Seed: content in REVIEW state
      mockDAO.findById.mockResolvedValue(reviewContent);
      mockDAO.update.mockResolvedValue(approvedContent);

      // Execute full flow through handler
      const result = await ApproveContentHandler.handle(contentId);

      // Assert: DAO was queried
      expect(mockDAO.findById).toHaveBeenCalledWith(contentId);

      // Assert: DB row updated to APPROVED
      expect(mockDAO.update).toHaveBeenCalledWith(contentId, 'APPROVED', 'FINALIZE');

      // Assert: returned entity has APPROVED status
      expect(result.entity.status).toBe('APPROVED');

      // Assert: workflow stage advanced to FINALIZE
      expect(result.workflowStage).toBe('FINALIZE');
      expect(result.entity.workflowStage).toBe('FINALIZE');
    });

    it('should return entity conforming to ContentEntity schema', async () => {
      mockDAO.findById.mockResolvedValue(reviewContent);
      mockDAO.update.mockResolvedValue(approvedContent);

      const result = await ApproveContentHandler.handle(contentId);
      const parsed = ContentEntitySchema.safeParse(result.entity);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: types preserved across boundaries
  // -------------------------------------------------------------------------

  describe('TypeInvariant across boundaries', () => {
    it('should preserve content ID type through handler → service → DAO', async () => {
      mockDAO.findById.mockResolvedValue(reviewContent);
      mockDAO.update.mockResolvedValue(approvedContent);

      const result = await ApproveContentHandler.handle(contentId);

      // The same ID should flow through
      expect(result.entity.id).toBe(contentId);
      expect(typeof result.entity.id).toBe('string');
      expect(typeof result.workflowStage).toBe('string');
    });

    it('should enforce status transition REVIEW → APPROVED only', async () => {
      mockDAO.findById.mockResolvedValue(reviewContent);
      mockDAO.update.mockResolvedValue(approvedContent);

      const result = await ApproveContentHandler.handle(contentId);

      expect(result.entity.status).toBe('APPROVED');
      // The update call should only be for APPROVED + FINALIZE
      expect(mockDAO.update).toHaveBeenCalledWith(
        contentId,
        'APPROVED',
        'FINALIZE',
      );
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: failure at each boundary
  // -------------------------------------------------------------------------

  describe('ErrorConsistency across boundaries', () => {
    it('should return CONTENT_NOT_FOUND when content does not exist', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await ApproveContentHandler.handle(contentId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ApprovalError);
        expect((e as ApprovalError).code).toBe('CONTENT_NOT_FOUND');
        expect((e as ApprovalError).statusCode).toBe(404);
      }

      // Workflow should not have proceeded
      expect(mockDAO.update).not.toHaveBeenCalled();
    });

    it('should return CONTENT_NOT_ELIGIBLE when content is in DRAFT state', async () => {
      const draftContent = { ...reviewContent, status: 'DRAFT' as const };
      mockDAO.findById.mockResolvedValue(draftContent);

      try {
        await ApproveContentHandler.handle(contentId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ApprovalError);
        expect((e as ApprovalError).code).toBe('CONTENT_NOT_ELIGIBLE');
        expect((e as ApprovalError).statusCode).toBe(422);
      }

      // Workflow should not have proceeded
      expect(mockDAO.update).not.toHaveBeenCalled();
    });

    it('should return CONTENT_NOT_ELIGIBLE when content is already APPROVED', async () => {
      mockDAO.findById.mockResolvedValue(approvedContent);

      try {
        await ApproveContentHandler.handle(contentId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ApprovalError);
        expect((e as ApprovalError).code).toBe('CONTENT_NOT_ELIGIBLE');
      }
    });

    it('should wrap DAO persistence errors as GenericError', async () => {
      mockDAO.findById.mockResolvedValue(reviewContent);
      mockDAO.update.mockRejectedValue(new Error('Connection lost'));

      try {
        await ApproveContentHandler.handle(contentId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }
    });
  });
});
