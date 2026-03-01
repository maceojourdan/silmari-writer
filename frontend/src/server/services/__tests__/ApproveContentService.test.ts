/**
 * ApproveContentService.test.ts - Step 3: Validate eligibility and prepare approval state
 *
 * TLA+ Properties:
 * - Reachability: Content in REVIEW state → approve → status=APPROVED, nextStage set, workflow chain triggered
 * - TypeInvariant: Returned entity matches ContentEntity type; status REVIEW → APPROVED only
 * - ErrorConsistency: DAO returns null → CONTENT_NOT_FOUND; status != REVIEW → CONTENT_NOT_ELIGIBLE; workflow chain NOT triggered on error
 *
 * Resource: db-h2s4 (service)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/ContentDAO', () => ({
  ContentDAO: {
    findById: vi.fn(),
    update: vi.fn(),
  },
}));

vi.mock('../../verifiers/ContentEligibilityVerifier', () => ({
  ContentEligibilityVerifier: {
    assertApprovable: vi.fn(),
  },
}));

vi.mock('../../process_chains/ApprovalWorkflowChain', () => ({
  ApprovalWorkflowChain: {
    trigger: vi.fn(),
  },
}));

import { ApproveContentService } from '../ApproveContentService';
import { ContentDAO } from '../../data_access_objects/ContentDAO';
import { ContentEligibilityVerifier } from '../../verifiers/ContentEligibilityVerifier';
import { ApprovalWorkflowChain } from '../../process_chains/ApprovalWorkflowChain';
import { ApprovalEligibilityError } from '../../error_definitions/ApprovalErrors';

const mockDAO = vi.mocked(ContentDAO);
const mockVerifier = vi.mocked(ContentEligibilityVerifier);
const mockChain = vi.mocked(ApprovalWorkflowChain);

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

const workflowResult = {
  contentId,
  previousStage: 'REVIEW',
  nextStage: 'FINALIZE',
  triggered: true,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ApproveContentService — Step 3: Validate eligibility and prepare approval', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.findById.mockResolvedValue(reviewContent);
    mockVerifier.assertApprovable.mockImplementation(() => {});
    mockDAO.update.mockResolvedValue(approvedContent);
    mockChain.trigger.mockResolvedValue(workflowResult);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return entity with status=APPROVED and nextStage set when content is in REVIEW state', async () => {
      const result = await ApproveContentService.approveContent(contentId);

      expect(mockDAO.findById).toHaveBeenCalledWith(contentId);
      expect(mockVerifier.assertApprovable).toHaveBeenCalledWith(reviewContent);
      expect(mockDAO.update).toHaveBeenCalledWith(contentId, 'APPROVED', 'FINALIZE');
      expect(result.entity.status).toBe('APPROVED');
      expect(result.entity.workflowStage).toBe('FINALIZE');
    });

    it('should trigger ApprovalWorkflowChain after successful update', async () => {
      const result = await ApproveContentService.approveContent(contentId);

      expect(mockChain.trigger).toHaveBeenCalledWith(approvedContent);
      expect(result.workflowStage).toBe('FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return entity conforming to ContentEntity schema', async () => {
      const result = await ApproveContentService.approveContent(contentId);
      const parsed = ContentEntitySchema.safeParse(result.entity);

      expect(parsed.success).toBe(true);
    });

    it('should only transition status from REVIEW to APPROVED', async () => {
      const result = await ApproveContentService.approveContent(contentId);

      expect(result.entity.status).toBe('APPROVED');
      expect(result.entity.workflowStage).toBe('FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw CONTENT_NOT_FOUND when DAO returns null', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await ApproveContentService.approveContent(contentId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ApprovalError);
        expect((e as ApprovalError).code).toBe('CONTENT_NOT_FOUND');
        expect((e as ApprovalError).statusCode).toBe(404);
      }
    });

    it('should throw CONTENT_NOT_ELIGIBLE when content status is not REVIEW', async () => {
      const draftContent = { ...reviewContent, status: 'DRAFT' as const };
      mockDAO.findById.mockResolvedValue(draftContent);
      mockVerifier.assertApprovable.mockImplementation(() => {
        throw ApprovalEligibilityError.CONTENT_NOT_ELIGIBLE(
          `Content '${contentId}' is in 'DRAFT' status, expected 'REVIEW'`,
        );
      });

      try {
        await ApproveContentService.approveContent(contentId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ApprovalError);
        expect((e as ApprovalError).code).toBe('CONTENT_NOT_ELIGIBLE');
        expect((e as ApprovalError).statusCode).toBe(422);
      }
    });

    it('should NOT trigger workflow chain when content is not found', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await ApproveContentService.approveContent(contentId);
      } catch {
        // expected
      }

      expect(mockChain.trigger).not.toHaveBeenCalled();
    });

    it('should NOT trigger workflow chain when content is not eligible', async () => {
      const draftContent = { ...reviewContent, status: 'DRAFT' as const };
      mockDAO.findById.mockResolvedValue(draftContent);
      mockVerifier.assertApprovable.mockImplementation(() => {
        throw ApprovalEligibilityError.CONTENT_NOT_ELIGIBLE();
      });

      try {
        await ApproveContentService.approveContent(contentId);
      } catch {
        // expected
      }

      expect(mockChain.trigger).not.toHaveBeenCalled();
    });
  });
});
