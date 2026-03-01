/**
 * ApproveContentHandler.test.ts - Step 2: Handle approval request
 *
 * TLA+ Properties:
 * - Reachability: Service approves → DAO updates → returns updated entity with workflow stage
 * - TypeInvariant: Returned entity matches ContentEntity schema
 * - ErrorConsistency: ApprovalError rethrown as-is; unknown errors wrapped in GenericError
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../services/ApproveContentService', () => ({
  ApproveContentService: {
    approveContent: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ApproveContentHandler } from '../ApproveContentHandler';
import { ApproveContentService } from '../../services/ApproveContentService';

const mockService = vi.mocked(ApproveContentService);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const contentId = '550e8400-e29b-41d4-a716-446655440000';

const approvedEntity = {
  id: contentId,
  status: 'APPROVED' as const,
  workflowStage: 'FINALIZE' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

const serviceResult = {
  entity: approvedEntity,
  workflowStage: 'FINALIZE',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ApproveContentHandler — Step 2: Handle approval request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockService.approveContent.mockResolvedValue(serviceResult);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call service.approveContent and return updated entity with workflow stage', async () => {
      const result = await ApproveContentHandler.handle(contentId);

      expect(mockService.approveContent).toHaveBeenCalledWith(contentId);
      expect(result.entity).toEqual(approvedEntity);
      expect(result.workflowStage).toBe('FINALIZE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return entity conforming to ContentEntity schema', async () => {
      const result = await ApproveContentHandler.handle(contentId);
      const parsed = ContentEntitySchema.safeParse(result.entity);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow ApprovalError as-is', async () => {
      const error = new ApprovalError('Content not found', 'CONTENT_NOT_FOUND', 404);
      mockService.approveContent.mockRejectedValue(error);

      try {
        await ApproveContentHandler.handle(contentId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(ApprovalError);
        expect((e as ApprovalError).code).toBe('CONTENT_NOT_FOUND');
        expect((e as ApprovalError).statusCode).toBe(404);
      }
    });

    it('should wrap unknown errors in GenericError', async () => {
      mockService.approveContent.mockRejectedValue(new Error('Something unexpected'));

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
