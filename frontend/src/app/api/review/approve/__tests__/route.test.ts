/**
 * route.test.ts - Step 2: API endpoint receives approval request
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * TLA+ properties tested:
 * - Reachability: Valid POST with contentId → ApproveContentHandler.handle() called
 * - TypeInvariant: Zod schema enforces { contentId: string }; handler receives typed object
 * - ErrorConsistency: Invalid body → 400 INVALID_REQUEST; domain errors → proper status codes
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock dependencies
vi.mock('@/server/request_handlers/ApproveContentHandler', () => ({
  ApproveContentHandler: {
    handle: vi.fn(),
  },
}));

import { ApproveContentHandler } from '@/server/request_handlers/ApproveContentHandler';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';
import { POST } from '../route';

const mockHandler = vi.mocked(ApproveContentHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function createRequest(body: unknown): NextRequest {
  return new NextRequest('http://localhost:3000/api/review/approve', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/review/approve — Step 2: Handle approval request at endpoint', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call ApproveContentHandler.handle() with validated contentId', async () => {
      mockHandler.handle.mockResolvedValue({
        entity: approvedEntity,
        workflowStage: 'FINALIZE',
      });

      const request = createRequest({ contentId });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith(contentId);
    });

    it('should return 200 with workflowStage on success', async () => {
      mockHandler.handle.mockResolvedValue({
        entity: approvedEntity,
        workflowStage: 'FINALIZE',
      });

      const request = createRequest({ contentId });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.workflowStage).toBe('FINALIZE');
      expect(data.entity.status).toBe('APPROVED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should enforce contentId is a string via Zod schema', async () => {
      const request = createRequest({ contentId: 123 });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 400 with INVALID_REQUEST for empty body', async () => {
      const request = createRequest({});
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
    });

    it('should return domain error status code for ApprovalError', async () => {
      mockHandler.handle.mockRejectedValue(
        new ApprovalError('Content not found', 'CONTENT_NOT_FOUND', 404),
      );

      const request = createRequest({ contentId });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(404);
      expect(data.code).toBe('CONTENT_NOT_FOUND');
    });

    it('should return 422 for ineligible content', async () => {
      mockHandler.handle.mockRejectedValue(
        new ApprovalError('Content not eligible', 'CONTENT_NOT_ELIGIBLE', 422),
      );

      const request = createRequest({ contentId });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('CONTENT_NOT_ELIGIBLE');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Unexpected'));

      const request = createRequest({ contentId });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
