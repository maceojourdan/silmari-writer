/**
 * route.test.ts - Step 2C: API route integration for export finalized answer
 *
 * TLA+ Properties:
 * - Reachability: HTTP GET /api/answers/123/export?format=markdown → 200 with structured content
 * - TypeInvariant: Response body matches Zod schema in api-q7v1
 * - ErrorConsistency: Not found → 404 with mapped shared error code
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 334-export-or-copy-finalized-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import { ExportFinalizedAnswerResponseSchema } from '@/api_contracts/exportFinalizedAnswer';

// Mock dependencies
vi.mock('@/server/request_handlers/ExportFinalizedAnswerHandler', () => ({
  ExportFinalizedAnswerHandler: {
    handle: vi.fn(),
  },
}));

vi.mock('@/server/transformers/AnswerExportTransformer', () => ({
  AnswerExportTransformer: {
    transform: vi.fn(),
  },
}));

import { ExportFinalizedAnswerHandler } from '@/server/request_handlers/ExportFinalizedAnswerHandler';
import { AnswerExportTransformer } from '@/server/transformers/AnswerExportTransformer';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';
import { SharedError } from '@/server/error_definitions/SharedErrors';
import { GET } from '../route';

const mockHandler = vi.mocked(ExportFinalizedAnswerHandler);
const mockTransformer = vi.mocked(AnswerExportTransformer);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const finalizedAnswer = {
  id: answerId,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  locked: true,
  content: 'My finalized answer about leadership experience.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

function createRequest(format = 'markdown'): NextRequest {
  return new NextRequest(
    `http://localhost:3000/api/answers/${answerId}/export?format=${format}`,
    { method: 'GET' },
  );
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('GET /api/answers/[id]/export — Step 2C: API route integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with structured content for valid request', async () => {
      mockHandler.handle.mockResolvedValue(finalizedAnswer);
      mockTransformer.transform.mockReturnValue('# My finalized answer about leadership experience.');

      const request = createRequest('markdown');
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.content).toBe('# My finalized answer about leadership experience.');
      expect(data.format).toBe('markdown');
      expect(data.answerId).toBe(answerId);
    });

    it('should call handler with answerId from params', async () => {
      mockHandler.handle.mockResolvedValue(finalizedAnswer);
      mockTransformer.transform.mockReturnValue('content');

      const request = createRequest();
      await GET(request, { params: Promise.resolve({ id: answerId }) });

      expect(mockHandler.handle).toHaveBeenCalledWith(answerId);
    });

    it('should call transformer with answer and format', async () => {
      mockHandler.handle.mockResolvedValue(finalizedAnswer);
      mockTransformer.transform.mockReturnValue('content');

      const request = createRequest('plain_text');
      await GET(request, { params: Promise.resolve({ id: answerId }) });

      expect(mockTransformer.transform).toHaveBeenCalledWith(finalizedAnswer, 'plain_text');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return response matching ExportFinalizedAnswerResponseSchema', async () => {
      mockHandler.handle.mockResolvedValue(finalizedAnswer);
      mockTransformer.transform.mockReturnValue('# Formatted content');

      const request = createRequest('markdown');
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      const parsed = ExportFinalizedAnswerResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });

    it('should return 400 for invalid format parameter', async () => {
      const request = createRequest('pdf');
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBeDefined();
    });

    it('should return 400 when format parameter is missing', async () => {
      const request = new NextRequest(
        `http://localhost:3000/api/answers/${answerId}/export`,
        { method: 'GET' },
      );
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });

      expect(response.status).toBe(400);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 404 for ANSWER_NOT_FOUND errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new AnswerError('Answer not found', 'ANSWER_NOT_FOUND', 404),
      );

      const request = createRequest();
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(404);
      expect(data.code).toBe('ANSWER_NOT_FOUND');
    });

    it('should return 422 for ANSWER_NOT_LOCKED errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new AnswerError('Not locked', 'ANSWER_NOT_LOCKED', 422),
      );

      const request = createRequest();
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('ANSWER_NOT_LOCKED');
    });

    it('should return 422 for SharedError (unsupported format)', async () => {
      mockHandler.handle.mockResolvedValue(finalizedAnswer);
      mockTransformer.transform.mockImplementation(() => {
        throw new SharedError('Unsupported format', 'UNSUPPORTED_EXPORT_FORMAT', 422, false);
      });

      const request = createRequest('markdown');
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('UNSUPPORTED_EXPORT_FORMAT');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Unexpected failure'));

      const request = createRequest();
      const response = await GET(request, { params: Promise.resolve({ id: answerId }) });
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
