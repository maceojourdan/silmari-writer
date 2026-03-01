/**
 * Tests for POST /api/draft/generate
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 326-generate-draft-with-only-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: POST valid { caseId } → handler invoked → 200
 * - TypeInvariant: Invalid body (missing caseId) → 400 with DraftErrors.ValidationError shape
 * - ErrorConsistency: JSON response matches error schema { code, message }
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { CaseDraft } from '@/server/data_structures/Claim';
import { DraftErrors326 } from '@/server/error_definitions/DraftErrors';

// Mock the request handler
vi.mock('@/server/request_handlers/generateDraftHandler', () => ({
  generateDraftHandler: {
    handle: vi.fn(),
    handleCaseDraft: vi.fn(),
  },
}));

import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { POST } from '../route';

const mockHandler = vi.mocked(generateDraftHandler);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validCaseId = 'case-abc-123';

function createMockCaseDraft(overrides: Partial<CaseDraft> = {}): CaseDraft {
  return {
    caseId: validCaseId,
    content: 'First confirmed claim\n\nSecond confirmed claim',
    claimsUsed: ['c1', 'c2'],
    ...overrides,
  };
}

function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/draft/generate', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/draft/generate — Step 2 (path 326)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with draft data on success', async () => {
      const mockDraft = createMockCaseDraft();
      mockHandler.handleCaseDraft.mockResolvedValueOnce(mockDraft);

      const request = createRequest({ caseId: validCaseId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.caseId).toBe(validCaseId);
      expect(data.content).toBeDefined();
      expect(data.claimsUsed).toBeDefined();
    });

    it('should call handler with caseId from request body', async () => {
      const mockDraft = createMockCaseDraft();
      mockHandler.handleCaseDraft.mockResolvedValueOnce(mockDraft);

      const request = createRequest({ caseId: validCaseId });
      await POST(request as any);

      expect(mockHandler.handleCaseDraft).toHaveBeenCalledWith(validCaseId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return 400 for missing caseId', async () => {
      const request = createRequest({});
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });

    it('should return 400 for empty caseId', async () => {
      const request = createRequest({ caseId: '' });
      const response = await POST(request as any);

      expect(response.status).toBe(400);
    });

    it('should return 400 for non-JSON body', async () => {
      const request = new Request('http://localhost/api/draft/generate', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: 'not json',
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return structured error { code, message } from DraftError', async () => {
      mockHandler.handleCaseDraft.mockRejectedValueOnce(
        DraftErrors326.DataAccessError('Claims retrieval failed'),
      );

      const request = createRequest({ caseId: validCaseId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('DATA_ACCESS_ERROR');
      expect(data.message).toContain('Claims retrieval failed');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handleCaseDraft.mockRejectedValueOnce(
        new Error('Something broke'),
      );

      const request = createRequest({ caseId: validCaseId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });

    it('should return correct status code for generation error', async () => {
      mockHandler.handleCaseDraft.mockRejectedValueOnce(
        DraftErrors326.GenerationError('Draft composition failed'),
      );

      const request = createRequest({ caseId: validCaseId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('GENERATION_FAILED');
    });
  });
});
