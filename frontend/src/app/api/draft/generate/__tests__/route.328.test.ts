/**
 * Tests for POST /api/draft/generate (path 328)
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 328-exclude-incomplete-claim-during-draft-generation
 *
 * TLA+ properties tested:
 * - Reachability: POST valid { sessionId } → handler invoked → returns 200 with draft response shape
 * - TypeInvariant: Assert normalized command matches DraftGenerationCommand Zod schema
 * - ErrorConsistency: POST invalid payload → 400 with DraftErrors328.InvalidDraftRequest
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { ExcludeIncompleteDraftResponse } from '@/server/data_structures/Claim';
import { DraftErrors328 } from '@/server/error_definitions/DraftErrors';

// Mock the request handler
vi.mock('@/server/request_handlers/generateDraftHandler', () => ({
  generateDraftHandler: {
    handle: vi.fn(),
    handleCaseDraft: vi.fn(),
    handleStoryDraft: vi.fn(),
    handleExcludeIncompleteDraft: vi.fn(),
  },
}));

import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { POST } from '../route';

const mockHandler = vi.mocked(generateDraftHandler);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'session-abc-123';

function createMockDraftResponse(
  overrides: Partial<ExcludeIncompleteDraftResponse> = {},
): ExcludeIncompleteDraftResponse {
  return {
    draft: 'Generated draft content from complete claims.',
    omissions: [
      {
        claimId: 'claim-B',
        reason: 'Claim omitted due to missing required structural metadata: metric, scope',
      },
    ],
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

describe('POST /api/draft/generate — Step 1 (path 328: sessionId draft generation)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with draft + omissions when sessionId provided', async () => {
      const mockDraft = createMockDraftResponse();
      mockHandler.handleExcludeIncompleteDraft.mockResolvedValueOnce(mockDraft);

      const request = createRequest({ sessionId: validSessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.draft).toBeDefined();
      expect(data.omissions).toBeDefined();
      expect(Array.isArray(data.omissions)).toBe(true);
    });

    it('should call handleExcludeIncompleteDraft with sessionId from request body', async () => {
      const mockDraft = createMockDraftResponse();
      mockHandler.handleExcludeIncompleteDraft.mockResolvedValueOnce(mockDraft);

      const request = createRequest({ sessionId: validSessionId });
      await POST(request as any);

      expect(mockHandler.handleExcludeIncompleteDraft).toHaveBeenCalledWith(validSessionId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return 400 for empty sessionId', async () => {
      const request = createRequest({ sessionId: '' });
      const response = await POST(request as any);

      expect(response.status).toBe(400);
    });

    it('should return 400 for missing sessionId', async () => {
      const request = createRequest({});
      const response = await POST(request as any);

      // Without sessionId, storyRecordId, or caseId, should get validation error
      expect(response.status).toBe(400);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 400 with INVALID_DRAFT_REQUEST when handler throws InvalidDraftRequest', async () => {
      mockHandler.handleExcludeIncompleteDraft.mockRejectedValueOnce(
        DraftErrors328.InvalidDraftRequest('Missing session ID'),
      );

      const request = createRequest({ sessionId: validSessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_DRAFT_REQUEST');
    });

    it('should return 500 with DATA_ACCESS_ERROR when handler throws DataAccessError', async () => {
      mockHandler.handleExcludeIncompleteDraft.mockRejectedValueOnce(
        DraftErrors328.DataAccessError('DB connection lost'),
      );

      const request = createRequest({ sessionId: validSessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('DATA_ACCESS_ERROR');
    });

    it('should return 500 with DRAFT_ASSEMBLY_ERROR when handler throws DraftAssemblyError', async () => {
      mockHandler.handleExcludeIncompleteDraft.mockRejectedValueOnce(
        DraftErrors328.DraftAssemblyError('Assembly failed'),
      );

      const request = createRequest({ sessionId: validSessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('DRAFT_ASSEMBLY_ERROR');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handleExcludeIncompleteDraft.mockRejectedValueOnce(
        new Error('Something broke'),
      );

      const request = createRequest({ sessionId: validSessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
