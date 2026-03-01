/**
 * Tests for POST /api/draft/generate (path 327)
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: POST valid { storyRecordId } → handler invoked → 200
 * - TypeInvariant: Invalid body (missing storyRecordId) → 400 with VALIDATION_ERROR
 * - ErrorConsistency:
 *   - NO_CONFIRMED_CLAIMS → 400 with structured error
 *   - Unexpected error → 500 with INTERNAL_ERROR
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { GenerateStoryDraftResponse } from '@/server/data_structures/Claim';
import { DraftErrors327 } from '@/server/error_definitions/DraftErrors';

// Mock the request handler
vi.mock('@/server/request_handlers/generateDraftHandler', () => ({
  generateDraftHandler: {
    handle: vi.fn(),
    handleCaseDraft: vi.fn(),
    handleStoryDraft: vi.fn(),
  },
}));

import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { POST } from '../route';

const mockHandler = vi.mocked(generateDraftHandler);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validStoryRecordId = 'story-record-abc-123';

function createMockStoryDraft(
  overrides: Partial<GenerateStoryDraftResponse> = {},
): GenerateStoryDraftResponse {
  return {
    storyRecordId: validStoryRecordId,
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

describe('POST /api/draft/generate — Step 2 (path 327: storyRecordId)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with draft data when storyRecordId provided', async () => {
      const mockDraft = createMockStoryDraft();
      mockHandler.handleStoryDraft.mockResolvedValueOnce(mockDraft);

      const request = createRequest({ storyRecordId: validStoryRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.storyRecordId).toBe(validStoryRecordId);
      expect(data.content).toBeDefined();
      expect(data.claimsUsed).toBeDefined();
    });

    it('should call handleStoryDraft with storyRecordId from request body', async () => {
      const mockDraft = createMockStoryDraft();
      mockHandler.handleStoryDraft.mockResolvedValueOnce(mockDraft);

      const request = createRequest({ storyRecordId: validStoryRecordId });
      await POST(request as any);

      expect(mockHandler.handleStoryDraft).toHaveBeenCalledWith(validStoryRecordId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return 400 for empty storyRecordId', async () => {
      const request = createRequest({ storyRecordId: '' });
      const response = await POST(request as any);

      expect(response.status).toBe(400);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 400 with NO_CONFIRMED_CLAIMS when handler throws NoConfirmedClaimsError', async () => {
      mockHandler.handleStoryDraft.mockRejectedValueOnce(
        DraftErrors327.NoConfirmedClaimsError('No confirmed claims are available.'),
      );

      const request = createRequest({ storyRecordId: validStoryRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('NO_CONFIRMED_CLAIMS');
      expect(data.message).toContain('No confirmed claims');
    });

    it('should return 500 with DATA_ACCESS_ERROR when handler throws DataAccessError', async () => {
      mockHandler.handleStoryDraft.mockRejectedValueOnce(
        DraftErrors327.DataAccessError('DB connection lost'),
      );

      const request = createRequest({ storyRecordId: validStoryRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('DATA_ACCESS_ERROR');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handleStoryDraft.mockRejectedValueOnce(
        new Error('Something broke'),
      );

      const request = createRequest({ storyRecordId: validStoryRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
