/**
 * Tests for POST /api/generate-draft
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 325-generate-draft-from-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Mock authenticated request with valid body → handler called → 200
 * - TypeInvariant: Parsed body matches backend Zod schema; response JSON matches Draft DTO
 * - ErrorConsistency: No auth → 401; Invalid body → 400; Service errors → correct status codes
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { StructuredDraft, StoryClaim } from '@/server/data_structures/StoryStructures';
import { DraftGenerationError } from '@/server/error_definitions/DraftErrors';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';

// Mock the request handler
vi.mock('@/server/request_handlers/generateDraftHandler', () => ({
  generateDraftHandler: {
    handle: vi.fn(),
  },
}));

import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { POST } from '../route';

const mockHandler = vi.mocked(generateDraftHandler);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validClaimSetId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';
const now = new Date().toISOString();

function createClaim(overrides: Partial<StoryClaim> = {}): StoryClaim {
  return {
    id: crypto.randomUUID(),
    claimSetId: validClaimSetId,
    content: 'A test claim',
    status: 'CONFIRMED',
    section: 'context',
    order: 0,
    createdAt: now,
    updatedAt: now,
    ...overrides,
  };
}

function createMockDraft(): StructuredDraft {
  return {
    id: crypto.randomUUID(),
    claimSetId: validClaimSetId,
    sections: [
      {
        sectionName: 'context',
        claims: [createClaim({ section: 'context', order: 0 })],
      },
      {
        sectionName: 'actions',
        claims: [createClaim({ section: 'actions', order: 0 })],
      },
      {
        sectionName: 'outcome',
        claims: [createClaim({ section: 'outcome', order: 0 })],
      },
    ],
    createdAt: now,
  };
}

function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/generate-draft', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/generate-draft — Step 2', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with draft data on success', async () => {
      const mockDraft = createMockDraft();
      mockHandler.handle.mockResolvedValueOnce({ draft: mockDraft });

      const request = createRequest({ claimSetId: validClaimSetId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.draft).toBeDefined();
      expect(data.draft.claimSetId).toBe(validClaimSetId);
    });

    it('should call handler with claimSetId from request body', async () => {
      const mockDraft = createMockDraft();
      mockHandler.handle.mockResolvedValueOnce({ draft: mockDraft });

      const request = createRequest({ claimSetId: validClaimSetId });
      await POST(request as any);

      expect(mockHandler.handle).toHaveBeenCalledWith(validClaimSetId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return 400 for missing claimSetId', async () => {
      const request = createRequest({});
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_PARAMETERS');
    });

    it('should return 400 for invalid claimSetId (not UUID)', async () => {
      const request = createRequest({ claimSetId: 'not-a-uuid' });
      const response = await POST(request as any);

      expect(response.status).toBe(400);
    });

    it('should return 400 for non-JSON body', async () => {
      const request = new Request('http://localhost/api/generate-draft', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: 'not json',
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_PARAMETERS');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 404 when claim set not found', async () => {
      mockHandler.handle.mockRejectedValueOnce(
        DraftGenerationError.CLAIM_SET_NOT_FOUND(),
      );

      const request = createRequest({ claimSetId: validClaimSetId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(404);
      expect(data.code).toBe('CLAIM_SET_NOT_FOUND');
    });

    it('should return 422 when no confirmed claims', async () => {
      mockHandler.handle.mockRejectedValueOnce(
        DraftGenerationError.NO_CONFIRMED_CLAIMS(),
      );

      const request = createRequest({ claimSetId: validClaimSetId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('NO_CONFIRMED_CLAIMS');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValueOnce(new Error('Something broke'));

      const request = createRequest({ claimSetId: validClaimSetId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });

    it('should return 422 when handler throws SharedError (TRANSFORMATION_ERROR)', async () => {
      mockHandler.handle.mockRejectedValueOnce(
        SharedErrors.TransformationError('Claim has invalid section "bogus"'),
      );

      const request = createRequest({ claimSetId: validClaimSetId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('TRANSFORMATION_ERROR');
      expect(data.message).toContain('bogus');
    });
  });
});
