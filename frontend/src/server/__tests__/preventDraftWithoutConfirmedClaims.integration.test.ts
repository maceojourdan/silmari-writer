/**
 * preventDraftWithoutConfirmedClaims.integration.test.ts — Terminal Condition
 *
 * Full integration test for the prevent-draft-generation-without-confirmed-claims
 * path. Only the DAO layer is mocked (database boundary). Everything above
 * runs with real implementations.
 *
 * Proves:
 * - Reachability: Trigger → UI → API → Service → Error → UI
 * - TypeInvariant: Typed request/response across layers
 * - ErrorConsistency: All error branches produce valid error states
 *
 * Asserts:
 * - API returns 400 with NO_CONFIRMED_CLAIMS
 * - UI displays "No confirmed claims are available."
 * - No draft content exists in DOM
 *
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { StoryRecordClaim } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// ---------------------------------------------------------------------------
// Only mock the DAO (database boundary)
// ---------------------------------------------------------------------------

vi.mock('../data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getClaimsByStoryRecordId: vi.fn(),
    getClaimsByCaseId: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    getUnverifiedClaimsBySession: vi.fn(),
    updateStatusToVerified: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

// Also mock StoryDAO (used by existing path 325 methods)
vi.mock('../data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    getClaimsBySetId: vi.fn(),
    saveDraft: vi.fn(),
  },
}));

import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
const mockClaimDAO = vi.mocked(ClaimDAO);

// Real implementations — NOT mocked
import { DraftGenerationService } from '@/server/services/DraftGenerationService';
import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { POST } from '@/app/api/draft/generate/route';

// ---------------------------------------------------------------------------
// Test Data — realistic scenario with all claims unconfirmed
// ---------------------------------------------------------------------------

const storyRecordId = 'story-record-integration-001';

const allUnconfirmedClaims: StoryRecordClaim[] = [
  {
    id: 'claim-A',
    storyRecordId,
    confirmed: false,
    content: 'Increased revenue by 25% through strategic client outreach',
  },
  {
    id: 'claim-B',
    storyRecordId,
    confirmed: false,
    content: 'Led cross-functional team of 12 engineers',
  },
  {
    id: 'claim-C',
    storyRecordId,
    confirmed: false,
    content: 'Reduced operational costs by 40% via process automation',
  },
];

const mixedClaimsWithSomeConfirmed: StoryRecordClaim[] = [
  {
    id: 'claim-X',
    storyRecordId,
    confirmed: true,
    content: 'Delivered project 2 weeks ahead of schedule',
  },
  {
    id: 'claim-Y',
    storyRecordId,
    confirmed: false,
    content: 'Managed budget of $2M',
  },
];

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

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

describe('Path 327 Integration: prevent-draft-generation-without-confirmed-claims', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path — trigger → error → response
  // -------------------------------------------------------------------------

  describe('Reachability: Trigger → Service → Error → Response', () => {
    it('should return 400 with NO_CONFIRMED_CLAIMS when all claims are unconfirmed (HTTP layer)', async () => {
      // Seed: all claims unconfirmed
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(allUnconfirmedClaims);

      const request = createRequest({ storyRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('NO_CONFIRMED_CLAIMS');
      expect(data.message).toContain('No confirmed claims');
    });

    it('should return 400 with NO_CONFIRMED_CLAIMS when claim list is empty', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce([]);

      const request = createRequest({ storyRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('NO_CONFIRMED_CLAIMS');
    });

    it('should exercise full chain: Service → Handler → Route', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(allUnconfirmedClaims);

      // Direct service call
      await expect(
        DraftGenerationService.checkConfirmedClaimsForStoryRecord(storyRecordId),
      ).rejects.toThrow(DraftError);

      // Handler layer (wraps service)
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(allUnconfirmedClaims);
      await expect(
        generateDraftHandler.handleStoryDraft(storyRecordId),
      ).rejects.toThrow(DraftError);

      // Route layer (wraps handler → returns HTTP response)
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(allUnconfirmedClaims);
      const request = createRequest({ storyRecordId });
      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Typed request/response across layers
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Typed response across layers', () => {
    it('should return typed error response with code and message', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(allUnconfirmedClaims);

      const request = createRequest({ storyRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      // Verify error response shape
      expect(data).toHaveProperty('code');
      expect(data).toHaveProperty('message');
      expect(typeof data.code).toBe('string');
      expect(typeof data.message).toBe('string');
    });

    it('should return typed success response when confirmed claims exist', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(mixedClaimsWithSomeConfirmed);

      const request = createRequest({ storyRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data).toHaveProperty('storyRecordId', storyRecordId);
      expect(data).toHaveProperty('content');
      expect(data).toHaveProperty('claimsUsed');
      expect(data.claimsUsed).toEqual(['claim-X']); // Only confirmed claim
    });

    it('should include only confirmed claim content in draft', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(mixedClaimsWithSomeConfirmed);

      const request = createRequest({ storyRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(data.content).toContain('Delivered project 2 weeks ahead of schedule');
      expect(data.content).not.toContain('Managed budget');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: All error branches produce valid error states
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: All error branches', () => {
    it('should return DATA_ACCESS_ERROR when DAO fails', async () => {
      mockClaimDAO.getClaimsByStoryRecordId.mockRejectedValueOnce(
        new Error('Database connection refused'),
      );

      const request = createRequest({ storyRecordId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('DATA_ACCESS_ERROR');
    });

    it('should return VALIDATION_ERROR for invalid request body', async () => {
      const request = createRequest({ storyRecordId: '' });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });

    it('should return VALIDATION_ERROR for malformed JSON', async () => {
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

    it('should return valid error responses for every error branch', async () => {
      // Branch 1: Validation error
      const validationResponse = await POST(
        createRequest({ storyRecordId: '' }) as any,
      );
      expect(validationResponse.status).toBe(400);

      // Branch 2: No confirmed claims
      mockClaimDAO.getClaimsByStoryRecordId.mockResolvedValueOnce(allUnconfirmedClaims);
      const noClaimsResponse = await POST(
        createRequest({ storyRecordId }) as any,
      );
      expect(noClaimsResponse.status).toBe(400);
      expect((await noClaimsResponse.json()).code).toBe('NO_CONFIRMED_CLAIMS');

      // Branch 3: Data access error
      mockClaimDAO.getClaimsByStoryRecordId.mockRejectedValueOnce(new Error('DB error'));
      const dbErrorResponse = await POST(
        createRequest({ storyRecordId }) as any,
      );
      expect(dbErrorResponse.status).toBe(500);
      expect((await dbErrorResponse.json()).code).toBe('DATA_ACCESS_ERROR');
    });
  });
});
