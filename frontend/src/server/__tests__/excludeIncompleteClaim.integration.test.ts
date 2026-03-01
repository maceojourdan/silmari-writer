/**
 * excludeIncompleteClaim.integration.test.ts — Terminal Condition
 *
 * Full integration test for the exclude-incomplete-claim-during-draft-generation
 * path. Only the DAO layer is mocked (database boundary). Everything above
 * runs with real implementations.
 *
 * Scenario:
 * - DB seeded with:
 *   - Claim A (CONFIRMED, complete — has metric, scope, context)
 *   - Claim B (CONFIRMED, missing required metadata — no metric, no scope)
 *
 * Execution:
 * - POST draft generation request with { sessionId }
 *
 * Assertions:
 * - HTTP 200
 * - Draft contains Claim A content only
 * - Claim B ID appears in omission report
 * - Omission message explicitly states claim omitted due to missing required structural metadata
 *
 * This proves:
 * - Reachability: Trigger → terminal condition
 * - TypeInvariant: All boundaries respect defined schemas
 * - ErrorConsistency: Incomplete claims excluded safely, not silently included
 *
 * Path: 328-exclude-incomplete-claim-during-draft-generation
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { ConfirmedClaim } from '@/server/data_structures/Claim';
import { ExcludeIncompleteDraftResponseSchema } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// ---------------------------------------------------------------------------
// Only mock the DAO (database boundary)
// ---------------------------------------------------------------------------

vi.mock('../data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getConfirmedClaims: vi.fn(),
    getClaimsByCaseId: vi.fn(),
    getClaimsByStoryRecordId: vi.fn(),
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

// Mock logger to avoid console noise
vi.mock('../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
const mockClaimDAO = vi.mocked(ClaimDAO);

// Real implementations — NOT mocked
import { DraftGenerationService } from '@/server/services/DraftGenerationService';
import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { POST } from '@/app/api/draft/generate/route';

// ---------------------------------------------------------------------------
// Test Data — realistic scenario
// ---------------------------------------------------------------------------

const sessionId = 'session-integration-328-001';

/**
 * Claim A: CONFIRMED and complete (has metric, scope, context)
 * Should be INCLUDED in the draft.
 */
const claimA: ConfirmedClaim = {
  id: 'claim-A',
  sessionId,
  content: 'Increased revenue by 25% through strategic client outreach',
  status: 'CONFIRMED',
  metric: '25% revenue increase',
  scope: 'Q3 2025 sales division',
  context: 'Strategic client outreach program',
  created_at: '2025-08-15T10:00:00.000Z',
  updated_at: '2025-08-15T10:00:00.000Z',
};

/**
 * Claim B: CONFIRMED but incomplete (missing metric and scope)
 * Should be EXCLUDED from the draft, listed in omission report.
 */
const claimB: ConfirmedClaim = {
  id: 'claim-B',
  sessionId,
  content: 'Led cross-functional team of 12 engineers',
  status: 'CONFIRMED',
  metric: undefined,
  scope: undefined,
  context: 'Engineering leadership initiative',
  created_at: '2025-08-15T10:01:00.000Z',
  updated_at: '2025-08-15T10:01:00.000Z',
};

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
// Integration Tests
// ---------------------------------------------------------------------------

describe('Path 328 Integration: exclude-incomplete-claim-during-draft-generation', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path — trigger → draft + omission → response
  // -------------------------------------------------------------------------

  describe('Reachability: Trigger → Service → Response', () => {
    it('should return 200 with draft containing only Claim A and omission report listing Claim B (HTTP layer)', async () => {
      // Seed: one complete claim (A) and one incomplete claim (B)
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB]);

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      // HTTP 200
      expect(response.status).toBe(200);

      // Draft contains Claim A content only
      expect(data.draft).toContain('Increased revenue by 25% through strategic client outreach');
      expect(data.draft).not.toContain('Led cross-functional team');

      // Claim B appears in omission report
      expect(data.omissions).toHaveLength(1);
      expect(data.omissions[0].claimId).toBe('claim-B');

      // Omission message explicitly states claim omitted due to missing required structural metadata
      expect(data.omissions[0].reason).toContain('missing required structural metadata');
      expect(data.omissions[0].reason).toContain('metric');
      expect(data.omissions[0].reason).toContain('scope');
    });

    it('should exercise full chain: Service → Handler → Route', async () => {
      // Direct service call
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB]);
      const serviceResult = await DraftGenerationService.generateDraftExcludingIncomplete(sessionId);
      expect(serviceResult.draftContent).toContain('Increased revenue');
      expect(serviceResult.omissionReport).toHaveLength(1);

      // Handler layer (wraps service)
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB]);
      const handlerResult = await generateDraftHandler.handleExcludeIncompleteDraft(sessionId);
      expect(handlerResult.draft).toContain('Increased revenue');
      expect(handlerResult.omissions).toHaveLength(1);

      // Route layer (wraps handler → returns HTTP response)
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB]);
      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      expect(response.status).toBe(200);
    });

    it('should return 200 with empty draft when all claims are incomplete', async () => {
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimB]);

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.draft).toBe('');
      expect(data.omissions).toHaveLength(1);
    });

    it('should return 200 with no omissions when all claims are complete', async () => {
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA]);

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.draft).toContain('Increased revenue');
      expect(data.omissions).toEqual([]);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: All boundaries respect defined schemas
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Typed response across layers', () => {
    it('should return typed response matching ExcludeIncompleteDraftResponse schema', async () => {
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB]);

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      const parsed = ExcludeIncompleteDraftResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });

    it('should return draft as string and omissions as array', async () => {
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB]);

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(typeof data.draft).toBe('string');
      expect(Array.isArray(data.omissions)).toBe(true);
    });

    it('should validate error response shape for malformed request', async () => {
      const request = createRequest({ sessionId: '' });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data).toHaveProperty('code');
      expect(data).toHaveProperty('message');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: Incomplete claims excluded safely, not silently included
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Incomplete claims excluded safely', () => {
    it('should NOT include incomplete claim B in the draft content', async () => {
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB]);

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      // Claim B's content must NOT appear in draft
      expect(data.draft).not.toContain('Led cross-functional team');
      expect(data.draft).not.toContain('claim-B');

      // But Claim B IS documented in omissions — not silently dropped
      expect(data.omissions.some((o: any) => o.claimId === 'claim-B')).toBe(true);
    });

    it('should return DATA_ACCESS_ERROR when DAO fails', async () => {
      mockClaimDAO.getConfirmedClaims.mockRejectedValueOnce(
        new Error('Database connection refused'),
      );

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('DATA_ACCESS_ERROR');
    });

    it('should return VALIDATION_ERROR for invalid request body', async () => {
      const request = createRequest({ sessionId: '' });
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

    it('should handle multiple incomplete claims with different missing fields', async () => {
      const claimC: ConfirmedClaim = {
        id: 'claim-C',
        sessionId,
        content: 'Reduced operational costs',
        status: 'CONFIRMED',
        metric: '40% cost reduction',
        scope: undefined,         // missing
        context: undefined,       // missing
        created_at: '2025-08-15T10:02:00.000Z',
        updated_at: '2025-08-15T10:02:00.000Z',
      };

      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([claimA, claimB, claimC]);

      const request = createRequest({ sessionId });
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(200);
      // Only Claim A in draft
      expect(data.draft).toContain('Increased revenue');
      expect(data.draft).not.toContain('Led cross-functional team');
      expect(data.draft).not.toContain('Reduced operational costs');

      // Both B and C in omissions
      expect(data.omissions).toHaveLength(2);
      const omissionIds = data.omissions.map((o: any) => o.claimId);
      expect(omissionIds).toContain('claim-B');
      expect(omissionIds).toContain('claim-C');

      // Claim B missing metric, scope
      const bOmission = data.omissions.find((o: any) => o.claimId === 'claim-B');
      expect(bOmission.reason).toContain('metric');
      expect(bOmission.reason).toContain('scope');

      // Claim C missing scope, context
      const cOmission = data.omissions.find((o: any) => o.claimId === 'claim-C');
      expect(cOmission.reason).toContain('scope');
      expect(cOmission.reason).toContain('context');
    });
  });
});
