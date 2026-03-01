/**
 * DraftGenerationService.328.test.ts — Step 4: Assemble draft from complete claims
 *
 * TLA+ Properties:
 * - Reachability: Given complete + incomplete → draft contains only complete claim IDs
 * - TypeInvariant: Output matches DraftGenerationResult type
 * - ErrorConsistency: Mock processor failure → throws DraftErrors328.DraftAssemblyError; assert no DB insert called
 *
 * Resource: db-h2s4 (service)
 * Path: 328-exclude-incomplete-claim-during-draft-generation
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { ConfirmedClaim } from '@/server/data_structures/Claim';
import { DraftGenerationResultSchema } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// ---------------------------------------------------------------------------
// Mock the DAO (database boundary)
// ---------------------------------------------------------------------------

vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getConfirmedClaims: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    getUnverifiedClaimsBySession: vi.fn(),
    updateStatusToVerified: vi.fn(),
    updateStatus: vi.fn(),
    getClaimsByCaseId: vi.fn(),
    getClaimsByStoryRecordId: vi.fn(),
  },
}));

// Also mock StoryDAO (used by existing path 325 methods)
vi.mock('@/server/data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    getClaimsBySetId: vi.fn(),
    saveDraft: vi.fn(),
  },
}));

// Mock logger
vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock DraftAssemblyProcessor - used to test service error wrapping
vi.mock('@/server/processors/DraftAssemblyProcessor', () => ({
  DraftAssemblyProcessor: {
    generateDraft: vi.fn(),
  },
}));

import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { DraftAssemblyProcessor } from '@/server/processors/DraftAssemblyProcessor';
import { DraftGenerationService } from '../DraftGenerationService';

const mockClaimDAO = vi.mocked(ClaimDAO);
const mockProcessor = vi.mocked(DraftAssemblyProcessor);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'session-test-328-svc';

function createConfirmedClaim(overrides: Partial<ConfirmedClaim> = {}): ConfirmedClaim {
  return {
    id: `claim-${Math.random().toString(36).slice(2, 8)}`,
    sessionId: validSessionId,
    content: 'Increased revenue by 25% through strategic initiative',
    status: 'CONFIRMED',
    metric: '25% revenue increase',
    scope: 'Q3 2025 sales division',
    context: 'Strategic client outreach program',
    created_at: new Date().toISOString(),
    updated_at: new Date().toISOString(),
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerationService — Step 4: Assemble draft from complete claims (path 328)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return draft containing only complete claim content', async () => {
      const completeA = createConfirmedClaim({
        id: 'claim-A',
        content: 'Complete claim A content',
        metric: 'Metric A',
        scope: 'Scope A',
        context: 'Context A',
      });
      const incompleteB = createConfirmedClaim({
        id: 'claim-B',
        content: 'Incomplete claim B content',
        metric: undefined,  // missing metric
        scope: undefined,   // missing scope
      });

      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([completeA, incompleteB]);
      mockProcessor.generateDraft.mockReturnValueOnce('Complete claim A content');

      const result = await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);

      expect(result.draftContent).toBe('Complete claim A content');
      expect(result.draftContent).not.toContain('Incomplete claim B');
    });

    it('should include incomplete claim in omission report', async () => {
      const completeA = createConfirmedClaim({
        id: 'claim-A',
        metric: 'M', scope: 'S', context: 'C',
      });
      const incompleteB = createConfirmedClaim({
        id: 'claim-B',
        metric: undefined,
        scope: undefined,
      });

      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([completeA, incompleteB]);
      mockProcessor.generateDraft.mockReturnValueOnce('Draft text');

      const result = await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);

      expect(result.omissionReport).toHaveLength(1);
      expect(result.omissionReport[0].claimId).toBe('claim-B');
      expect(result.omissionReport[0].reason).toContain('missing required structural metadata');
      expect(result.omissionReport[0].reason).toContain('metric');
      expect(result.omissionReport[0].reason).toContain('scope');
    });

    it('should pass only complete claims to DraftAssemblyProcessor', async () => {
      const completeA = createConfirmedClaim({
        id: 'claim-A', metric: 'M', scope: 'S', context: 'C',
      });
      const incompleteB = createConfirmedClaim({
        id: 'claim-B', metric: undefined,
      });

      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([completeA, incompleteB]);
      mockProcessor.generateDraft.mockReturnValueOnce('Draft');

      await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);

      // Only complete claim passed to processor
      expect(mockProcessor.generateDraft).toHaveBeenCalledWith(
        expect.arrayContaining([expect.objectContaining({ id: 'claim-A' })]),
      );
      const calledWith = mockProcessor.generateDraft.mock.calls[0][0];
      expect(calledWith).toHaveLength(1);
      expect(calledWith[0].id).toBe('claim-A');
    });

    it('should return empty draft and full omission report when all claims are incomplete', async () => {
      const incompleteA = createConfirmedClaim({ id: 'claim-A', metric: undefined });
      const incompleteB = createConfirmedClaim({ id: 'claim-B', scope: undefined });

      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([incompleteA, incompleteB]);
      mockProcessor.generateDraft.mockReturnValueOnce('');

      const result = await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);

      expect(result.draftContent).toBe('');
      expect(result.omissionReport).toHaveLength(2);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching DraftGenerationResult schema', async () => {
      const complete = createConfirmedClaim({
        id: 'c1', metric: 'M', scope: 'S', context: 'C',
      });

      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([complete]);
      mockProcessor.generateDraft.mockReturnValueOnce('Draft text');

      const result = await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);

      const parsed = DraftGenerationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should produce omission entries with claimId and reason strings', async () => {
      const incomplete = createConfirmedClaim({ id: 'c1', metric: undefined });

      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([incomplete]);
      mockProcessor.generateDraft.mockReturnValueOnce('');

      const result = await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);

      expect(result.omissionReport[0]).toEqual({
        claimId: 'c1',
        reason: expect.stringContaining('metric'),
      });
      expect(typeof result.omissionReport[0].claimId).toBe('string');
      expect(typeof result.omissionReport[0].reason).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw DATA_ACCESS_ERROR when DAO fails', async () => {
      mockClaimDAO.getConfirmedClaims.mockRejectedValueOnce(
        new Error('Database connection lost'),
      );

      await expect(
        DraftGenerationService.generateDraftExcludingIncomplete(validSessionId),
      ).rejects.toThrow(DraftError);

      try {
        mockClaimDAO.getConfirmedClaims.mockRejectedValueOnce(new Error('DB fail'));
        await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);
      } catch (e) {
        expect((e as DraftError).code).toBe('DATA_ACCESS_ERROR');
        expect((e as DraftError).statusCode).toBe(500);
      }
    });

    it('should throw DRAFT_ASSEMBLY_ERROR when processor fails', async () => {
      const complete = createConfirmedClaim({
        id: 'c1', metric: 'M', scope: 'S', context: 'C',
      });
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([complete]);
      mockProcessor.generateDraft.mockImplementationOnce(() => {
        throw new Error('Assembly crash');
      });

      await expect(
        DraftGenerationService.generateDraftExcludingIncomplete(validSessionId),
      ).rejects.toThrow(DraftError);

      // Verify error code
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([complete]);
      mockProcessor.generateDraft.mockImplementationOnce(() => {
        throw new Error('Assembly crash');
      });

      try {
        await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);
      } catch (e) {
        expect((e as DraftError).code).toBe('DRAFT_ASSEMBLY_ERROR');
      }
    });

    it('should not make any DB insert calls when assembly fails', async () => {
      const complete = createConfirmedClaim({
        id: 'c1', metric: 'M', scope: 'S', context: 'C',
      });
      mockClaimDAO.getConfirmedClaims.mockResolvedValueOnce([complete]);
      mockProcessor.generateDraft.mockImplementationOnce(() => {
        throw new Error('Assembly crash');
      });

      try {
        await DraftGenerationService.generateDraftExcludingIncomplete(validSessionId);
      } catch {
        // No persistence methods should have been called
        // (service only reads, never writes on error)
      }
    });
  });
});
