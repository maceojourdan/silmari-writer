/**
 * generateDraftHandler.328.test.ts — Step 5: Return draft and omission notice
 *
 * TLA+ Properties:
 * - Reachability: Valid service result → HTTP 200 with { draft, omissions }
 * - TypeInvariant: Response matches frontend contract type
 * - ErrorConsistency: Simulate service failure → DraftErrors328 thrown; logger called
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 328-exclude-incomplete-claim-during-draft-generation
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ExcludeIncompleteDraftResponseSchema } from '@/server/data_structures/Claim';
import type { DraftGenerationResult } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// Mock the service
vi.mock('@/server/services/DraftGenerationService', () => ({
  DraftGenerationService: {
    generateDraftExcludingIncomplete: vi.fn(),
    // Stubs for existing methods
    generate: vi.fn(),
    retrieveConfirmedClaims: vi.fn(),
    transformClaimsToDraft: vi.fn(),
    persistDraft: vi.fn(),
    getConfirmedClaimsForCase: vi.fn(),
    composeCaseDraft: vi.fn(),
    generateCaseDraft: vi.fn(),
    checkConfirmedClaimsForStoryRecord: vi.fn(),
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

import { DraftGenerationService } from '@/server/services/DraftGenerationService';
import { logger } from '@/server/logging/logger';
import { generateDraftHandler } from '../generateDraftHandler';

const mockService = vi.mocked(DraftGenerationService);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'session-test-328-handler';

function createServiceResult(overrides: Partial<DraftGenerationResult> = {}): DraftGenerationResult {
  return {
    draftContent: 'Generated draft content from complete claims.',
    omissionReport: [
      {
        claimId: 'claim-B',
        reason: 'Claim omitted due to missing required structural metadata: metric, scope',
      },
    ],
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('generateDraftHandler — Step 5: Return draft and omission notice (path 328)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return response with draft and omissions on success', async () => {
      const serviceResult = createServiceResult();
      mockService.generateDraftExcludingIncomplete.mockResolvedValueOnce(serviceResult);

      const result = await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);

      expect(result.draft).toBe('Generated draft content from complete claims.');
      expect(result.omissions).toHaveLength(1);
      expect(result.omissions[0].claimId).toBe('claim-B');
    });

    it('should call service with correct sessionId', async () => {
      const serviceResult = createServiceResult();
      mockService.generateDraftExcludingIncomplete.mockResolvedValueOnce(serviceResult);

      await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);

      expect(mockService.generateDraftExcludingIncomplete).toHaveBeenCalledWith(validSessionId);
    });

    it('should return empty omissions array when all claims are complete', async () => {
      const serviceResult = createServiceResult({
        draftContent: 'Full draft',
        omissionReport: [],
      });
      mockService.generateDraftExcludingIncomplete.mockResolvedValueOnce(serviceResult);

      const result = await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);

      expect(result.omissions).toEqual([]);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return response matching ExcludeIncompleteDraftResponse schema', async () => {
      const serviceResult = createServiceResult();
      mockService.generateDraftExcludingIncomplete.mockResolvedValueOnce(serviceResult);

      const result = await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);

      const parsed = ExcludeIncompleteDraftResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should map draftContent to draft and omissionReport to omissions', async () => {
      const serviceResult = createServiceResult({
        draftContent: 'Custom draft content',
        omissionReport: [
          { claimId: 'c1', reason: 'Missing metric' },
          { claimId: 'c2', reason: 'Missing scope' },
        ],
      });
      mockService.generateDraftExcludingIncomplete.mockResolvedValueOnce(serviceResult);

      const result = await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);

      expect(result).toHaveProperty('draft', 'Custom draft content');
      expect(result).toHaveProperty('omissions');
      expect(result.omissions).toHaveLength(2);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should re-throw DraftError from service as-is', async () => {
      const { DraftErrors328 } = await import('@/server/error_definitions/DraftErrors');
      const dataAccessError = DraftErrors328.DataAccessError('DB connection failed');
      mockService.generateDraftExcludingIncomplete.mockRejectedValueOnce(dataAccessError);

      await expect(
        generateDraftHandler.handleExcludeIncompleteDraft(validSessionId),
      ).rejects.toThrow(DraftError);

      mockService.generateDraftExcludingIncomplete.mockRejectedValueOnce(
        DraftErrors328.DataAccessError('DB fail'),
      );

      try {
        await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);
      } catch (e) {
        expect((e as DraftError).code).toBe('DATA_ACCESS_ERROR');
      }
    });

    it('should wrap unexpected errors as SERVER_ERROR and log', async () => {
      const unexpectedError = new Error('Unexpected failure');
      mockService.generateDraftExcludingIncomplete.mockRejectedValueOnce(unexpectedError);

      try {
        await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('SERVER_ERROR');
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        'Exclude-incomplete draft generation failed',
        expect.any(Error),
        expect.objectContaining({ path: '328', resource: 'api-n8k2', sessionId: validSessionId }),
      );
    });

    it('should not log when DraftError is re-thrown', async () => {
      const { DraftErrors328 } = await import('@/server/error_definitions/DraftErrors');
      mockService.generateDraftExcludingIncomplete.mockRejectedValueOnce(
        DraftErrors328.DraftAssemblyError('assembly failed'),
      );

      try {
        await generateDraftHandler.handleExcludeIncompleteDraft(validSessionId);
      } catch {
        // Expected
      }

      // Logger should NOT have been called for DraftError (they're re-thrown directly)
      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });
});
