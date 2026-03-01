/**
 * generateDraftHandler.326.test.ts — Step 3: Orchestrate draft generation (path 326)
 *
 * TLA+ Properties:
 * - Reachability: Mock service → assert DraftGenerationService.generateCaseDraft(caseId) called
 * - TypeInvariant: Assert return type is CaseDraft (matches CaseDraftSchema)
 * - ErrorConsistency: Service throw → assert backend/logging.error called, error rethrown as DraftErrors326.GenerationError
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 326-generate-draft-with-only-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { GenerateCaseDraftResponseSchema } from '@/server/data_structures/Claim';
import type { CaseDraft } from '@/server/data_structures/Claim';
import { DraftError, DraftErrors326 } from '@/server/error_definitions/DraftErrors';

// Mock the service
vi.mock('@/server/services/DraftGenerationService', () => ({
  DraftGenerationService: {
    generate: vi.fn(),
    retrieveConfirmedClaims: vi.fn(),
    transformClaimsToDraft: vi.fn(),
    persistDraft: vi.fn(),
    getConfirmedClaimsForCase: vi.fn(),
    composeCaseDraft: vi.fn(),
    generateCaseDraft: vi.fn(),
  },
}));

// Mock the backend logger
vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { generateDraftHandler } from '../generateDraftHandler';
import { DraftGenerationService } from '@/server/services/DraftGenerationService';
import { logger } from '@/server/logging/logger';

const mockService = vi.mocked(DraftGenerationService);
const mockLogger = vi.mocked(logger);

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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('generateDraftHandler — Step 3: Orchestrate draft generation (path 326)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DraftGenerationService.generateCaseDraft with caseId', async () => {
      const mockDraft = createMockCaseDraft();
      mockService.generateCaseDraft.mockResolvedValueOnce(mockDraft);

      await generateDraftHandler.handleCaseDraft(validCaseId);

      expect(mockService.generateCaseDraft).toHaveBeenCalledWith(validCaseId);
    });

    it('should return the generated case draft', async () => {
      const mockDraft = createMockCaseDraft();
      mockService.generateCaseDraft.mockResolvedValueOnce(mockDraft);

      const result = await generateDraftHandler.handleCaseDraft(validCaseId);

      expect(result).toEqual(mockDraft);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching GenerateCaseDraftResponse schema', async () => {
      const mockDraft = createMockCaseDraft();
      mockService.generateCaseDraft.mockResolvedValueOnce(mockDraft);

      const result = await generateDraftHandler.handleCaseDraft(validCaseId);

      const parsed = GenerateCaseDraftResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log error and rethrow as GENERATION_FAILED when service throws unexpected error', async () => {
      const originalError = new Error('unexpected failure');
      mockService.generateCaseDraft.mockRejectedValueOnce(originalError);

      await expect(
        generateDraftHandler.handleCaseDraft(validCaseId),
      ).rejects.toThrow(DraftError);

      expect(mockLogger.error).toHaveBeenCalled();

      try {
        mockService.generateCaseDraft.mockRejectedValueOnce(originalError);
        await generateDraftHandler.handleCaseDraft(validCaseId);
      } catch (e) {
        expect((e as DraftError).code).toBe('GENERATION_FAILED');
      }
    });

    it('should re-throw DraftError from service without wrapping', async () => {
      const error = DraftErrors326.DataAccessError('DB failed');
      mockService.generateCaseDraft.mockRejectedValueOnce(error);

      await expect(
        generateDraftHandler.handleCaseDraft(validCaseId),
      ).rejects.toThrow(DraftError);

      try {
        mockService.generateCaseDraft.mockRejectedValueOnce(error);
        await generateDraftHandler.handleCaseDraft(validCaseId);
      } catch (e) {
        expect((e as DraftError).code).toBe('DATA_ACCESS_ERROR');
      }
    });
  });
});
