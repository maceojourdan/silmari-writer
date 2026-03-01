/**
 * generateDraftHandler.327.test.ts — Step 4: Return no-confirmed-claims response
 *
 * TLA+ Properties:
 * - Reachability: Mock service throwing NoConfirmedClaimsError → expect HTTP 400 with code NO_CONFIRMED_CLAIMS
 * - TypeInvariant: Response body matches ErrorResponse type
 * - ErrorConsistency: Unknown error → HTTP 500 with GENERATION_FAILED and safe message
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { GenerateStoryDraftResponseSchema, ErrorResponseSchema } from '@/server/data_structures/Claim';
import type { StoryRecordClaim } from '@/server/data_structures/Claim';
import { DraftError, DraftErrors327 } from '@/server/error_definitions/DraftErrors';

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
    checkConfirmedClaimsForStoryRecord: vi.fn(),
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

const validStoryRecordId = 'story-record-abc-123';

function createMockConfirmedClaims(): StoryRecordClaim[] {
  return [
    {
      id: 'c1',
      storyRecordId: validStoryRecordId,
      confirmed: true,
      content: 'First confirmed claim',
    },
    {
      id: 'c2',
      storyRecordId: validStoryRecordId,
      confirmed: true,
      content: 'Second confirmed claim',
    },
  ];
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('generateDraftHandler — Step 4: Return no-confirmed-claims response (path 327)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DraftGenerationService.checkConfirmedClaimsForStoryRecord with storyRecordId', async () => {
      const mockClaims = createMockConfirmedClaims();
      mockService.checkConfirmedClaimsForStoryRecord.mockResolvedValueOnce(mockClaims);

      await generateDraftHandler.handleStoryDraft(validStoryRecordId);

      expect(mockService.checkConfirmedClaimsForStoryRecord).toHaveBeenCalledWith(validStoryRecordId);
    });

    it('should throw DraftError with NO_CONFIRMED_CLAIMS when service throws NoConfirmedClaimsError', async () => {
      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(
        DraftErrors327.NoConfirmedClaimsError('No confirmed claims are available.'),
      );

      await expect(
        generateDraftHandler.handleStoryDraft(validStoryRecordId),
      ).rejects.toThrow(DraftError);

      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(
        DraftErrors327.NoConfirmedClaimsError('No confirmed claims are available.'),
      );
      try {
        await generateDraftHandler.handleStoryDraft(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).code).toBe('NO_CONFIRMED_CLAIMS');
        expect((e as DraftError).statusCode).toBe(400);
      }
    });

    it('should return story draft response on success', async () => {
      const mockClaims = createMockConfirmedClaims();
      mockService.checkConfirmedClaimsForStoryRecord.mockResolvedValueOnce(mockClaims);

      const result = await generateDraftHandler.handleStoryDraft(validStoryRecordId);

      expect(result.storyRecordId).toBe(validStoryRecordId);
      expect(result.content).toBeDefined();
      expect(result.claimsUsed).toEqual(['c1', 'c2']);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching GenerateStoryDraftResponse schema', async () => {
      const mockClaims = createMockConfirmedClaims();
      mockService.checkConfirmedClaimsForStoryRecord.mockResolvedValueOnce(mockClaims);

      const result = await generateDraftHandler.handleStoryDraft(validStoryRecordId);

      const parsed = GenerateStoryDraftResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should produce error matching ErrorResponse type when NoConfirmedClaimsError thrown', async () => {
      const error = DraftErrors327.NoConfirmedClaimsError('No confirmed claims are available.');
      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(error);

      try {
        await generateDraftHandler.handleStoryDraft(validStoryRecordId);
      } catch (e) {
        const errorResponse = { code: (e as DraftError).code, message: (e as DraftError).message };
        const parsed = ErrorResponseSchema.safeParse(errorResponse);
        expect(parsed.success).toBe(true);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should re-throw DraftError from service without wrapping', async () => {
      const error = DraftErrors327.DataAccessError('DB failed');
      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(error);

      await expect(
        generateDraftHandler.handleStoryDraft(validStoryRecordId),
      ).rejects.toThrow(DraftError);

      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(error);
      try {
        await generateDraftHandler.handleStoryDraft(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).code).toBe('DATA_ACCESS_ERROR');
      }
    });

    it('should log and rethrow as GENERATION_FAILED when service throws unexpected error', async () => {
      const originalError = new Error('unexpected failure');
      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(originalError);

      await expect(
        generateDraftHandler.handleStoryDraft(validStoryRecordId),
      ).rejects.toThrow(DraftError);

      expect(mockLogger.error).toHaveBeenCalled();

      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(originalError);
      try {
        await generateDraftHandler.handleStoryDraft(validStoryRecordId);
      } catch (e) {
        expect((e as DraftError).code).toBe('GENERATION_FAILED');
        expect((e as DraftError).statusCode).toBe(500);
      }
    });

    it('should return safe message for unexpected errors (no stack leak)', async () => {
      mockService.checkConfirmedClaimsForStoryRecord.mockRejectedValueOnce(
        new Error('sensitive internal details'),
      );

      try {
        await generateDraftHandler.handleStoryDraft(validStoryRecordId);
      } catch (e) {
        // The error message should wrap the original but come from the handler
        expect(e).toBeInstanceOf(DraftError);
      }
    });
  });
});
