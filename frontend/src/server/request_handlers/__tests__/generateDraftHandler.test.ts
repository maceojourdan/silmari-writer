/**
 * Tests for generateDraftHandler
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 325-generate-draft-from-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Valid claimSetId → DraftGenerationService.generate() called → draft returned
 * - TypeInvariant: Response matches GenerateDraftResponse schema
 * - ErrorConsistency: Service errors are re-thrown; unexpected errors are wrapped
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { GenerateDraftResponseSchema } from '@/server/data_structures/StoryStructures';
import type { StructuredDraft, StoryClaim } from '@/server/data_structures/StoryStructures';
import { DraftError, DraftGenerationError } from '@/server/error_definitions/DraftErrors';
import { SharedError, SharedErrors } from '@/server/error_definitions/SharedErrors';

// Mock the service
vi.mock('@/server/services/DraftGenerationService', () => ({
  DraftGenerationService: {
    generate: vi.fn(),
    retrieveConfirmedClaims: vi.fn(),
    transformClaimsToDraft: vi.fn(),
    persistDraft: vi.fn(),
  },
}));

import { generateDraftHandler } from '../generateDraftHandler';
import { DraftGenerationService } from '@/server/services/DraftGenerationService';

const mockService = vi.mocked(DraftGenerationService);

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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('generateDraftHandler — Step 2', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DraftGenerationService.generate with claimSetId', async () => {
      const mockDraft = createMockDraft();
      mockService.generate.mockResolvedValueOnce(mockDraft);

      await generateDraftHandler.handle(validClaimSetId);

      expect(mockService.generate).toHaveBeenCalledWith(validClaimSetId);
    });

    it('should return the generated draft wrapped in response', async () => {
      const mockDraft = createMockDraft();
      mockService.generate.mockResolvedValueOnce(mockDraft);

      const result = await generateDraftHandler.handle(validClaimSetId);

      expect(result.draft).toEqual(mockDraft);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching GenerateDraftResponse schema', async () => {
      const mockDraft = createMockDraft();
      mockService.generate.mockResolvedValueOnce(mockDraft);

      const result = await generateDraftHandler.handle(validClaimSetId);

      const parsed = GenerateDraftResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should re-throw DraftError from service', async () => {
      const error = DraftGenerationError.CLAIM_SET_NOT_FOUND();
      mockService.generate.mockRejectedValueOnce(error);

      await expect(generateDraftHandler.handle(validClaimSetId)).rejects.toThrow(
        DraftError,
      );

      try {
        mockService.generate.mockRejectedValueOnce(error);
        await generateDraftHandler.handle(validClaimSetId);
      } catch (e) {
        expect((e as DraftError).code).toBe('CLAIM_SET_NOT_FOUND');
      }
    });

    it('should wrap unexpected errors as RESPONSE_TRANSFORM_FAILED', async () => {
      mockService.generate.mockRejectedValueOnce(new Error('unexpected'));

      await expect(generateDraftHandler.handle(validClaimSetId)).rejects.toThrow(
        DraftError,
      );

      try {
        mockService.generate.mockRejectedValueOnce(new Error('unexpected'));
        await generateDraftHandler.handle(validClaimSetId);
      } catch (e) {
        expect((e as DraftError).code).toBe('RESPONSE_TRANSFORM_FAILED');
      }
    });

    it('should re-throw SharedError from service (e.g. TRANSFORMATION_ERROR)', async () => {
      const error = SharedErrors.TransformationError('Claim has invalid section');
      mockService.generate.mockRejectedValueOnce(error);

      await expect(generateDraftHandler.handle(validClaimSetId)).rejects.toThrow(
        SharedError,
      );

      try {
        mockService.generate.mockRejectedValueOnce(error);
        await generateDraftHandler.handle(validClaimSetId);
      } catch (e) {
        expect((e as SharedError).code).toBe('TRANSFORMATION_ERROR');
        expect((e as SharedError).statusCode).toBe(422);
      }
    });
  });
});
