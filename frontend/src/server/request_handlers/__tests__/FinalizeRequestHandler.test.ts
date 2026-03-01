/**
 * FinalizeRequestHandler.test.ts - Step 5: Return Export Response to User
 *
 * TLA+ Properties:
 * - Reachability: Mock processor returning artifact + FINALIZED → handler → HTTP 200 with response
 * - TypeInvariant: Response matches FinalizeResponse schema
 * - ErrorConsistency: Processor throws FinalizeErrors → mapped HTTP error; logged via backend_logging
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeResponseSchema } from '@/api_contracts/finalize';
import { FinalizeError } from '@/server/error_definitions/FinalizeErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../processors/FinalizeProcessor', () => ({
  FinalizeProcessor: {
    finalizeDraft: vi.fn(),
    computeAndLogMetrics: vi.fn(),
    validateApprovedDraft: vi.fn(),
    transformToArtifact: vi.fn(),
    computeMetrics: vi.fn(),
  },
}));

vi.mock('../../data_access_objects/DraftDAO', () => ({
  DraftDAO: {
    getDraftById: vi.fn(),
    updateStatus: vi.fn(),
    insertMetrics: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('../../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FinalizeRequestHandler } from '../FinalizeRequestHandler';
import { FinalizeProcessor } from '../../processors/FinalizeProcessor';
import { DraftDAO } from '../../data_access_objects/DraftDAO';
import { logger } from '../../logging/logger';

const mockProcessor = vi.mocked(FinalizeProcessor);
const mockDAO = vi.mocked(DraftDAO);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const draftId = '660e8400-e29b-41d4-a716-446655440001';
const userId = '770e8400-e29b-41d4-a716-446655440002';

const artifact = {
  draftId,
  content: 'Finalized content here',
  title: 'My Story',
  exportedAt: '2026-02-28T12:02:00.000Z',
  format: 'text' as const,
  metadata: {
    userId,
    originalCreatedAt: '2026-02-28T10:00:00.000Z',
    finalizedAt: '2026-02-28T12:02:00.000Z',
  },
};

const finalizedDraft = {
  id: draftId,
  status: 'FINALIZED' as const,
  content: 'Finalized content here',
  title: 'My Story',
  userId,
  createdAt: '2026-02-28T10:00:00.000Z',
  updatedAt: '2026-02-28T12:02:00.000Z',
  approvedAt: '2026-02-28T11:00:00.000Z',
  finalizedAt: '2026-02-28T12:02:00.000Z',
  interactionData: {
    editsCount: 5,
    revisionsCount: 2,
    claimsVerified: 3,
    totalClaims: 4,
    signalEvents: 10,
  },
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeRequestHandler — Step 5: Return Export Response', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockProcessor.finalizeDraft.mockResolvedValue({
      artifact,
      status: 'FINALIZED',
    });
    mockDAO.getDraftById.mockResolvedValue(finalizedDraft);
    mockProcessor.computeAndLogMetrics.mockResolvedValue(true);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call processor.finalizeDraft and computeAndLogMetrics', async () => {
      const result = await FinalizeRequestHandler.handle(draftId, userId);

      expect(mockProcessor.finalizeDraft).toHaveBeenCalledWith(draftId);
      expect(mockDAO.getDraftById).toHaveBeenCalledWith(draftId);
      expect(mockProcessor.computeAndLogMetrics).toHaveBeenCalledWith(finalizedDraft);
      expect(result.finalized).toBe(true);
      expect(result.metricsLogged).toBe(true);
    });

    it('should return full response with artifact', async () => {
      const result = await FinalizeRequestHandler.handle(draftId, userId);

      expect(result.artifact).toEqual(artifact);
      expect(result.finalized).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return response conforming to FinalizeResponse schema', async () => {
      const result = await FinalizeRequestHandler.handle(draftId, userId);
      const parsed = FinalizeResponseSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow FinalizeError as-is', async () => {
      const error = new FinalizeError('Draft not found', 'DRAFT_NOT_FOUND', 404);
      mockProcessor.finalizeDraft.mockRejectedValue(error);

      try {
        await FinalizeRequestHandler.handle(draftId, userId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeError);
        expect((e as FinalizeError).code).toBe('DRAFT_NOT_FOUND');
        expect((e as FinalizeError).statusCode).toBe(404);
      }
    });

    it('should wrap unknown errors in GenericError', async () => {
      mockProcessor.finalizeDraft.mockRejectedValue(new Error('Something unexpected'));

      try {
        await FinalizeRequestHandler.handle(draftId, userId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }
    });

    it('should log unknown errors via backend_logging', async () => {
      mockProcessor.finalizeDraft.mockRejectedValue(new Error('Something unexpected'));

      try {
        await FinalizeRequestHandler.handle(draftId, userId);
      } catch {
        // expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Unexpected error during finalization'),
        expect.any(Error),
        expect.objectContaining({
          path: '300-finalize-approved-draft-and-log-metrics',
          resource: 'api-n8k2',
        }),
      );
    });

    it('should still return metricsLogged: false when metrics fail but finalization succeeds', async () => {
      mockProcessor.computeAndLogMetrics.mockResolvedValue(false);

      const result = await FinalizeRequestHandler.handle(draftId, userId);

      expect(result.finalized).toBe(true);
      expect(result.metricsLogged).toBe(false);
    });
  });
});
