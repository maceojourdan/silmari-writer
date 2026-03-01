/**
 * FinalizeProcessor.validate.test.ts - Step 2: Validate Draft Approval State
 *
 * TLA+ Properties:
 * - Reachability: Mock DAO returning draft { status: "APPROVED" } → validateApprovedDraft → returns Draft
 * - TypeInvariant: Returned object matches Draft type
 * - ErrorConsistency: DAO null → DraftNotFound; DAO { status: "DRAFT" } → InvalidDraftState
 *
 * Resource: db-b7r2 (processor)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftSchema } from '@/server/data_structures/Draft';
import { FinalizeError } from '@/server/error_definitions/FinalizeErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

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

import { FinalizeProcessor } from '../FinalizeProcessor';
import { DraftDAO } from '../../data_access_objects/DraftDAO';

const mockDAO = vi.mocked(DraftDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const draftId = '660e8400-e29b-41d4-a716-446655440001';
const userId = '770e8400-e29b-41d4-a716-446655440002';

const approvedDraft = {
  id: draftId,
  status: 'APPROVED' as const,
  content: 'This is an approved draft content.',
  title: 'My Story',
  userId,
  createdAt: '2026-02-28T10:00:00.000Z',
  updatedAt: '2026-02-28T11:00:00.000Z',
  approvedAt: '2026-02-28T11:00:00.000Z',
  interactionData: {
    editsCount: 5,
    revisionsCount: 2,
    claimsVerified: 3,
    totalClaims: 4,
    signalEvents: 10,
  },
};

const draftInDraftState = {
  ...approvedDraft,
  status: 'DRAFT' as const,
  approvedAt: undefined,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeProcessor.validateApprovedDraft — Step 2: Validate Draft Approval State', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return the draft when status is APPROVED', async () => {
      mockDAO.getDraftById.mockResolvedValue(approvedDraft);

      const result = await FinalizeProcessor.validateApprovedDraft(draftId);

      expect(mockDAO.getDraftById).toHaveBeenCalledWith(draftId);
      expect(result).toEqual(approvedDraft);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object conforming to Draft schema', async () => {
      mockDAO.getDraftById.mockResolvedValue(approvedDraft);

      const result = await FinalizeProcessor.validateApprovedDraft(draftId);
      const parsed = DraftSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw DraftNotFound when DAO returns null', async () => {
      mockDAO.getDraftById.mockResolvedValue(null);

      try {
        await FinalizeProcessor.validateApprovedDraft(draftId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeError);
        expect((e as FinalizeError).code).toBe('DRAFT_NOT_FOUND');
        expect((e as FinalizeError).statusCode).toBe(404);
      }
    });

    it('should throw InvalidDraftState when status is DRAFT', async () => {
      mockDAO.getDraftById.mockResolvedValue(draftInDraftState);

      try {
        await FinalizeProcessor.validateApprovedDraft(draftId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeError);
        expect((e as FinalizeError).code).toBe('INVALID_DRAFT_STATE');
        expect((e as FinalizeError).statusCode).toBe(422);
      }
    });

    it('should throw InvalidDraftState when status is FINALIZED', async () => {
      mockDAO.getDraftById.mockResolvedValue({
        ...approvedDraft,
        status: 'FINALIZED' as const,
      });

      try {
        await FinalizeProcessor.validateApprovedDraft(draftId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(FinalizeError);
        expect((e as FinalizeError).code).toBe('INVALID_DRAFT_STATE');
      }
    });
  });
});
