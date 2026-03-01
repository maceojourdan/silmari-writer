/**
 * DraftProcessChain.integration.test.ts — Terminal Condition
 *
 * Full integration test for the draft-state-filters-unconfirmed-hard-claims
 * path. Only the DAO layer is mocked (database boundary). Everything above
 * runs with real implementations.
 *
 * Proves:
 * - Reachability: Trigger → terminal (full path from request to response)
 * - TypeInvariant: All step boundaries validated via Zod schemas
 * - ErrorConsistency: All error branches mapped to structured DraftErrors
 *
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftRequestHandler } from '@/server/request_handlers/DraftRequestHandler';
import { DraftResponseSchema } from '@/server/data_structures/DraftStoryRecord';
import type { DraftStoryRecord } from '@/server/data_structures/DraftStoryRecord';
import { DraftError, DraftDataAccessError } from '@/server/error_definitions/DraftErrors';

// ---------------------------------------------------------------------------
// Only mock the DAO (database boundary)
// ---------------------------------------------------------------------------

vi.mock('../data_access_objects/StoryRecordDAO', () => ({
  StoryRecordDAO: {
    findById: vi.fn(),
    updateDraft: vi.fn(),
  },
}));

import { StoryRecordDAO } from '@/server/data_access_objects/StoryRecordDAO';
const mockDAO = vi.mocked(StoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data — realistic scenario
// ---------------------------------------------------------------------------

const storyRecordWithMixedClaims: DraftStoryRecord = {
  id: 'integration-record-001',
  status: 'DRAFT',
  truth_checks: [
    {
      id: 'claim-A',
      text: 'Increased quarterly revenue by 25% through strategic client outreach',
      type: 'hard',
      truth_check: { status: 'confirmed', source: 'Q3 Financial Report' },
    },
    {
      id: 'claim-B',
      text: 'Reduced operational costs by 40% via process automation',
      type: 'hard',
      truth_check: { status: 'denied', source: 'Internal Audit' },
    },
    {
      id: 'claim-C',
      text: 'Led cross-functional team of 12 engineers',
      type: 'soft',
    },
    {
      id: 'claim-D',
      text: 'Achieved 99.9% uptime SLA',
      type: 'hard',
      // No truth_check → missing confirmation metadata → excluded
    },
  ],
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Draft Process Chain — Integration (Terminal Condition)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path from trigger to terminal
  // -------------------------------------------------------------------------

  describe('Reachability: Trigger → terminal', () => {
    it('should produce a draft containing only confirmed hard claim A and soft claim C', async () => {
      mockDAO.findById.mockResolvedValue(storyRecordWithMixedClaims);
      mockDAO.updateDraft.mockImplementation(async (_id, payload) => ({
        ...storyRecordWithMixedClaims,
        draft_text: payload.draft_text,
        claims_used: payload.claims_used,
      }));

      const response = await DraftRequestHandler.handle('integration-record-001');

      // draft_text contains claim A (confirmed hard)
      expect(response.draft_text).toContain(
        'Increased quarterly revenue by 25% through strategic client outreach',
      );

      // draft_text does NOT contain claim B (denied hard)
      expect(response.draft_text).not.toContain(
        'Reduced operational costs by 40%',
      );

      // draft_text contains claim C (soft — always included)
      expect(response.draft_text).toContain(
        'Led cross-functional team of 12 engineers',
      );

      // draft_text does NOT contain claim D (hard without truth_check)
      expect(response.draft_text).not.toContain('99.9% uptime SLA');

      // claims_used includes only A and C
      expect(response.claims_used).toEqual(['claim-A', 'claim-C']);
    });

    it('should call updateDraft with the correct payload', async () => {
      mockDAO.findById.mockResolvedValue(storyRecordWithMixedClaims);
      mockDAO.updateDraft.mockImplementation(async (_id, payload) => ({
        ...storyRecordWithMixedClaims,
        draft_text: payload.draft_text,
        claims_used: payload.claims_used,
      }));

      await DraftRequestHandler.handle('integration-record-001');

      expect(mockDAO.updateDraft).toHaveBeenCalledTimes(1);
      const [id, payload] = mockDAO.updateDraft.mock.calls[0];
      expect(id).toBe('integration-record-001');
      expect(payload.claims_used).toEqual(['claim-A', 'claim-C']);
      expect(payload.draft_text).toContain('Increased quarterly revenue');
      expect(payload.draft_text).not.toContain('Reduced operational costs');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: All step boundaries validated
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Response matches schema', () => {
    it('should return a response that passes DraftResponseSchema', async () => {
      mockDAO.findById.mockResolvedValue(storyRecordWithMixedClaims);
      mockDAO.updateDraft.mockImplementation(async (_id, payload) => ({
        ...storyRecordWithMixedClaims,
        draft_text: payload.draft_text,
        claims_used: payload.claims_used,
      }));

      const response = await DraftRequestHandler.handle('integration-record-001');
      const parsed = DraftResponseSchema.safeParse(response);

      expect(parsed.success).toBe(true);
    });

    it('should have draft_text as string and claims_used as string[]', async () => {
      mockDAO.findById.mockResolvedValue(storyRecordWithMixedClaims);
      mockDAO.updateDraft.mockImplementation(async (_id, payload) => ({
        ...storyRecordWithMixedClaims,
        draft_text: payload.draft_text,
        claims_used: payload.claims_used,
      }));

      const response = await DraftRequestHandler.handle('integration-record-001');

      expect(typeof response.draft_text).toBe('string');
      expect(Array.isArray(response.claims_used)).toBe(true);
      response.claims_used.forEach((id) => {
        expect(typeof id).toBe('string');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: All error branches mapped
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Failures without partial records', () => {
    it('should throw STORY_NOT_FOUND when record does not exist', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await DraftRequestHandler.handle('nonexistent');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('STORY_NOT_FOUND');
        expect((e as DraftError).statusCode).toBe(404);
        // No DAO update should have been attempted
        expect(mockDAO.updateDraft).not.toHaveBeenCalled();
      }
    });

    it('should throw INVALID_STATE when record is not in DRAFT state', async () => {
      const approvedRecord: DraftStoryRecord = {
        ...storyRecordWithMixedClaims,
        status: 'APPROVED',
      };
      mockDAO.findById.mockResolvedValue(approvedRecord);

      try {
        await DraftRequestHandler.handle('integration-record-001');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('INVALID_STATE');
        expect(mockDAO.updateDraft).not.toHaveBeenCalled();
      }
    });

    it('should throw PERSISTENCE_FAILED when DAO update fails', async () => {
      mockDAO.findById.mockResolvedValue(storyRecordWithMixedClaims);
      mockDAO.updateDraft.mockRejectedValue(
        DraftDataAccessError.PERSISTENCE_FAILED('DB unavailable'),
      );

      try {
        await DraftRequestHandler.handle('integration-record-001');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('PERSISTENCE_FAILED');
        expect((e as DraftError).retryable).toBe(true);
      }
    });
  });
});
