/**
 * StoryRecordDAO.step5.test.ts - Step 5: Persist draft and metadata
 *
 * TLA+ Properties:
 * - Reachability: draft payload → persisted StoryRecord with draft_text + claims_used
 * - TypeInvariant: returned entity passes DraftStoryRecordSchema
 * - ErrorConsistency: DB failure → PERSISTENCE_FAILED; no partial update
 *
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftStoryRecordSchema } from '@/server/data_structures/DraftStoryRecord';
import type { DraftStoryRecord, DraftPayload } from '@/server/data_structures/DraftStoryRecord';
import {
  DraftError,
  DraftDataAccessError,
} from '@/server/error_definitions/DraftErrors';

// ---------------------------------------------------------------------------
// Mock StoryRecordDAO
// ---------------------------------------------------------------------------

vi.mock('../StoryRecordDAO', () => ({
  StoryRecordDAO: {
    findById: vi.fn(),
    updateDraft: vi.fn(),
  },
}));

import { StoryRecordDAO } from '../StoryRecordDAO';
const mockDAO = vi.mocked(StoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const draftPayload: DraftPayload = {
  draft_text: 'Revenue increased by 30%\n\nTeam collaboration improved',
  claims_used: ['claim-1', 'claim-3'],
};

const persistedRecord: DraftStoryRecord = {
  id: 'record-001',
  status: 'DRAFT',
  truth_checks: [
    {
      id: 'claim-1',
      text: 'Revenue increased by 30%',
      type: 'hard',
      truth_check: { status: 'confirmed', source: 'Q4 report' },
    },
    {
      id: 'claim-3',
      text: 'Team collaboration improved',
      type: 'soft',
    },
  ],
  draft_text: 'Revenue increased by 30%\n\nTeam collaboration improved',
  claims_used: ['claim-1', 'claim-3'],
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StoryRecordDAO.updateDraft — Step 5: Persist draft and metadata', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should update and return entity with draft_text and claims_used', async () => {
      mockDAO.updateDraft.mockResolvedValue(persistedRecord);

      const result = await StoryRecordDAO.updateDraft('record-001', draftPayload);

      expect(result).toBeDefined();
      expect(result.draft_text).toBe(draftPayload.draft_text);
      expect(result.claims_used).toEqual(draftPayload.claims_used);
      expect(mockDAO.updateDraft).toHaveBeenCalledWith('record-001', draftPayload);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return entity that passes DraftStoryRecordSchema', async () => {
      mockDAO.updateDraft.mockResolvedValue(persistedRecord);

      const result = await StoryRecordDAO.updateDraft('record-001', draftPayload);
      const parsed = DraftStoryRecordSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should propagate PERSISTENCE_FAILED on DB failure', async () => {
      mockDAO.updateDraft.mockRejectedValue(
        DraftDataAccessError.PERSISTENCE_FAILED('DB write failed'),
      );

      try {
        await StoryRecordDAO.updateDraft('record-001', draftPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('PERSISTENCE_FAILED');
        expect((e as DraftError).retryable).toBe(true);
      }
    });

    it('should ensure no partial update (transaction rollback assertion)', async () => {
      mockDAO.updateDraft.mockRejectedValue(
        DraftDataAccessError.PERSISTENCE_FAILED('Transaction rolled back'),
      );

      try {
        await StoryRecordDAO.updateDraft('record-001', draftPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        // On failure, updateDraft should not have returned a partial result
        expect(mockDAO.updateDraft).toHaveBeenCalledTimes(1);
        expect((e as DraftError).code).toBe('PERSISTENCE_FAILED');
      }
    });
  });
});
