/**
 * DraftRequestHandler.step6.test.ts - Step 6: Return updated draft to caller
 *
 * TLA+ Properties:
 * - Reachability: persisted StoryRecord → response with draft_text excluding unconfirmed hard claims
 * - TypeInvariant: response matches DraftResponseSchema
 * - ErrorConsistency: transform failure → RESPONSE_TRANSFORM_FAILED
 *
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftRequestHandler } from '../DraftRequestHandler';
import { DraftError } from '@/server/error_definitions/DraftErrors';
import { DraftResponseSchema } from '@/server/data_structures/DraftStoryRecord';
import type { DraftStoryRecord } from '@/server/data_structures/DraftStoryRecord';

// ---------------------------------------------------------------------------
// Mock dependencies at module boundary
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/StoryRecordDAO', () => ({
  StoryRecordDAO: {
    findById: vi.fn(),
    updateDraft: vi.fn(),
  },
}));

import { StoryRecordDAO } from '@/server/data_access_objects/StoryRecordDAO';
const mockDAO = vi.mocked(StoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const draftRecord: DraftStoryRecord = {
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
      id: 'claim-2',
      text: 'Cost reduced by 50%',
      type: 'hard',
      truth_check: { status: 'denied', source: 'audit' },
    },
    {
      id: 'claim-3',
      text: 'Team collaboration improved',
      type: 'soft',
    },
  ],
};

const persistedRecord: DraftStoryRecord = {
  id: 'record-001',
  status: 'DRAFT',
  truth_checks: draftRecord.truth_checks,
  draft_text: 'Revenue increased by 30%\n\nTeam collaboration improved',
  claims_used: ['claim-1', 'claim-3'],
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftRequestHandler.handle — Step 6: Return updated draft to caller', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return response with draft_text excluding unconfirmed hard claims', async () => {
      mockDAO.findById.mockResolvedValue(draftRecord);
      mockDAO.updateDraft.mockResolvedValue(persistedRecord);

      const response = await DraftRequestHandler.handle('record-001');

      expect(response).toBeDefined();
      expect(response.draft_text).toContain('Revenue increased by 30%');
      expect(response.draft_text).toContain('Team collaboration improved');
      expect(response.draft_text).not.toContain('Cost reduced by 50%');
      expect(response.claims_used).toContain('claim-1');
      expect(response.claims_used).toContain('claim-3');
      expect(response.claims_used).not.toContain('claim-2');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return response matching DraftResponseSchema', async () => {
      mockDAO.findById.mockResolvedValue(draftRecord);
      mockDAO.updateDraft.mockResolvedValue(persistedRecord);

      const response = await DraftRequestHandler.handle('record-001');
      const parsed = DraftResponseSchema.safeParse(response);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw RESPONSE_TRANSFORM_FAILED on transform failure', async () => {
      // Return a record that will produce a response that fails schema validation
      const badPersistedRecord = {
        ...persistedRecord,
        draft_text: undefined, // will cause schema validation failure
        claims_used: undefined,
      } as unknown as DraftStoryRecord;

      mockDAO.findById.mockResolvedValue(draftRecord);
      mockDAO.updateDraft.mockResolvedValue(badPersistedRecord);

      try {
        await DraftRequestHandler.handle('record-001');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('RESPONSE_TRANSFORM_FAILED');
      }
    });

    it('should propagate DraftError from process chain', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await DraftRequestHandler.handle('nonexistent');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('STORY_NOT_FOUND');
      }
    });
  });
});
