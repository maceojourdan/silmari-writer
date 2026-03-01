/**
 * DraftProcessChain.step1.test.ts - Step 1: Trigger DRAFT execution
 *
 * TLA+ Properties:
 * - Reachability: DRAFT state StoryRecord → execution context
 * - TypeInvariant: context matches DraftExecutionContext
 * - ErrorConsistency: missing/invalid state → typed DraftError
 *
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftProcessChain } from '../DraftProcessChain';
import { DraftError } from '@/server/error_definitions/DraftErrors';
import type { DraftStoryRecord } from '@/server/data_structures/DraftStoryRecord';

// ---------------------------------------------------------------------------
// Mock StoryRecordDAO at the module boundary
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

const validDraftRecord: DraftStoryRecord = {
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
      text: 'Team collaboration improved',
      type: 'soft',
    },
  ],
};

const approvedRecord: DraftStoryRecord = {
  id: 'record-002',
  status: 'APPROVED',
  truth_checks: [],
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftProcessChain.execute — Step 1: Trigger DRAFT execution', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return execution context for a StoryRecord in DRAFT state', async () => {
      mockDAO.findById.mockResolvedValue(validDraftRecord);

      const context = await DraftProcessChain.execute('record-001');

      expect(context).toBeDefined();
      expect(context.storyRecordId).toBe('record-001');
      expect(context.storyRecord).toBeDefined();
      expect(context.storyRecord.truth_checks).toBeDefined();
      expect(mockDAO.findById).toHaveBeenCalledWith('record-001');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object matching DraftExecutionContext shape', async () => {
      mockDAO.findById.mockResolvedValue(validDraftRecord);

      const context = await DraftProcessChain.execute('record-001');

      expect(context).toHaveProperty('storyRecordId');
      expect(context).toHaveProperty('storyRecord');
      expect(typeof context.storyRecordId).toBe('string');
      expect(Array.isArray(context.storyRecord.truth_checks)).toBe(true);
    });

    it('should contain truth_checks as a defined array', async () => {
      mockDAO.findById.mockResolvedValue(validDraftRecord);

      const context = await DraftProcessChain.execute('record-001');

      expect(context.storyRecord.truth_checks).toBeDefined();
      expect(context.storyRecord.truth_checks.length).toBe(2);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw STORY_NOT_FOUND when no StoryRecord exists', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await DraftProcessChain.execute('nonexistent-id');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('STORY_NOT_FOUND');
        expect((e as DraftError).statusCode).toBe(404);
      }
    });

    it('should throw INVALID_STATE when StoryRecord is not in DRAFT state', async () => {
      mockDAO.findById.mockResolvedValue(approvedRecord);

      try {
        await DraftProcessChain.execute('record-002');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('INVALID_STATE');
        expect((e as DraftError).statusCode).toBe(422);
      }
    });
  });
});
