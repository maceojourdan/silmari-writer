/**
 * StoryRecordDAO Wiring Tests
 *
 * TLA+ properties per method:
 * - Reachability: Supabase mock returns data → DAO returns mapped entity
 * - TypeInvariant: Returned entity conforms to DraftStoryRecordSchema
 * - ErrorConsistency: Supabase error → PersistenceError
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftStoryRecordSchema } from '@/server/data_structures/DraftStoryRecord';
import { PersistenceError } from '@/server/error_definitions/PersistenceErrors';

const { mockSingle, mockMaybeSingle, mockSelect, mockUpdate, mockEq, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn(() => ({ single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockUpdate = vi.fn(() => ({ eq: vi.fn(() => ({ select: mockSelect })) }));
  const mockEq = vi.fn(() => ({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockFrom = vi.fn(() => ({
    select: vi.fn(() => ({ eq: mockEq })),
    update: mockUpdate,
  }));
  return { mockSingle, mockMaybeSingle, mockSelect, mockUpdate, mockEq, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { StoryRecordDAO } from '../StoryRecordDAO';

describe('StoryRecordDAO — Supabase Wiring', () => {
  beforeEach(() => vi.clearAllMocks());

  // --- findById ---
  describe('findById', () => {
    describe('Reachability', () => {
      it('returns DraftStoryRecord when found', async () => {
        const row = { id: 'sr-1', status: 'DRAFT', truth_checks: [], draft_text: 'text', claims_used: ['c1'] };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryRecordDAO.findById('sr-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('sr-1');
        expect(mockFrom).toHaveBeenCalledWith('story_records');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await StoryRecordDAO.findById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to DraftStoryRecordSchema', async () => {
        const row = { id: 'sr-1', status: 'DRAFT', truth_checks: [], draft_text: 'text', claims_used: ['c1'] };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryRecordDAO.findById('sr-1');
        expect(DraftStoryRecordSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws PersistenceError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryRecordDAO.findById('x')).rejects.toThrow(PersistenceError);
      });
    });
  });

  // --- updateDraft ---
  describe('updateDraft', () => {
    describe('Reachability', () => {
      it('returns updated DraftStoryRecord', async () => {
        const row = { id: 'sr-1', status: 'DRAFT', truth_checks: [], draft_text: 'new text', claims_used: ['c1', 'c2'] };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryRecordDAO.updateDraft('sr-1', { draft_text: 'new text', claims_used: ['c1', 'c2'] });
        expect(result.draft_text).toBe('new text');
        expect(mockFrom).toHaveBeenCalledWith('story_records');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to DraftStoryRecordSchema', async () => {
        const row = { id: 'sr-1', status: 'DRAFT', truth_checks: [], draft_text: 'new text', claims_used: ['c1'] };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryRecordDAO.updateDraft('sr-1', { draft_text: 'new text', claims_used: ['c1'] });
        expect(DraftStoryRecordSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws PersistenceError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryRecordDAO.updateDraft('x', { draft_text: 'text', claims_used: [] })).rejects.toThrow(PersistenceError);
      });
    });
  });
});
