/**
 * SessionStoryRecordDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeSessionError } from '@/server/error_definitions/FinalizeSessionErrors';

const { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate, mockUpsert, mockEq, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn();
  const mockInsert = vi.fn();
  const mockUpdate = vi.fn();
  const mockUpsert = vi.fn();
  const mockEq = vi.fn();
  const mockFrom = vi.fn();
  return { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate, mockUpsert, mockEq, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { SessionStoryRecordDAO } from '../SessionStoryRecordDAO';

const sessionRow = {
  id: 'sess-1', state: 'ACTIVE', required_inputs_complete: true,
  responses: ['r1', 'r2'], created_at: '2026-01-01', updated_at: '2026-01-01',
};

const storyRecordRow = {
  id: 'sr-1', session_id: 'sess-1', responses: ['r1', 'r2'],
  status: 'FINALIZED', created_at: '2026-01-01', updated_at: '2026-01-01',
};

describe('SessionStoryRecordDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockInsert.mockReturnValue({ select: mockSelect });
    mockUpdate.mockReturnValue({ eq: mockEq });
    mockUpsert.mockReturnValue({ select: mockSelect });
    mockEq.mockReturnValue({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
      insert: mockInsert,
      update: mockUpdate,
      upsert: mockUpsert,
    });
  });

  // --- findSessionById ---
  describe('findSessionById', () => {
    describe('Reachability', () => {
      it('returns SessionForFinalization when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: sessionRow, error: null });
        const result = await SessionStoryRecordDAO.findSessionById('sess-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('sess-1');
        expect(mockFrom).toHaveBeenCalledWith('sessions');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await SessionStoryRecordDAO.findSessionById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws FinalizeSessionError on failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(SessionStoryRecordDAO.findSessionById('x')).rejects.toThrow(FinalizeSessionError);
      });
    });
  });

  // --- updateSessionState ---
  describe('updateSessionState', () => {
    describe('Reachability', () => {
      it('returns updated Session', async () => {
        mockSingle.mockResolvedValue({ data: { ...sessionRow, state: 'FINALIZE' }, error: null });
        const result = await SessionStoryRecordDAO.updateSessionState('sess-1', 'FINALIZE');
        expect(result.state).toBe('FINALIZE');
        expect(mockFrom).toHaveBeenCalledWith('sessions');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws FinalizeSessionError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(SessionStoryRecordDAO.updateSessionState('sess-1', 'FINALIZE')).rejects.toThrow(FinalizeSessionError);
      });
    });
  });

  // --- upsertStoryRecord ---
  describe('upsertStoryRecord', () => {
    describe('Reachability', () => {
      it('returns StoryRecord', async () => {
        mockSingle.mockResolvedValue({ data: storyRecordRow, error: null });
        const result = await SessionStoryRecordDAO.upsertStoryRecord('sess-1', ['r1', 'r2'], 'FINALIZED');
        expect(result.id).toBe('sr-1');
        expect(mockFrom).toHaveBeenCalledWith('story_records');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws FinalizeSessionError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(SessionStoryRecordDAO.upsertStoryRecord('sess-1', ['r1'], 'FINALIZED')).rejects.toThrow(FinalizeSessionError);
      });
    });
  });
});
