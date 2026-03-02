/**
 * SessionStoryRecordDAO Wiring Tests
 *
 * TLA+ properties per method:
 * - Reachability: Supabase mock returns data -> DAO returns mapped entity
 * - TypeInvariant: Returned entity has expected shape
 * - ErrorConsistency: Supabase error -> domain error with expected code
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { FinalizeSessionError } from '@/server/error_definitions/FinalizeSessionErrors';

const UUID1 = '00000000-0000-4000-8000-000000000001';

const { mockSingle, mockMaybeSingle, mockSelect, mockUpdate, mockUpsert, mockEq, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn(() => ({ single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockUpdate = vi.fn(() => ({ eq: vi.fn(() => ({ select: mockSelect })) }));
  const mockUpsert = vi.fn(() => ({ select: mockSelect }));
  const mockEq = vi.fn(() => ({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockFrom = vi.fn(() => ({
    select: vi.fn(() => ({ eq: mockEq })),
    update: mockUpdate,
    upsert: mockUpsert,
  }));
  return { mockSingle, mockMaybeSingle, mockSelect, mockUpdate, mockUpsert, mockEq, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { SessionStoryRecordDAO } from '../SessionStoryRecordDAO';

describe('SessionStoryRecordDAO — Supabase Wiring', () => {
  beforeEach(() => vi.clearAllMocks());

  // --- findSessionById ---
  describe('findSessionById', () => {
    describe('Reachability', () => {
      it('returns session when found', async () => {
        const row = {
          id: UUID1, state: 'ACTIVE', required_inputs_complete: true,
          responses: ['r1'], created_at: '2026-01-01', updated_at: '2026-01-01',
        };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await SessionStoryRecordDAO.findSessionById(UUID1);
        expect(result).not.toBeNull();
        expect(result!.id).toBe(UUID1);
        expect(result!.requiredInputsComplete).toBe(true);
        expect(mockFrom).toHaveBeenCalledWith('sessions');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await SessionStoryRecordDAO.findSessionById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('returned object has SessionForFinalization shape', async () => {
        const row = {
          id: UUID1, state: 'ACTIVE', required_inputs_complete: true,
          responses: ['r1'], created_at: '2026-01-01', updated_at: '2026-01-01',
        };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await SessionStoryRecordDAO.findSessionById(UUID1);
        expect(result).toHaveProperty('id');
        expect(result).toHaveProperty('state');
        expect(result).toHaveProperty('requiredInputsComplete');
        expect(result).toHaveProperty('responses');
        expect(result).toHaveProperty('createdAt');
        expect(result).toHaveProperty('updatedAt');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws FinalizeSessionError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(SessionStoryRecordDAO.findSessionById('x')).rejects.toThrow(FinalizeSessionError);
      });
    });
  });

  // --- updateSessionState ---
  describe('updateSessionState', () => {
    describe('Reachability', () => {
      it('updates and returns session with new state', async () => {
        const row = {
          id: UUID1, state: 'FINALIZE', required_inputs_complete: true,
          created_at: '2026-01-01', updated_at: '2026-01-02',
        };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await SessionStoryRecordDAO.updateSessionState(UUID1, 'FINALIZE');
        expect(result.state).toBe('FINALIZE');
      });
    });
    describe('TypeInvariant', () => {
      it('returned object has Session shape', async () => {
        const row = {
          id: UUID1, state: 'FINALIZE', required_inputs_complete: true,
          created_at: '2026-01-01', updated_at: '2026-01-02',
        };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await SessionStoryRecordDAO.updateSessionState(UUID1, 'FINALIZE');
        expect(result).toHaveProperty('id');
        expect(result).toHaveProperty('state');
        expect(result).toHaveProperty('createdAt');
        expect(result).toHaveProperty('updatedAt');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws FinalizeSessionError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(SessionStoryRecordDAO.updateSessionState('x', 'FINALIZE')).rejects.toThrow(FinalizeSessionError);
      });
    });
  });

  // --- upsertStoryRecord ---
  describe('upsertStoryRecord', () => {
    describe('Reachability', () => {
      it('upserts and returns story record', async () => {
        const row = {
          id: 'sr-1', session_id: UUID1, responses: ['r1'],
          status: 'FINALIZED', created_at: '2026-01-01', updated_at: '2026-01-02',
        };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await SessionStoryRecordDAO.upsertStoryRecord(UUID1, ['r1'], 'FINALIZED');
        expect(result).toHaveProperty('id');
        expect(mockFrom).toHaveBeenCalledWith('story_records');
      });
    });
    describe('TypeInvariant', () => {
      it('returned object is a StoryRecord', async () => {
        const row = {
          id: 'sr-1', session_id: UUID1, responses: ['r1'],
          status: 'FINALIZED', created_at: '2026-01-01', updated_at: '2026-01-02',
        };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await SessionStoryRecordDAO.upsertStoryRecord(UUID1, ['r1'], 'FINALIZED');
        expect(result.status).toBe('FINALIZED');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws FinalizeSessionError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(
          SessionStoryRecordDAO.upsertStoryRecord('x', ['r1'], 'FINALIZED'),
        ).rejects.toThrow(FinalizeSessionError);
      });
    });
  });
});
