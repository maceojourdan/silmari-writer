/**
 * BehavioralQuestionDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { BehavioralQuestionError } from '@/server/error_definitions/BehavioralQuestionErrors';

const { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate, mockEq, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn();
  const mockInsert = vi.fn();
  const mockUpdate = vi.fn();
  const mockEq = vi.fn();
  const mockFrom = vi.fn();
  return { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate, mockEq, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { BehavioralQuestionDAO } from '../BehavioralQuestionDAO';

const baseRow = {
  id: 'bq-1',
  session_id: 's-1',
  objective: 'Lead migration',
  actions: ['a1', 'a2', 'a3'],
  obstacles: ['o1'],
  outcome: 'Delivered',
  role_clarity: 'Tech lead',
  status: 'DRAFT',
  created_at: '2026-01-01',
  updated_at: '2026-01-01',
};

describe('BehavioralQuestionDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockInsert.mockReturnValue({ select: mockSelect });
    mockUpdate.mockReturnValue({ eq: vi.fn(() => ({ select: mockSelect })) });
    mockEq.mockReturnValue({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
      insert: mockInsert,
      update: mockUpdate,
    });
  });

  // --- updateStatus ---
  describe('updateStatus', () => {
    describe('Reachability', () => {
      it('returns updated BehavioralQuestion', async () => {
        mockSingle.mockResolvedValue({ data: { ...baseRow, status: 'VERIFY' }, error: null });
        const result = await BehavioralQuestionDAO.updateStatus('bq-1', 'VERIFY');
        expect(result.status).toBe('VERIFY');
        expect(mockFrom).toHaveBeenCalledWith('behavioral_questions');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BehavioralQuestionError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(BehavioralQuestionDAO.updateStatus('bq-1', 'VERIFY')).rejects.toThrow(BehavioralQuestionError);
      });
    });
  });

  // --- insert ---
  describe('insert', () => {
    describe('Reachability', () => {
      it('returns BehavioralQuestion with generated ID', async () => {
        mockSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await BehavioralQuestionDAO.insert({
          sessionId: 's-1',
          objective: 'Lead migration',
          actions: ['a1', 'a2', 'a3'],
          obstacles: ['o1'],
          outcome: 'Delivered',
          roleClarity: 'Tech lead',
          status: 'DRAFT',
        });
        expect(result.id).toBe('bq-1');
        expect(mockFrom).toHaveBeenCalledWith('behavioral_questions');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BehavioralQuestionError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(BehavioralQuestionDAO.insert({
          sessionId: 's-1',
          objective: 'Lead migration',
          actions: ['a1', 'a2', 'a3'],
          obstacles: ['o1'],
          outcome: 'Delivered',
          roleClarity: 'Tech lead',
          status: 'DRAFT',
        })).rejects.toThrow(BehavioralQuestionError);
      });
    });
  });

  // --- findById ---
  describe('findById', () => {
    describe('Reachability', () => {
      it('returns BehavioralQuestion when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await BehavioralQuestionDAO.findById('bq-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('bq-1');
        expect(mockFrom).toHaveBeenCalledWith('behavioral_questions');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await BehavioralQuestionDAO.findById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BehavioralQuestionError on failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(BehavioralQuestionDAO.findById('x')).rejects.toThrow(BehavioralQuestionError);
      });
    });
  });
});
