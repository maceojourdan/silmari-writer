/**
 * ConfirmStoryDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ConfirmStoryError } from '@/server/error_definitions/ConfirmStoryErrors';

const { mockSingle, mockMaybeSingle, mockSelect, mockEq, mockFrom, mockRpc } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn();
  const mockEq = vi.fn();
  const mockFrom = vi.fn();
  const mockRpc = vi.fn();
  return { mockSingle, mockMaybeSingle, mockSelect, mockEq, mockFrom, mockRpc };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom, rpc: mockRpc } }));

import { ConfirmStoryDAO } from '../ConfirmStoryDAO';

describe('ConfirmStoryDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockEq.mockReturnValue({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
    });
  });

  // --- findQuestionById ---
  describe('findQuestionById', () => {
    describe('Reachability', () => {
      it('returns Question when found', async () => {
        const row = { id: 'q-1', text: 'Tell me about...', status: 'ACTIVE' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ConfirmStoryDAO.findQuestionById('q-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('questions');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await ConfirmStoryDAO.findQuestionById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws ConfirmStoryError on failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ConfirmStoryDAO.findQuestionById('x')).rejects.toThrow(ConfirmStoryError);
      });
    });
  });

  // --- findJobRequirementsByQuestionId ---
  describe('findJobRequirementsByQuestionId', () => {
    describe('Reachability', () => {
      it('returns JobRequirement array', async () => {
        const rows = [{ id: 'jr-1', question_id: 'q-1', requirement: 'Node.js' }];
        mockEq.mockResolvedValueOnce({ data: rows, error: null });
        const result = await ConfirmStoryDAO.findJobRequirementsByQuestionId('q-1');
        expect(result).toHaveLength(1);
        expect(mockFrom).toHaveBeenCalledWith('job_requirements');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws ConfirmStoryError on failure', async () => {
        mockEq.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ConfirmStoryDAO.findJobRequirementsByQuestionId('x')).rejects.toThrow(ConfirmStoryError);
      });
    });
  });

  // --- findStoriesByQuestionId ---
  describe('findStoriesByQuestionId', () => {
    describe('Reachability', () => {
      it('returns Story array', async () => {
        const rows = [{ id: 'st-1', question_id: 'q-1', title: 'My Story', status: 'PENDING' }];
        mockEq.mockResolvedValueOnce({ data: rows, error: null });
        const result = await ConfirmStoryDAO.findStoriesByQuestionId('q-1');
        expect(result).toHaveLength(1);
        expect(mockFrom).toHaveBeenCalledWith('stories');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws ConfirmStoryError on failure', async () => {
        mockEq.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ConfirmStoryDAO.findStoriesByQuestionId('x')).rejects.toThrow(ConfirmStoryError);
      });
    });
  });

  // --- findStoryById ---
  describe('findStoryById', () => {
    describe('Reachability', () => {
      it('returns Story when found', async () => {
        const row = { id: 'st-1', title: 'My Story', status: 'PENDING' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ConfirmStoryDAO.findStoryById('st-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('stories');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws ConfirmStoryError on failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ConfirmStoryDAO.findStoryById('x')).rejects.toThrow(ConfirmStoryError);
      });
    });
  });

  // --- updateStatusesTransactional ---
  describe('updateStatusesTransactional', () => {
    describe('Reachability', () => {
      it('calls RPC and returns result', async () => {
        mockRpc.mockResolvedValue({ data: { confirmed_story_id: 'st-1', excluded_count: 3 }, error: null });
        const result = await ConfirmStoryDAO.updateStatusesTransactional('q-1', 'st-1');
        expect(result.confirmedStoryId).toBe('st-1');
        expect(result.excludedCount).toBe(3);
        expect(mockRpc).toHaveBeenCalledWith('confirm_story', { p_question_id: 'q-1', p_story_id: 'st-1' });
      });
    });
    describe('ErrorConsistency', () => {
      it('throws ConfirmStoryError on RPC failure', async () => {
        mockRpc.mockResolvedValue({ data: null, error: { message: 'rpc fail' } });
        await expect(ConfirmStoryDAO.updateStatusesTransactional('q-1', 'st-1')).rejects.toThrow(ConfirmStoryError);
      });
    });
  });
});
