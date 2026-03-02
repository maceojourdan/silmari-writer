import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '@/server/error_definitions/SessionErrors';

const { mockSingle, mockSelect, mockInsert, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockSelect = vi.fn(() => ({ single: mockSingle }));
  const mockInsert = vi.fn(() => ({ select: mockSelect }));
  const mockFrom = vi.fn(() => ({ insert: mockInsert }));
  return { mockSingle, mockSelect, mockInsert, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { SessionInitDAO } from '../SessionInitDAO';

describe('SessionInitDAO — Supabase Wiring', () => {
  beforeEach(() => vi.clearAllMocks());

  describe('insertResume', () => {
    it('Reachability: returns generated UUID', async () => {
      mockSingle.mockResolvedValue({ data: { id: 'r-1' }, error: null });
      const id = await SessionInitDAO.insertResume({ content: 'test', name: 'test', wordCount: 5 });
      expect(id).toBe('r-1');
      expect(mockFrom).toHaveBeenCalledWith('resumes');
    });
    it('ErrorConsistency: throws SessionError on failure', async () => {
      mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
      await expect(SessionInitDAO.insertResume({ content: 'test', name: 'test', wordCount: 5 })).rejects.toThrow(SessionError);
    });
  });

  describe('insertJob', () => {
    it('Reachability: returns generated UUID', async () => {
      mockSingle.mockResolvedValue({ data: { id: 'j-1' }, error: null });
      const id = await SessionInitDAO.insertJob({ title: 'SE', description: 'desc', sourceType: 'text', sourceValue: 'val' });
      expect(id).toBe('j-1');
      expect(mockFrom).toHaveBeenCalledWith('jobs');
    });
    it('ErrorConsistency: throws SessionError on failure', async () => {
      mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
      await expect(SessionInitDAO.insertJob({ title: 'SE', description: 'desc', sourceType: 'text', sourceValue: 'val' })).rejects.toThrow(SessionError);
    });
  });

  describe('insertQuestion', () => {
    it('Reachability: returns generated UUID', async () => {
      mockSingle.mockResolvedValue({ data: { id: 'q-1' }, error: null });
      const id = await SessionInitDAO.insertQuestion({ text: 'Tell me...' });
      expect(id).toBe('q-1');
      expect(mockFrom).toHaveBeenCalledWith('questions');
    });
    it('ErrorConsistency: throws SessionError on failure', async () => {
      mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
      await expect(SessionInitDAO.insertQuestion({ text: 'Tell me...' })).rejects.toThrow(SessionError);
    });
  });

  describe('insertSession', () => {
    it('Reachability: returns generated UUID', async () => {
      mockSingle.mockResolvedValue({ data: { id: 's-1' }, error: null });
      const id = await SessionInitDAO.insertSession({ resumeId: 'r-1', jobId: 'j-1', questionId: 'q-1', status: 'INITIALIZED' });
      expect(id).toBe('s-1');
      expect(mockFrom).toHaveBeenCalledWith('sessions');
    });
    it('ErrorConsistency: throws SessionError on failure', async () => {
      mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
      await expect(SessionInitDAO.insertSession({ resumeId: 'r-1', jobId: 'j-1', questionId: 'q-1', status: 'INITIALIZED' })).rejects.toThrow(SessionError);
    });
  });
});
