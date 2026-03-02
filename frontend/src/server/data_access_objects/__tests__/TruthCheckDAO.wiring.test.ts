/**
 * TruthCheckDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { TruthCheckError } from '@/server/error_definitions/TruthCheckErrors';

const { mockSingle, mockSelect, mockInsert, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockSelect = vi.fn();
  const mockInsert = vi.fn();
  const mockFrom = vi.fn();
  return { mockSingle, mockSelect, mockInsert, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { TruthCheckDAO } from '../TruthCheckDAO';

const baseRow = {
  id: 'tc-1', claim_id: 'cl-1', status: 'confirmed',
  source: 'voice', created_at: '2026-01-01',
};

describe('TruthCheckDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle });
    mockInsert.mockReturnValue({ select: mockSelect });
    mockFrom.mockReturnValue({ insert: mockInsert });
  });

  // --- create ---
  describe('create', () => {
    describe('Reachability', () => {
      it('returns TruthCheck with generated ID', async () => {
        mockSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await TruthCheckDAO.create({ claim_id: 'cl-1', status: 'confirmed', source: 'voice' });
        expect(result.id).toBe('tc-1');
        expect(mockFrom).toHaveBeenCalledWith('truth_checks');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws TruthCheckError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(TruthCheckDAO.create({ claim_id: 'cl-1', status: 'confirmed', source: 'voice' })).rejects.toThrow(TruthCheckError);
      });
    });
  });
});
