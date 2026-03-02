/**
 * UserDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SharedError } from '@/server/error_definitions/SharedErrors';

const { mockMaybeSingle, mockEq, mockFrom } = vi.hoisted(() => {
  const mockMaybeSingle = vi.fn();
  const mockEq = vi.fn();
  const mockFrom = vi.fn();
  return { mockMaybeSingle, mockEq, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { UserDAO } from '../UserDAO';

const baseRow = {
  id: 'u-1', sms_opt_in: true, phone_number: '+1234567890',
  created_at: '2026-01-01', updated_at: '2026-01-01',
};

describe('UserDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockEq.mockReturnValue({ maybeSingle: mockMaybeSingle });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
    });
  });

  // --- findById ---
  describe('findById', () => {
    describe('Reachability', () => {
      it('returns User when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await UserDAO.findById('u-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('u-1');
        expect(mockFrom).toHaveBeenCalledWith('users');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await UserDAO.findById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws SharedError on failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(UserDAO.findById('x')).rejects.toThrow(SharedError);
      });
    });
  });
});
