/**
 * VerificationDAO Wiring Tests
 *
 * TLA+ properties per method:
 * - Reachability: Supabase mock returns data → DAO returns mapped entity
 * - TypeInvariant: Returned entity conforms to expected shape
 * - ErrorConsistency: Supabase error → VerificationError
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';

const { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate,
        mockOrder, mockLimit, mockEq, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn();
  const mockInsert = vi.fn();
  const mockUpdate = vi.fn();
  const mockLimit = vi.fn(() => ({ single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockOrder = vi.fn(() => ({ limit: mockLimit, single: mockSingle }));
  const mockEq = vi.fn();
  const mockFrom = vi.fn();
  return { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate,
           mockOrder, mockLimit, mockEq, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { VerificationDAO } from '../VerificationDAO';

describe('VerificationDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockInsert.mockReturnValue({ select: mockSelect });
    mockUpdate.mockReturnValue({ eq: mockEq });
    mockEq.mockReturnValue({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle, order: mockOrder });
    mockOrder.mockReturnValue({ limit: mockLimit, single: mockSingle });
    mockLimit.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
      insert: mockInsert,
      update: mockUpdate,
    });
  });

  // --- getClaimantById ---
  describe('getClaimantById', () => {
    describe('Reachability', () => {
      it('returns Claimant when found', async () => {
        const row = { id: 'cl-1', key_claims: [], phone: '+1234', sms_opt_in: true };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await VerificationDAO.getClaimantById('cl-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('cl-1');
        expect(mockFrom).toHaveBeenCalledWith('claimants');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await VerificationDAO.getClaimantById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(VerificationDAO.getClaimantById('x')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- createVerificationAttempt ---
  describe('createVerificationAttempt', () => {
    describe('Reachability', () => {
      it('returns VerificationAttempt', async () => {
        const row = { id: 'va-1', claimant_id: 'cl-1', status: 'FAILED', reason: 'no contact', created_at: '2026-01-01', updated_at: '2026-01-01' };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await VerificationDAO.createVerificationAttempt('cl-1', 'FAILED', 'no contact');
        expect(result.id).toBe('va-1');
        expect(mockFrom).toHaveBeenCalledWith('verification_attempts');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(VerificationDAO.createVerificationAttempt('cl-1', 'FAILED', 'reason')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- getLatestVerificationAttempt ---
  describe('getLatestVerificationAttempt', () => {
    describe('Reachability', () => {
      it('returns latest VerificationAttempt when found', async () => {
        const row = { id: 'va-1', claimant_id: 'cl-1', status: 'FAILED', reason: 'no contact', created_at: '2026-01-01', updated_at: '2026-01-01' };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await VerificationDAO.getLatestVerificationAttempt('cl-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('verification_attempts');
      });
      it('returns null when none found', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { code: 'PGRST116', message: 'no rows' } });
        // When using .single() and no rows found, Supabase returns error PGRST116
        // The DAO should handle this gracefully
        const result = await VerificationDAO.getLatestVerificationAttempt('cl-1');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'connection refused', code: 'PGRST000' } });
        await expect(VerificationDAO.getLatestVerificationAttempt('x')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- updateDraftingStatus ---
  describe('updateDraftingStatus', () => {
    describe('Reachability', () => {
      it('updates without error', async () => {
        mockEq.mockResolvedValueOnce({ error: null });
        await expect(VerificationDAO.updateDraftingStatus('va-1', 'BLOCKED')).resolves.toBeUndefined();
        expect(mockFrom).toHaveBeenCalledWith('verification_attempts');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on failure', async () => {
        mockEq.mockResolvedValueOnce({ error: { message: 'fail' } });
        await expect(VerificationDAO.updateDraftingStatus('va-1', 'BLOCKED')).rejects.toThrow(VerificationError);
      });
    });
  });
});
