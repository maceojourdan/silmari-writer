// @ts-nocheck
/**
 * ClaimDAO Wiring Tests
 *
 * TLA+ properties per method:
 * - Reachability: Supabase mock returns data → DAO returns mapped entity
 * - TypeInvariant: Returned entity conforms to Zod schema
 * - ErrorConsistency: Supabase error → DomainError with PERSISTENCE_ERROR code
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimSchema, CaseClaimSchema, StoryRecordClaimSchema, ConfirmedClaimSchema } from '@/server/data_structures/Claim';
import { ClaimRecordSchema } from '@/server/data_structures/ClaimRecord';
import { DomainError } from '@/server/error_definitions/DomainErrors';

const { mockSingle, mockMaybeSingle, mockSelect, mockUpdate, mockEq, mockFrom, mockOrder, mockLimit, mockIn } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn(() => ({ single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockOrder = vi.fn();
  const mockLimit = vi.fn(() => ({ single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockIn = vi.fn(() => ({ select: mockSelect }));
  const mockEq = vi.fn(() => ({
    select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle,
    eq: mockEq, order: mockOrder, limit: mockLimit,
  }));
  mockOrder.mockReturnValue({ limit: mockLimit, order: mockOrder });
  const mockUpdate = vi.fn(() => ({
    eq: vi.fn(() => ({ select: mockSelect })),
    in: mockIn,
  }));
  const mockFrom = vi.fn(() => ({
    select: vi.fn(() => ({ eq: mockEq })),
    update: mockUpdate,
  }));
  return { mockSingle, mockMaybeSingle, mockSelect, mockUpdate, mockEq, mockFrom, mockOrder, mockLimit, mockIn };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { ClaimDAO } from '../ClaimDAO';

describe('ClaimDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.resetAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockLimit.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockIn.mockReturnValue({ select: mockSelect });
    mockEq.mockReturnValue({
      select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle,
      eq: mockEq, order: mockOrder, limit: mockLimit,
    });
    mockOrder.mockReturnValue({ limit: mockLimit, order: mockOrder });
    mockUpdate.mockReturnValue({
      eq: vi.fn(() => ({ select: mockSelect })),
      in: mockIn,
    });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
      update: mockUpdate,
    });
  });

  // --- findById ---
  describe('findById', () => {
    const row = { id: 'c-1', content: 'Led team', status: 'UNCERTAIN', sms_opt_in: true, phone_number: '+1555', truth_checks: [], created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns claim when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimDAO.findById('c-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('c-1');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await ClaimDAO.findById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ClaimSchema', async () => {
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimDAO.findById('c-1');
        expect(ClaimSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.findById('x')).rejects.toThrow(DomainError);
      });
    });
  });

  // --- findByPhoneNumber ---
  describe('findByPhoneNumber', () => {
    const row = { id: 'c-2', content: 'Revenue up', status: 'UNCERTAIN', sms_opt_in: true, phone_number: '+15551234567', truth_checks: [], created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns claim when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimDAO.findByPhoneNumber('+15551234567');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await ClaimDAO.findByPhoneNumber('+10000000000');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.findByPhoneNumber('x')).rejects.toThrow(DomainError);
      });
    });
  });

  // --- updateTruthCheck ---
  describe('updateTruthCheck', () => {
    const updatedRow = {
      id: 'c-1',
      content: 'Led team',
      status: 'CONFIRMED',
      sms_opt_in: false,
      phone_number: null,
      truth_checks: [{ id: 'tc-1', verdict: 'confirmed', source: 'sms', created_at: '2026-01-02' }],
      created_at: '2026-01-01',
      updated_at: '2026-01-02',
    };

    describe('Reachability', () => {
      it('reads claim then updates with appended truth check', async () => {
        mockSingle.mockResolvedValueOnce({ data: updatedRow, error: null });
        const result = await ClaimDAO.updateTruthCheck('c-1', 'confirmed', 'sms');
        expect(result.status).toBe('CONFIRMED');
        expect(result.truth_checks).toHaveLength(1);
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ClaimSchema', async () => {
        mockSingle.mockResolvedValueOnce({ data: updatedRow, error: null });
        const result = await ClaimDAO.updateTruthCheck('c-1', 'confirmed', 'sms');
        expect(ClaimSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError when update fails', async () => {
        mockSingle.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.updateTruthCheck('x', 'confirmed', 'sms')).rejects.toThrow(DomainError);
      });
    });
  });

  // --- getUnverifiedClaimsBySession ---
  describe('getUnverifiedClaimsBySession', () => {
    const recordRow = { id: 'cr-1', session_id: 's-1', category: 'metrics', status: 'unverified', content: 'Revenue', contact_phone: null, contact_method: null, verified_at: null, disputed_at: null, created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns unverified claims ordered by category', async () => {
        mockOrder.mockResolvedValueOnce({ data: [recordRow], error: null });
        const result = await ClaimDAO.getUnverifiedClaimsBySession('s-1');
        expect(result).toHaveLength(1);
        expect(result[0].sessionId).toBe('s-1');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns empty array when none found', async () => {
        mockOrder.mockResolvedValueOnce({ data: [], error: null });
        const result = await ClaimDAO.getUnverifiedClaimsBySession('s-1');
        expect(result).toEqual([]);
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ClaimRecordSchema', async () => {
        mockOrder.mockResolvedValueOnce({ data: [recordRow], error: null });
        const result = await ClaimDAO.getUnverifiedClaimsBySession('s-1');
        expect(ClaimRecordSchema.safeParse(result[0]).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockOrder.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.getUnverifiedClaimsBySession('x')).rejects.toThrow(DomainError);
      });
    });
  });

  // --- updateStatusToVerified ---
  describe('updateStatusToVerified', () => {
    const verifiedRow = { id: 'cr-1', session_id: 's-1', category: 'metrics', status: 'verified', content: 'Revenue', contact_phone: null, contact_method: null, verified_at: '2026-01-02', disputed_at: null, created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('batch updates claims and returns verified records', async () => {
        mockSelect.mockResolvedValueOnce({ data: [verifiedRow], error: null });
        const result = await ClaimDAO.updateStatusToVerified(['cr-1']);
        expect(result).toHaveLength(1);
        expect(result[0].status).toBe('verified');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ClaimRecordSchema', async () => {
        mockSelect.mockResolvedValueOnce({ data: [verifiedRow], error: null });
        const result = await ClaimDAO.updateStatusToVerified(['cr-1']);
        expect(ClaimRecordSchema.safeParse(result[0]).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockSelect.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.updateStatusToVerified(['x'])).rejects.toThrow(DomainError);
      });
    });
  });

  // --- updateStatus ---
  describe('updateStatus', () => {
    const row = { id: 'c-1', content: 'Led team', status: 'DENIED', sms_opt_in: false, phone_number: null, truth_checks: [], created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('updates status and returns claim', async () => {
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimDAO.updateStatus('c-1', 'DENIED');
        expect(result.status).toBe('DENIED');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ClaimSchema', async () => {
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimDAO.updateStatus('c-1', 'DENIED');
        expect(ClaimSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.updateStatus('x', 'DENIED')).rejects.toThrow(DomainError);
      });
    });
  });

  // --- getClaimsByCaseId ---
  describe('getClaimsByCaseId', () => {
    const row = { id: 'cc-1', case_id: 'case-1', text: 'Revenue increase', status: 'confirmed', metadata: { metric: '25%', scope: 'Q3', context: 'Outreach' } };

    describe('Reachability', () => {
      it('returns case claims', async () => {
        mockEq.mockResolvedValueOnce({ data: [row], error: null });
        const result = await ClaimDAO.getClaimsByCaseId('case-1');
        expect(result).toHaveLength(1);
        expect(result[0].caseId).toBe('case-1');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns empty array when none found', async () => {
        mockEq.mockResolvedValueOnce({ data: [], error: null });
        const result = await ClaimDAO.getClaimsByCaseId('case-none');
        expect(result).toEqual([]);
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to CaseClaimSchema', async () => {
        mockEq.mockResolvedValueOnce({ data: [row], error: null });
        const result = await ClaimDAO.getClaimsByCaseId('case-1');
        expect(CaseClaimSchema.safeParse(result[0]).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockEq.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.getClaimsByCaseId('x')).rejects.toThrow(DomainError);
      });
    });
  });

  // --- getClaimsByStoryRecordId ---
  describe('getClaimsByStoryRecordId', () => {
    const row = { id: 'src-1', story_record_id: 'sr-1', content: 'Led team of 5', confirmed: true };

    describe('Reachability', () => {
      it('returns story record claims', async () => {
        mockEq.mockResolvedValueOnce({ data: [row], error: null });
        const result = await ClaimDAO.getClaimsByStoryRecordId('sr-1');
        expect(result).toHaveLength(1);
        expect(result[0].storyRecordId).toBe('sr-1');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns empty array when none found', async () => {
        mockEq.mockResolvedValueOnce({ data: [], error: null });
        const result = await ClaimDAO.getClaimsByStoryRecordId('sr-none');
        expect(result).toEqual([]);
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to StoryRecordClaimSchema', async () => {
        mockEq.mockResolvedValueOnce({ data: [row], error: null });
        const result = await ClaimDAO.getClaimsByStoryRecordId('sr-1');
        expect(StoryRecordClaimSchema.safeParse(result[0]).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockEq.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.getClaimsByStoryRecordId('x')).rejects.toThrow(DomainError);
      });
    });
  });

  // --- getConfirmedClaims ---
  describe('getConfirmedClaims', () => {
    const row = { id: 'cf-1', session_id: 's-1', content: 'Revenue up 25%', status: 'CONFIRMED', metric: '25%', scope: 'Q3', context: 'Outreach', created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns only CONFIRMED claims', async () => {
        mockEq
          .mockReturnValueOnce({ eq: mockEq })
          .mockResolvedValueOnce({ data: [row], error: null });
        const result = await ClaimDAO.getConfirmedClaims('s-1');
        expect(result).toHaveLength(1);
        expect(result[0].status).toBe('CONFIRMED');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns empty array when none confirmed', async () => {
        mockEq
          .mockReturnValueOnce({ eq: mockEq })
          .mockResolvedValueOnce({ data: [], error: null });
        const result = await ClaimDAO.getConfirmedClaims('s-1');
        expect(result).toEqual([]);
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ConfirmedClaimSchema', async () => {
        mockEq
          .mockReturnValueOnce({ eq: mockEq })
          .mockResolvedValueOnce({ data: [row], error: null });
        const result = await ClaimDAO.getConfirmedClaims('s-1');
        expect(ConfirmedClaimSchema.safeParse(result[0]).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on DB failure', async () => {
        mockEq
          .mockReturnValueOnce({ eq: mockEq })
          .mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(ClaimDAO.getConfirmedClaims('x')).rejects.toThrow(DomainError);
      });
    });
  });
});
