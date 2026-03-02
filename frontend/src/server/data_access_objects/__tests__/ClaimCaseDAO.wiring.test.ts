/**
 * ClaimCaseDAO Wiring Tests
 *
 * TLA+ properties per method:
 * - Reachability: Supabase mock returns data → DAO returns mapped entity
 * - TypeInvariant: Returned entity conforms to Zod schema
 * - ErrorConsistency: Supabase error → VerificationError with DATA_ACCESS_ERROR code
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ClaimRecordSchema } from '@/server/data_structures/ClaimRecord';
import { CaseSchema } from '@/server/data_structures/Case';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';

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

import { ClaimCaseDAO } from '../ClaimCaseDAO';

describe('ClaimCaseDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockEq.mockReturnValue({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle });
    mockUpdate.mockReturnValue({ eq: vi.fn(() => ({ select: mockSelect })) });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
      update: mockUpdate,
    });
  });

  // --- getClaimById ---
  describe('getClaimById', () => {
    const row = { id: 'cr-1', session_id: 's-1', category: 'metrics', status: 'unverified', content: 'Revenue', contact_phone: null, contact_method: null, verified_at: null, disputed_at: null, created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns claim record when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.getClaimById('cr-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('cr-1');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await ClaimCaseDAO.getClaimById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ClaimRecordSchema', async () => {
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.getClaimById('cr-1');
        expect(ClaimRecordSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ClaimCaseDAO.getClaimById('x')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- updateClaimVerificationStatus ---
  describe('updateClaimVerificationStatus', () => {
    const row = { id: 'cr-1', session_id: 's-1', category: 'metrics', status: 'not_verified', content: 'Revenue', contact_phone: null, contact_method: null, verified_at: null, disputed_at: '2026-01-02', created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('updates status and returns claim record', async () => {
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.updateClaimVerificationStatus('cr-1', 'not_verified', '2026-01-02');
        expect(result.status).toBe('not_verified');
        expect(result.disputedAt).toBe('2026-01-02');
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ClaimRecordSchema', async () => {
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.updateClaimVerificationStatus('cr-1', 'not_verified', '2026-01-02');
        expect(ClaimRecordSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ClaimCaseDAO.updateClaimVerificationStatus('x', 'not_verified', '2026-01-02')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- getCaseByClaimantId ---
  describe('getCaseByClaimantId', () => {
    const row = { id: 'case-1', claimant_id: 'cl-1', session_id: 's-1', drafting_status: 'drafting_allowed', created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns case when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.getCaseByClaimantId('cl-1');
        expect(result).not.toBeNull();
        expect(result!.claimantId).toBe('cl-1');
        expect(mockFrom).toHaveBeenCalledWith('cases');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await ClaimCaseDAO.getCaseByClaimantId('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to CaseSchema', async () => {
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.getCaseByClaimantId('cl-1');
        expect(CaseSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ClaimCaseDAO.getCaseByClaimantId('x')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- updateCaseDraftingStatus ---
  describe('updateCaseDraftingStatus', () => {
    const row = { id: 'case-1', claimant_id: 'cl-1', session_id: 's-1', drafting_status: 'blocked_due_to_unverified_claims', created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('updates drafting status and returns case', async () => {
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.updateCaseDraftingStatus('case-1', 'blocked_due_to_unverified_claims');
        expect(result.drafting_status).toBe('blocked_due_to_unverified_claims');
        expect(mockFrom).toHaveBeenCalledWith('cases');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to CaseSchema', async () => {
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await ClaimCaseDAO.updateCaseDraftingStatus('case-1', 'blocked_due_to_unverified_claims');
        expect(CaseSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(ClaimCaseDAO.updateCaseDraftingStatus('x', 'blocked_due_to_unverified_claims')).rejects.toThrow(VerificationError);
      });
    });
  });
});
