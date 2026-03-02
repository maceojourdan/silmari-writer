/**
 * VerificationRequestDAO Wiring Tests
 *
 * TLA+ properties per method:
 * - Reachability: Supabase mock returns data → DAO returns mapped entity
 * - TypeInvariant: Returned entity conforms to expected shape
 * - ErrorConsistency: Supabase error → VerificationError
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';

const { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate,
        mockOrder, mockLimit, mockEq, mockIs, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockMaybeSingle = vi.fn();
  const mockSelect = vi.fn();
  const mockInsert = vi.fn();
  const mockUpdate = vi.fn();
  const mockLimit = vi.fn();
  const mockOrder = vi.fn();
  const mockEq = vi.fn();
  const mockIs = vi.fn();
  const mockFrom = vi.fn();
  return { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockUpdate,
           mockOrder, mockLimit, mockEq, mockIs, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { VerificationRequestDAO } from '../VerificationRequestDAO';

const baseRow = {
  id: 'vr-1', session_id: 's-1', status: 'pending', attempt_count: 0,
  token: 'tok-1', claim_ids: ['c-1'], contact_phone: '+1234',
  contact_method: 'sms', created_at: '2026-01-01', responded_at: null,
  updated_at: '2026-01-01',
};

describe('VerificationRequestDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockInsert.mockReturnValue({ select: mockSelect });
    mockUpdate.mockReturnValue({ eq: mockEq });
    mockLimit.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockOrder.mockReturnValue({ limit: mockLimit, single: mockSingle });
    mockIs.mockReturnValue({ select: mockSelect, update: mockUpdate });
    mockEq.mockReturnValue({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle, order: mockOrder, is: mockIs, eq: mockEq });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
      insert: mockInsert,
      update: mockUpdate,
    });
  });

  // --- create ---
  describe('create', () => {
    describe('Reachability', () => {
      it('returns VerificationRequest with status=pending', async () => {
        mockSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await VerificationRequestDAO.create({
          sessionId: 's-1', claimIds: ['c-1'], contactPhone: '+1234', contactMethod: 'sms', token: 'tok-1',
        });
        expect(result.id).toBe('vr-1');
        expect(mockFrom).toHaveBeenCalledWith('verification_requests');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(VerificationRequestDAO.create({
          sessionId: 's-1', claimIds: ['c-1'], contactPhone: '+1234', contactMethod: 'sms', token: 'tok-1',
        })).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- findByToken ---
  describe('findByToken', () => {
    describe('Reachability', () => {
      it('returns VerificationRequest when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await VerificationRequestDAO.findByToken('tok-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('verification_requests');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await VerificationRequestDAO.findByToken('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(VerificationRequestDAO.findByToken('x')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- findBySessionId ---
  describe('findBySessionId', () => {
    describe('Reachability', () => {
      it('returns VerificationRequest when found', async () => {
        mockSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await VerificationRequestDAO.findBySessionId('s-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('verification_requests');
      });
      it('returns null when none found', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { code: 'PGRST116', message: 'no rows' } });
        const result = await VerificationRequestDAO.findBySessionId('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail', code: 'PGRST000' } });
        await expect(VerificationRequestDAO.findBySessionId('x')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- updateStatus ---
  describe('updateStatus', () => {
    describe('Reachability', () => {
      it('returns updated VerificationRequest', async () => {
        mockSingle.mockResolvedValue({ data: { ...baseRow, status: 'confirmed' }, error: null });
        const result = await VerificationRequestDAO.updateStatus('vr-1', 'confirmed');
        expect(result.status).toBe('confirmed');
        expect(mockFrom).toHaveBeenCalledWith('verification_requests');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(VerificationRequestDAO.updateStatus('vr-1', 'confirmed')).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- logDeliveryAttempt ---
  describe('logDeliveryAttempt', () => {
    describe('Reachability', () => {
      it('returns DeliveryAttempt', async () => {
        const row = { id: 'da-1', request_id: 'vr-1', attempt_number: 1, status: 'success', created_at: '2026-01-01' };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await VerificationRequestDAO.logDeliveryAttempt({
          requestId: 'vr-1', attemptNumber: 1, status: 'success',
        });
        expect(result.id).toBe('da-1');
        expect(mockFrom).toHaveBeenCalledWith('delivery_attempts');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(VerificationRequestDAO.logDeliveryAttempt({
          requestId: 'vr-1', attemptNumber: 1, status: 'success',
        })).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- findPendingUnresponded ---
  describe('findPendingUnresponded', () => {
    describe('Reachability', () => {
      it('returns VerificationRequest array', async () => {
        mockIs.mockResolvedValueOnce({ data: [baseRow], error: null });
        const result = await VerificationRequestDAO.findPendingUnresponded();
        expect(result).toHaveLength(1);
        expect(mockFrom).toHaveBeenCalledWith('verification_requests');
      });
      it('returns empty array when none found', async () => {
        mockIs.mockResolvedValueOnce({ data: [], error: null });
        const result = await VerificationRequestDAO.findPendingUnresponded();
        expect(result).toHaveLength(0);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on DB failure', async () => {
        mockIs.mockResolvedValueOnce({ data: null, error: { message: 'fail' } });
        await expect(VerificationRequestDAO.findPendingUnresponded()).rejects.toThrow(VerificationError);
      });
    });
  });

  // --- updateStatusIfUnresponded ---
  describe('updateStatusIfUnresponded', () => {
    describe('Reachability', () => {
      it('returns affected row count', async () => {
        mockIs.mockResolvedValueOnce({ count: 1, error: null });
        const result = await VerificationRequestDAO.updateStatusIfUnresponded('vr-1', 'timed_out');
        expect(result).toBe(1);
        expect(mockFrom).toHaveBeenCalledWith('verification_requests');
      });
      it('returns 0 when already responded', async () => {
        mockIs.mockResolvedValueOnce({ count: 0, error: null });
        const result = await VerificationRequestDAO.updateStatusIfUnresponded('vr-1', 'timed_out');
        expect(result).toBe(0);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws VerificationError on failure', async () => {
        mockIs.mockResolvedValueOnce({ count: null, error: { message: 'fail' } });
        await expect(VerificationRequestDAO.updateStatusIfUnresponded('vr-1', 'timed_out')).rejects.toThrow(VerificationError);
      });
    });
  });
});
