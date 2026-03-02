/**
 * PrimaryKpiDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { KpiError } from '@/server/error_definitions/KpiErrors';

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

import { PrimaryKpiDAO } from '../PrimaryKpiDAO';

const baseRow = {
  id: 'kpi-1', user_id: 'u-1', action_type: 'purchase',
  metadata: { amount: 100 }, status: 'PENDING',
  timestamp: '2026-01-01T00:00:00Z', created_at: '2026-01-01',
};

describe('PrimaryKpiDAO — Supabase Wiring', () => {
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

  // --- insert ---
  describe('insert', () => {
    describe('Reachability', () => {
      it('returns PrimaryKpiRecord with generated ID', async () => {
        mockSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await PrimaryKpiDAO.insert({
          userId: 'u-1', actionType: 'purchase', metadata: { amount: 100 },
          status: 'PENDING', timestamp: '2026-01-01T00:00:00Z',
        });
        expect(result.id).toBe('kpi-1');
        expect(mockFrom).toHaveBeenCalledWith('primary_kpi_events');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws KpiError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(PrimaryKpiDAO.insert({
          userId: 'u-1', actionType: 'purchase', metadata: {},
          status: 'PENDING', timestamp: '2026-01-01T00:00:00Z',
        })).rejects.toThrow(KpiError);
      });
    });
  });

  // --- findById ---
  describe('findById', () => {
    describe('Reachability', () => {
      it('returns PrimaryKpiRecord when found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await PrimaryKpiDAO.findById('kpi-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('kpi-1');
        expect(mockFrom).toHaveBeenCalledWith('primary_kpi_events');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await PrimaryKpiDAO.findById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws KpiError on failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(PrimaryKpiDAO.findById('x')).rejects.toThrow(KpiError);
      });
    });
  });

  // --- updateStatus ---
  describe('updateStatus', () => {
    describe('Reachability', () => {
      it('returns updated PrimaryKpiRecord', async () => {
        mockSingle.mockResolvedValue({ data: { ...baseRow, status: 'ANALYTICS_SENT' }, error: null });
        const result = await PrimaryKpiDAO.updateStatus('kpi-1', 'ANALYTICS_SENT');
        expect(result.status).toBe('ANALYTICS_SENT');
        expect(mockFrom).toHaveBeenCalledWith('primary_kpi_events');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws KpiError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(PrimaryKpiDAO.updateStatus('kpi-1', 'ANALYTICS_SENT')).rejects.toThrow(KpiError);
      });
    });
  });
});
