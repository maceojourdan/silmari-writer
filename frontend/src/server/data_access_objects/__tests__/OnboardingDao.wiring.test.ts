/**
 * OnboardingDao Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { OnboardingSchema } from '@/server/data_structures/Onboarding';
import { AnalyticsEventSchema } from '@/server/data_structures/AnalyticsEvent';
import { BackendError } from '@/server/error_definitions/BackendErrors';

function createChainMock() {
  let resolveValue: { data: unknown; error: unknown } = { data: null, error: null };
  const setResult = (val: { data: unknown; error: unknown }) => { resolveValue = val; };
  const chain: Record<string, unknown> = {};
  for (const m of ['select', 'eq', 'insert', 'update', 'delete', 'upsert']) {
    chain[m] = vi.fn(() => chain);
  }
  chain.single = vi.fn(() => Promise.resolve(resolveValue));
  chain.maybeSingle = vi.fn(() => Promise.resolve(resolveValue));
  chain.then = (resolve: (v: unknown) => void) => Promise.resolve(resolveValue).then(resolve);
  return { chain, setResult };
}

const { mockFrom } = vi.hoisted(() => ({ mockFrom: vi.fn() }));
vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { OnboardingDao } from '../OnboardingDao';

const UUID1 = '00000000-0000-4000-8000-000000000001';
const UUID2 = '00000000-0000-4000-8000-000000000002';

let mockChain: ReturnType<typeof createChainMock>;

describe('OnboardingDao — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockChain = createChainMock();
    mockFrom.mockReturnValue(mockChain.chain);
  });

  describe('findByUserAndStep', () => {
    const row = { id: UUID1, user_id: 'u-1', step: 1, status: 'NOT_STARTED', completed_at: null, created_at: '2026-01-01', updated_at: '2026-01-01' };
    const typeRow = { id: UUID1, user_id: 'u-1', step: 1, status: 'COMPLETED', completed_at: '2026-01-01', created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns onboarding when found', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.findByUserAndStep('u-1', 1);
        expect(result).not.toBeNull();
        expect(result!.id).toBe(UUID1);
        expect(mockFrom).toHaveBeenCalledWith('onboarding');
      });
      it('returns null when not found', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await OnboardingDao.findByUserAndStep('u-1', 99);
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to OnboardingSchema', async () => {
        mockChain.setResult({ data: typeRow, error: null });
        const result = await OnboardingDao.findByUserAndStep('u-1', 1);
        expect(OnboardingSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BackendError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(OnboardingDao.findByUserAndStep('u-1', 1)).rejects.toThrow(BackendError);
      });
    });
  });

  describe('updateOnboardingStep', () => {
    const row = { id: UUID1, user_id: 'u-1', step: 1, status: 'COMPLETED', completed_at: '2026-01-02', created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('returns updated onboarding', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.updateOnboardingStep('u-1', 1, { status: 'COMPLETED', completedAt: '2026-01-02' });
        expect(result.status).toBe('COMPLETED');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to OnboardingSchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.updateOnboardingStep('u-1', 1, { status: 'COMPLETED', completedAt: '2026-01-02' });
        expect(OnboardingSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BackendError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(OnboardingDao.updateOnboardingStep('u-1', 1, { status: 'COMPLETED' })).rejects.toThrow(BackendError);
      });
    });
  });

  describe('createOnboarding', () => {
    const row = { id: UUID1, user_id: 'u-1', step: 1, status: 'NOT_STARTED', completed_at: null, created_at: '2026-01-01', updated_at: '2026-01-01' };
    const typeRow = { id: UUID1, user_id: 'u-1', step: 1, status: 'NOT_STARTED', completed_at: '2026-01-01', created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns created onboarding', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.createOnboarding({ userId: 'u-1', step: 1 });
        expect(result.userId).toBe('u-1');
        expect(result.step).toBe(1);
        expect(mockFrom).toHaveBeenCalledWith('onboarding');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to OnboardingSchema', async () => {
        mockChain.setResult({ data: typeRow, error: null });
        const result = await OnboardingDao.createOnboarding({ userId: 'u-1', step: 1 });
        expect(OnboardingSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BackendError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(OnboardingDao.createOnboarding({ userId: 'u-1', step: 1 })).rejects.toThrow(BackendError);
      });
    });
  });

  describe('insertAnalyticsEvent', () => {
    const row = { id: UUID2, kpi_id: 'kpi-1', user_id: 'u-1', timestamp: '2026-01-01T00:00:00Z', metadata: {}, created_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns created analytics event', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.insertAnalyticsEvent({ kpiId: 'kpi-1', userId: 'u-1', timestamp: '2026-01-01T00:00:00Z', metadata: {} });
        expect(result.kpiId).toBe('kpi-1');
        expect(mockFrom).toHaveBeenCalledWith('analytics_events');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to AnalyticsEventSchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.insertAnalyticsEvent({ kpiId: 'kpi-1', userId: 'u-1', timestamp: '2026-01-01T00:00:00Z', metadata: {} });
        expect(AnalyticsEventSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BackendError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(OnboardingDao.insertAnalyticsEvent({ kpiId: 'kpi-1', userId: 'u-1', timestamp: '2026-01-01T00:00:00Z', metadata: {} })).rejects.toThrow(BackendError);
      });
    });
  });

  describe('findAnalyticsEvent', () => {
    const row = { id: UUID2, kpi_id: 'kpi-1', user_id: 'u-1', timestamp: '2026-01-01T00:00:00Z', metadata: {}, created_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns analytics event when found', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.findAnalyticsEvent('u-1', 'kpi-1', {});
        expect(result).not.toBeNull();
        expect(result!.kpiId).toBe('kpi-1');
        expect(mockFrom).toHaveBeenCalledWith('analytics_events');
      });
      it('returns null when not found', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await OnboardingDao.findAnalyticsEvent('u-1', 'kpi-1', {});
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to AnalyticsEventSchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await OnboardingDao.findAnalyticsEvent('u-1', 'kpi-1', {});
        expect(AnalyticsEventSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws BackendError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(OnboardingDao.findAnalyticsEvent('u-1', 'kpi-1', {})).rejects.toThrow(BackendError);
      });
    });
  });
});
