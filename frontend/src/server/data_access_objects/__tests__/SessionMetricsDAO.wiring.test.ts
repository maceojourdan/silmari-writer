/**
 * SessionMetricsDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionMetricsSchema, AggregatedSessionDatasetSchema } from '@/server/data_structures/SessionMetrics';
import { MetricsError } from '@/server/error_definitions/MetricsErrors';

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

import { SessionMetricsDAO } from '../SessionMetricsDAO';

const UUID1 = '00000000-0000-4000-8000-000000000001';
const UUID2 = '00000000-0000-4000-8000-000000000002';

let mockChain: ReturnType<typeof createChainMock>;

describe('SessionMetricsDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockChain = createChainMock();
    mockFrom.mockReturnValue(mockChain.chain);
  });

  describe('getSessionWithEvents', () => {
    const sessionRow = { id: UUID1, status: 'FINALIZED', created_at: '2026-01-01', updated_at: '2026-01-02', first_draft_at: '2026-01-01T01:00:00Z', finalized_at: '2026-01-02T00:00:00Z' };
    const eventsRow = [{ id: UUID2, session_id: UUID1, category: 'DRAFT', timestamp: '2026-01-01T01:00:00Z', metadata: {} }];

    describe('Reachability', () => {
      it('returns aggregated dataset when found', async () => {
        // First call gets the session, second call gets events
        const sessionChain = createChainMock();
        sessionChain.setResult({ data: sessionRow, error: null });
        const eventsChain = createChainMock();
        eventsChain.setResult({ data: eventsRow, error: null });
        mockFrom.mockReturnValueOnce(sessionChain.chain).mockReturnValueOnce(eventsChain.chain);

        const result = await SessionMetricsDAO.getSessionWithEvents(UUID1);
        expect(result).not.toBeNull();
        expect(result!.session.id).toBe(UUID1);
        expect(mockFrom).toHaveBeenCalledWith('sessions');
      });
      it('returns null when session not found', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await SessionMetricsDAO.getSessionWithEvents('x');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws MetricsError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(SessionMetricsDAO.getSessionWithEvents('x')).rejects.toThrow(MetricsError);
      });
    });
  });

  describe('upsertSessionMetrics', () => {
    const metricsRow = { id: UUID1, session_id: UUID2, time_to_first_draft: 100, completion_rate: 0.9, confirmation_rate: 0.8, signal_density: 0.7, drop_off: 0.1, created_at: '2026-01-01', updated_at: '2026-01-02' };
    const metricsInput = { sessionId: UUID2, timeToFirstDraft: 100, completionRate: 0.9, confirmationRate: 0.8, signalDensity: 0.7, dropOff: 0.1 };

    describe('Reachability', () => {
      it('returns upserted metrics', async () => {
        mockChain.setResult({ data: metricsRow, error: null });
        const result = await SessionMetricsDAO.upsertSessionMetrics(metricsInput);
        expect(result.sessionId).toBe(UUID2);
        expect(mockFrom).toHaveBeenCalledWith('session_metrics');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to SessionMetricsSchema', async () => {
        mockChain.setResult({ data: metricsRow, error: null });
        const result = await SessionMetricsDAO.upsertSessionMetrics(metricsInput);
        expect(SessionMetricsSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws MetricsError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(SessionMetricsDAO.upsertSessionMetrics(metricsInput)).rejects.toThrow(MetricsError);
      });
    });
  });
});
