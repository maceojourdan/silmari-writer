/**
 * DraftDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DraftError } from '@/server/error_definitions/DraftErrors';

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

import { DraftDAO } from '../DraftDAO';

let mockChain: ReturnType<typeof createChainMock>;

describe('DraftDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockChain = createChainMock();
    mockFrom.mockReturnValue(mockChain.chain);
  });

  describe('getDraftById', () => {
    describe('Reachability', () => {
      it('returns draft when found', async () => {
        const row = { id: 'd-1', status: 'DRAFT', content: 'text', user_id: 'u-1', created_at: '2026-01-01', updated_at: '2026-01-01' };
        mockChain.setResult({ data: row, error: null });
        const result = await DraftDAO.getDraftById('d-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('d-1');
        expect(mockFrom).toHaveBeenCalledWith('drafts');
      });
      it('returns null when not found', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await DraftDAO.getDraftById('x');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DraftError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(DraftDAO.getDraftById('x')).rejects.toThrow(DraftError);
      });
    });
  });

  describe('updateStatus', () => {
    describe('Reachability', () => {
      it('returns updated draft', async () => {
        const row = { id: 'd-1', status: 'FINALIZED', content: 'text', user_id: 'u-1', created_at: '2026-01-01', updated_at: '2026-01-02' };
        mockChain.setResult({ data: row, error: null });
        const result = await DraftDAO.updateStatus('d-1', 'FINALIZED');
        expect(result.status).toBe('FINALIZED');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DraftError on failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(DraftDAO.updateStatus('d-1', 'FINALIZED')).rejects.toThrow(DraftError);
      });
    });
  });

  describe('insertMetrics', () => {
    describe('Reachability', () => {
      it('inserts without error', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await DraftDAO.insertMetrics('d-1', { timeToDraft: 100, confirmationRate: 0.9, signalDensity: 0.5 });
        expect(result).toBeUndefined();
        expect(mockFrom).toHaveBeenCalledWith('draft_metrics');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DraftError on failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(DraftDAO.insertMetrics('d-1', { timeToDraft: 100, confirmationRate: 0.9, signalDensity: 0.5 })).rejects.toThrow(DraftError);
      });
    });
  });
});
