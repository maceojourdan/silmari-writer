/**
 * DraftingWorkflowDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { DomainError } from '@/server/error_definitions/DomainErrors';

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

import { DraftingWorkflowDAO } from '../DraftingWorkflowDAO';

let mockChain: ReturnType<typeof createChainMock>;

describe('DraftingWorkflowDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockChain = createChainMock();
    mockFrom.mockReturnValue(mockChain.chain);
  });

  describe('findByClaimId', () => {
    describe('Reachability', () => {
      it('returns workflow when found', async () => {
        const row = { id: 'wf-1', claim_id: 'c-1', status: 'Ready', created_at: '2026-01-01', updated_at: '2026-01-01' };
        mockChain.setResult({ data: row, error: null });
        const result = await DraftingWorkflowDAO.findByClaimId('c-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('drafting_workflows');
      });
      it('returns null when not found', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await DraftingWorkflowDAO.findByClaimId('x');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(DraftingWorkflowDAO.findByClaimId('x')).rejects.toThrow(DomainError);
      });
    });
  });

  describe('updateStatus', () => {
    describe('Reachability', () => {
      it('returns updated workflow', async () => {
        const row = { id: 'wf-1', claim_id: 'c-1', status: 'On Hold', reason: 'timeout', created_at: '2026-01-01', updated_at: '2026-01-02' };
        mockChain.setResult({ data: row, error: null });
        const result = await DraftingWorkflowDAO.updateStatus('wf-1', 'On Hold', 'timeout');
        expect(result.status).toBe('On Hold');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws DomainError on failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(DraftingWorkflowDAO.updateStatus('wf-1', 'On Hold')).rejects.toThrow(DomainError);
      });
    });
  });
});
