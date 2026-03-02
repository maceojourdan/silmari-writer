/**
 * AnswerDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AnswerSchema } from '@/server/data_structures/Answer';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';

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

import { AnswerDAO } from '../AnswerDAO';

const UUID1 = '00000000-0000-4000-8000-000000000001';

let mockChain: ReturnType<typeof createChainMock>;

describe('AnswerDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockChain = createChainMock();
    mockFrom.mockReturnValue(mockChain.chain);
  });

  describe('findById', () => {
    const row = { id: UUID1, status: 'DRAFT', finalized: false, editable: true, locked: false, content: 'text', user_id: 'u-1', created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns answer when found', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await AnswerDAO.findById(UUID1);
        expect(result).not.toBeNull();
        expect(result!.id).toBe(UUID1);
        expect(mockFrom).toHaveBeenCalledWith('answers');
      });
      it('returns null when not found', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await AnswerDAO.findById('x');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to AnswerSchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await AnswerDAO.findById(UUID1);
        expect(AnswerSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws AnswerError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(AnswerDAO.findById('x')).rejects.toThrow(AnswerError);
      });
    });
  });

  describe('update', () => {
    const row = { id: UUID1, status: 'FINALIZED', finalized: true, editable: false, locked: false, content: 'text', user_id: 'u-1', created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('returns updated answer', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await AnswerDAO.update(UUID1, { finalized: true, editable: false, status: 'FINALIZED' });
        expect(result.finalized).toBe(true);
        expect(result.editable).toBe(false);
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to AnswerSchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await AnswerDAO.update(UUID1, { finalized: true, editable: false, status: 'FINALIZED' });
        expect(AnswerSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws AnswerError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(AnswerDAO.update('x', { finalized: true })).rejects.toThrow(AnswerError);
      });
    });
  });

  describe('updateContent', () => {
    const row = { id: UUID1, status: 'DRAFT', finalized: false, editable: true, locked: false, content: 'revised', user_id: 'u-1', created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('returns updated answer with new content', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await AnswerDAO.updateContent(UUID1, 'revised');
        expect(result.content).toBe('revised');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to AnswerSchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await AnswerDAO.updateContent(UUID1, 'revised');
        expect(AnswerSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws AnswerError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(AnswerDAO.updateContent('x', 'revised')).rejects.toThrow(AnswerError);
      });
    });
  });
});
