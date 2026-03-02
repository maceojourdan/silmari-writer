/**
 * ContentDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';
import { EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';

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

import { ContentDAO } from '../ContentDAO';

const UUID1 = '00000000-0000-4000-8000-000000000001';

let mockChain: ReturnType<typeof createChainMock>;

describe('ContentDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockChain = createChainMock();
    mockFrom.mockReturnValue(mockChain.chain);
  });

  describe('findById', () => {
    const row = { id: UUID1, body: 'text', status: 'REVIEW', workflow_stage: 'REVIEW', created_at: '2026-01-01', updated_at: '2026-01-01' };

    describe('Reachability', () => {
      it('returns content entity when found', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await ContentDAO.findById(UUID1);
        expect(result).not.toBeNull();
        expect(result!.id).toBe(UUID1);
        expect(mockFrom).toHaveBeenCalledWith('content');
      });
      it('returns null when not found', async () => {
        mockChain.setResult({ data: null, error: null });
        const result = await ContentDAO.findById('x');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ContentEntitySchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await ContentDAO.findById(UUID1);
        expect(ContentEntitySchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws ApprovalError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(ContentDAO.findById('x')).rejects.toThrow(ApprovalError);
      });
    });
  });

  describe('update', () => {
    const row = { id: UUID1, body: 'text', status: 'APPROVED', workflow_stage: 'FINALIZE', created_at: '2026-01-01', updated_at: '2026-01-02' };

    describe('Reachability', () => {
      it('returns updated content entity', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await ContentDAO.update(UUID1, 'APPROVED', 'FINALIZE');
        expect(result.status).toBe('APPROVED');
        expect(result.workflowStage).toBe('FINALIZE');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ContentEntitySchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await ContentDAO.update(UUID1, 'APPROVED', 'FINALIZE');
        expect(ContentEntitySchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws ApprovalError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(ContentDAO.update('x', 'APPROVED', 'FINALIZE')).rejects.toThrow(ApprovalError);
      });
    });
  });

  describe('updateContent', () => {
    const row = { id: UUID1, body: 'revised', status: 'REVIEW', workflow_stage: 'REVIEW', created_at: '2026-01-01', updated_at: '2026-01-02' };
    const entity = { id: UUID1, body: 'revised', status: 'REVIEW' as const, workflowStage: 'REVIEW' as const, createdAt: '2026-01-01', updatedAt: '2026-01-01' };

    describe('Reachability', () => {
      it('returns updated content entity', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await ContentDAO.updateContent(entity);
        expect(result.body).toBe('revised');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to ContentEntitySchema', async () => {
        mockChain.setResult({ data: row, error: null });
        const result = await ContentDAO.updateContent(entity);
        expect(ContentEntitySchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws EditByVoiceError on DB failure', async () => {
        mockChain.setResult({ data: null, error: { message: 'fail' } });
        await expect(ContentDAO.updateContent(entity)).rejects.toThrow(EditByVoiceError);
      });
    });
  });
});
