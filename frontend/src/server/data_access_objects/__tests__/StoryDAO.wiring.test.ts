// @ts-nocheck
/**
 * StoryDAO Wiring Tests
 *
 * TLA+ properties per method:
 * - Reachability: Supabase mock returns data → DAO returns mapped entity
 * - TypeInvariant: Returned entity conforms to expected shape
 * - ErrorConsistency: Supabase error → StoryError with PERSISTENCE_FAILED
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoryError } from '@/server/error_definitions/StoryErrors';
import { StoryClaimSchema } from '@/server/data_structures/StoryStructures';
import { StructuredDraftSchema } from '@/server/data_structures/StoryStructures';

const { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockOrder, mockEq, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn<any, any>();
  const mockMaybeSingle = vi.fn<any, any>();
  const mockSelect = vi.fn<any, any>(() => ({ single: mockSingle, maybeSingle: mockMaybeSingle }));
  const mockInsert = vi.fn<any, any>(() => ({ select: mockSelect }));
  const mockOrder = vi.fn<any, any>();
  // Default: order returns self (for chaining .order().order())
  mockOrder.mockReturnValue({ order: mockOrder });
  const mockEq = vi.fn<any, any>(() => ({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle, order: mockOrder }));
  const mockFrom = vi.fn<any, any>(() => ({
    select: vi.fn(() => ({ eq: mockEq })),
    insert: mockInsert,
  }));
  return { mockSingle, mockMaybeSingle, mockSelect, mockInsert, mockOrder, mockEq, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { StoryDAO } from '../StoryDAO';

describe('StoryDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    // Restore default mock chain after clearAllMocks
    mockSelect.mockReturnValue({ single: mockSingle, maybeSingle: mockMaybeSingle });
    mockInsert.mockReturnValue({ select: mockSelect });
    mockOrder.mockReturnValue({ order: mockOrder });
    mockEq.mockReturnValue({ select: mockSelect, single: mockSingle, maybeSingle: mockMaybeSingle, order: mockOrder });
    mockFrom.mockReturnValue({
      select: vi.fn(() => ({ eq: mockEq })),
      insert: mockInsert,
    });
  });

  // --- findDraftById ---
  describe('findDraftById', () => {
    describe('Reachability', () => {
      it('returns DraftData when found', async () => {
        const row = { id: 'd-1', content: 'text', resume_id: 'r-1', job_id: 'j-1', question_id: 'q-1', voice_session_id: 'vs-1' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findDraftById('d-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('d-1');
        expect(mockFrom).toHaveBeenCalledWith('drafts');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await StoryDAO.findDraftById('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('returned object has DraftData shape', async () => {
        const row = { id: 'd-1', content: 'text', resume_id: 'r-1', job_id: 'j-1', question_id: 'q-1', voice_session_id: 'vs-1' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findDraftById('d-1');
        expect(result).toHaveProperty('id');
        expect(result).toHaveProperty('content');
        expect(result).toHaveProperty('resumeId');
        expect(result).toHaveProperty('jobId');
        expect(result).toHaveProperty('questionId');
        expect(result).toHaveProperty('voiceSessionId');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findDraftById('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- findResumeById ---
  describe('findResumeById', () => {
    describe('Reachability', () => {
      it('returns ResumeData when found', async () => {
        const row = { id: 'r-1', name: 'John', content: 'resume text' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findResumeById('r-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('r-1');
        expect(mockFrom).toHaveBeenCalledWith('resumes');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findResumeById('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- findJobById ---
  describe('findJobById', () => {
    describe('Reachability', () => {
      it('returns JobData when found', async () => {
        const row = { id: 'j-1', title: 'SE', description: 'desc' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findJobById('j-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('jobs');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findJobById('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- findQuestionById ---
  describe('findQuestionById', () => {
    describe('Reachability', () => {
      it('returns QuestionData when found', async () => {
        const row = { id: 'q-1', text: 'Tell me...' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findQuestionById('q-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('questions');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findQuestionById('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- findSessionById ---
  describe('findSessionById', () => {
    describe('Reachability', () => {
      it('returns SessionData when found', async () => {
        const row = { id: 's-1', duration_ms: 5000, started_at: '2026-01-01', ended_at: '2026-01-01' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findSessionById('s-1');
        expect(result).not.toBeNull();
        expect(result!.id).toBe('s-1');
      });
    });
    describe('TypeInvariant', () => {
      it('maps snake_case columns to camelCase', async () => {
        const row = { id: 's-1', duration_ms: 5000, started_at: '2026-01-01', ended_at: '2026-01-01' };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findSessionById('s-1');
        expect(result).toHaveProperty('durationMs');
        expect(result).toHaveProperty('startedAt');
        expect(result).toHaveProperty('endedAt');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findSessionById('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- findTruthChecksByDraftId ---
  describe('findTruthChecksByDraftId', () => {
    describe('Reachability', () => {
      it('returns array of TruthChecks', async () => {
        const rows = [
          { id: 'tc-1', story_record_id: 'sr-1', claim: 'c1', verdict: 'VERIFIED', evidence: 'e1' },
        ];
        mockEq.mockResolvedValue({ data: rows, error: null });
        const result = await StoryDAO.findTruthChecksByDraftId('d-1');
        expect(result).toHaveLength(1);
        expect(mockFrom).toHaveBeenCalledWith('truth_checks');
      });
      it('returns empty array when none found', async () => {
        mockEq.mockResolvedValue({ data: [], error: null });
        const result = await StoryDAO.findTruthChecksByDraftId('d-1');
        expect(result).toHaveLength(0);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockEq.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findTruthChecksByDraftId('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- findDraftVersionsByDraftId ---
  describe('findDraftVersionsByDraftId', () => {
    describe('Reachability', () => {
      it('returns array of DraftVersions', async () => {
        const rows = [{ id: 'dv-1', story_record_id: 'sr-1', version_number: 1, content: 'v1' }];
        mockEq.mockResolvedValue({ data: rows, error: null });
        const result = await StoryDAO.findDraftVersionsByDraftId('d-1');
        expect(result).toHaveLength(1);
        expect(mockFrom).toHaveBeenCalledWith('draft_versions');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockEq.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findDraftVersionsByDraftId('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- findMetricsBySessionId ---
  describe('findMetricsBySessionId', () => {
    describe('Reachability', () => {
      it('returns StoryMetrics when found', async () => {
        const row = { id: 'sm-1', story_record_id: 'sr-1', word_count: 100, sentence_count: 5, readability_score: 0.8, voice_session_duration_ms: 5000 };
        mockMaybeSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.findMetricsBySessionId('s-1');
        expect(result).not.toBeNull();
        expect(mockFrom).toHaveBeenCalledWith('story_metrics');
      });
      it('returns null when not found', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: null });
        const result = await StoryDAO.findMetricsBySessionId('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        mockMaybeSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.findMetricsBySessionId('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- insertStoryRecord ---
  describe('insertStoryRecord', () => {
    describe('Reachability', () => {
      it('returns generated UUID', async () => {
        mockSingle.mockResolvedValue({ data: { id: 'sr-1' }, error: null });
        const record = { draftId: 'd-1', resumeId: 'r-1', jobId: 'j-1', questionId: 'q-1', voiceSessionId: 'vs-1', userId: 'u-1', status: 'DRAFT' as const, content: 'text' };
        const result = await StoryDAO.insertStoryRecord(record);
        expect(result).toBe('sr-1');
        expect(mockFrom).toHaveBeenCalledWith('story_records');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        const record = { draftId: 'd-1', resumeId: 'r-1', jobId: 'j-1', questionId: 'q-1', voiceSessionId: 'vs-1', userId: 'u-1', status: 'DRAFT' as const, content: 'text' };
        await expect(StoryDAO.insertStoryRecord(record)).rejects.toThrow(StoryError);
      });
    });
  });

  // --- insertTruthChecks ---
  describe('insertTruthChecks', () => {
    describe('Reachability', () => {
      it('inserts without error', async () => {
        mockInsert.mockResolvedValueOnce({ error: null });
        const checks = [{ claim: 'c1', verdict: 'VERIFIED' as const, evidence: 'e1' }];
        await expect(StoryDAO.insertTruthChecks(checks)).resolves.toBeUndefined();
        expect(mockFrom).toHaveBeenCalledWith('truth_checks');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on failure', async () => {
        mockInsert.mockResolvedValueOnce({ error: { message: 'fail' } });
        const checks = [{ claim: 'c1', verdict: 'VERIFIED' as const, evidence: 'e1' }];
        await expect(StoryDAO.insertTruthChecks(checks)).rejects.toThrow(StoryError);
      });
    });
  });

  // --- insertDraftVersions ---
  describe('insertDraftVersions', () => {
    describe('Reachability', () => {
      it('inserts without error', async () => {
        mockInsert.mockResolvedValueOnce({ error: null });
        const versions = [{ versionNumber: 1, content: 'v1' }];
        await expect(StoryDAO.insertDraftVersions(versions)).resolves.toBeUndefined();
        expect(mockFrom).toHaveBeenCalledWith('draft_versions');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on failure', async () => {
        mockInsert.mockResolvedValueOnce({ error: { message: 'fail' } });
        const versions = [{ versionNumber: 1, content: 'v1' }];
        await expect(StoryDAO.insertDraftVersions(versions)).rejects.toThrow(StoryError);
      });
    });
  });

  // --- insertMetrics ---
  describe('insertMetrics', () => {
    describe('Reachability', () => {
      it('inserts without error', async () => {
        mockInsert.mockResolvedValueOnce({ error: null });
        const metrics = { wordCount: 100, sentenceCount: 5, readabilityScore: 0.8, voiceSessionDurationMs: 5000 };
        await expect(StoryDAO.insertMetrics(metrics)).resolves.toBeUndefined();
        expect(mockFrom).toHaveBeenCalledWith('story_metrics');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on failure', async () => {
        mockInsert.mockResolvedValueOnce({ error: { message: 'fail' } });
        const metrics = { wordCount: 100, sentenceCount: 5, readabilityScore: 0.8, voiceSessionDurationMs: 5000 };
        await expect(StoryDAO.insertMetrics(metrics)).rejects.toThrow(StoryError);
      });
    });
  });

  // --- getClaimsBySetId ---
  describe('getClaimsBySetId', () => {
    const setupOrderChain = (resolveValue: unknown) => {
      const secondOrder = vi.fn().mockResolvedValue(resolveValue);
      mockOrder.mockReturnValue({ order: secondOrder });
    };

    describe('Reachability', () => {
      it('returns StoryClaim array', async () => {
        const rows = [{
          id: 'c-1', claim_set_id: 'cs-1', content: 'claim text', status: 'CONFIRMED',
          section: 'context', order: 0, created_at: '2026-01-01', updated_at: '2026-01-01',
        }];
        setupOrderChain({ data: rows, error: null });
        const result = await StoryDAO.getClaimsBySetId('cs-1');
        expect(result).not.toBeNull();
        expect(result!).toHaveLength(1);
        expect(mockFrom).toHaveBeenCalledWith('claims');
      });
      it('returns null when claim set not found', async () => {
        setupOrderChain({ data: null, error: null });
        const result = await StoryDAO.getClaimsBySetId('nonexistent');
        expect(result).toBeNull();
      });
    });
    describe('TypeInvariant', () => {
      it('each item conforms to StoryClaimSchema', async () => {
        const rows = [{
          id: '550e8400-e29b-41d4-a716-446655440099', claim_set_id: '550e8400-e29b-41d4-a716-446655440001',
          content: 'claim text', status: 'CONFIRMED',
          section: 'context', order: 0,
          created_at: '2026-01-01', updated_at: '2026-01-01',
        }];
        setupOrderChain({ data: rows, error: null });
        const result = await StoryDAO.getClaimsBySetId('cs-1');
        for (const item of result!) {
          expect(StoryClaimSchema.safeParse(item).success).toBe(true);
        }
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on DB failure', async () => {
        setupOrderChain({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.getClaimsBySetId('x')).rejects.toThrow(StoryError);
      });
    });
  });

  // --- saveDraft ---
  describe('saveDraft', () => {
    const draft = {
      id: '550e8400-e29b-41d4-a716-446655440099',
      claimSetId: '550e8400-e29b-41d4-a716-446655440001',
      sections: [],
      createdAt: '2026-01-01',
    };
    describe('Reachability', () => {
      it('inserts and returns StructuredDraft', async () => {
        const row = { id: draft.id, claim_set_id: draft.claimSetId, sections: [], created_at: draft.createdAt };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.saveDraft(draft);
        expect(result.id).toBe(draft.id);
        expect(mockFrom).toHaveBeenCalledWith('drafts');
      });
    });
    describe('TypeInvariant', () => {
      it('conforms to StructuredDraftSchema', async () => {
        const row = { id: draft.id, claim_set_id: draft.claimSetId, sections: [], created_at: draft.createdAt };
        mockSingle.mockResolvedValue({ data: row, error: null });
        const result = await StoryDAO.saveDraft(draft);
        expect(StructuredDraftSchema.safeParse(result).success).toBe(true);
      });
    });
    describe('ErrorConsistency', () => {
      it('throws StoryError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(StoryDAO.saveDraft(draft)).rejects.toThrow(StoryError);
      });
    });
  });
});
