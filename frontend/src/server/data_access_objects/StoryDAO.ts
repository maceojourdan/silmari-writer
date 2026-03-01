/**
 * StoryDAO - Encapsulates database query operations for story-related entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Paths:
 *   - 293-approve-voice-session-and-persist-story-record
 *   - 325-generate-draft-from-confirmed-claims
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type {
  StoryRecord,
  TruthCheck,
  DraftVersion,
  StoryMetrics,
} from '@/server/data_structures/StoryRecord';
import type { StoryClaim, StructuredDraft } from '@/server/data_structures/StoryStructures';

export interface DraftData {
  id: string;
  content: string;
  resumeId: string;
  jobId: string;
  questionId: string;
  voiceSessionId: string;
}

export interface ResumeData {
  id: string;
  name: string;
  content: string;
}

export interface JobData {
  id: string;
  title: string;
  description: string;
}

export interface QuestionData {
  id: string;
  text: string;
}

export interface SessionData {
  id: string;
  durationMs: number;
  startedAt: string;
  endedAt: string;
}

export const StoryDAO = {
  async findDraftById(draftId: string): Promise<DraftData | null> {
    // Supabase: supabase.from('drafts').select('*').eq('id', draftId).single()
    throw new Error('StoryDAO.findDraftById not yet wired to Supabase');
  },

  async findResumeById(resumeId: string): Promise<ResumeData | null> {
    throw new Error('StoryDAO.findResumeById not yet wired to Supabase');
  },

  async findJobById(jobId: string): Promise<JobData | null> {
    throw new Error('StoryDAO.findJobById not yet wired to Supabase');
  },

  async findQuestionById(questionId: string): Promise<QuestionData | null> {
    throw new Error('StoryDAO.findQuestionById not yet wired to Supabase');
  },

  async findSessionById(sessionId: string): Promise<SessionData | null> {
    throw new Error('StoryDAO.findSessionById not yet wired to Supabase');
  },

  async findTruthChecksByDraftId(draftId: string): Promise<TruthCheck[]> {
    throw new Error('StoryDAO.findTruthChecksByDraftId not yet wired to Supabase');
  },

  async findDraftVersionsByDraftId(draftId: string): Promise<DraftVersion[]> {
    throw new Error('StoryDAO.findDraftVersionsByDraftId not yet wired to Supabase');
  },

  async findMetricsBySessionId(sessionId: string): Promise<StoryMetrics | null> {
    throw new Error('StoryDAO.findMetricsBySessionId not yet wired to Supabase');
  },

  async insertStoryRecord(record: StoryRecord): Promise<string> {
    throw new Error('StoryDAO.insertStoryRecord not yet wired to Supabase');
  },

  async insertTruthChecks(checks: TruthCheck[]): Promise<void> {
    throw new Error('StoryDAO.insertTruthChecks not yet wired to Supabase');
  },

  async insertDraftVersions(versions: DraftVersion[]): Promise<void> {
    throw new Error('StoryDAO.insertDraftVersions not yet wired to Supabase');
  },

  async insertMetrics(metrics: StoryMetrics): Promise<void> {
    throw new Error('StoryDAO.insertMetrics not yet wired to Supabase');
  },

  // -------------------------------------------------------------------------
  // Path 325: generate-draft-from-confirmed-claims
  // -------------------------------------------------------------------------

  /**
   * Get all claims belonging to a claim set.
   * Returns null if claim set does not exist.
   *
   * Step 3: Retrieve confirmed claims
   */
  async getClaimsBySetId(_claimSetId: string): Promise<StoryClaim[] | null> {
    // Supabase: supabase.from('claims')
    //   .select('*')
    //   .eq('claimSetId', claimSetId)
    //   .order('section', { ascending: true })
    //   .order('order', { ascending: true })
    throw new Error('StoryDAO.getClaimsBySetId not yet wired to Supabase');
  },

  /**
   * Persist a structured draft to the database.
   * Returns the saved draft with server-generated fields.
   *
   * Step 5: Persist and return generated draft
   */
  async saveDraft(_draft: StructuredDraft): Promise<StructuredDraft> {
    // Supabase: supabase.from('drafts')
    //   .insert({
    //     id: draft.id,
    //     claimSetId: draft.claimSetId,
    //     sections: draft.sections,
    //     createdAt: draft.createdAt,
    //   })
    //   .select()
    //   .single()
    throw new Error('StoryDAO.saveDraft not yet wired to Supabase');
  },
} as const;
