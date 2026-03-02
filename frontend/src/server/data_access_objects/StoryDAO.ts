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
import { supabase } from '@/lib/supabase';
import { StoryErrors, StoryError } from '@/server/error_definitions/StoryErrors';

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
    try {
      const { data, error } = await supabase
        .from('drafts')
        .select('*')
        .eq('id', draftId)
        .maybeSingle();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find draft: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        content: data.content,
        resumeId: data.resume_id,
        jobId: data.job_id,
        questionId: data.question_id,
        voiceSessionId: data.voice_session_id,
      };
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findResumeById(resumeId: string): Promise<ResumeData | null> {
    try {
      const { data, error } = await supabase
        .from('resumes')
        .select('*')
        .eq('id', resumeId)
        .maybeSingle();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find resume: ${error.message}`);
      if (!data) return null;

      return { id: data.id, name: data.name, content: data.content };
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findJobById(jobId: string): Promise<JobData | null> {
    try {
      const { data, error } = await supabase
        .from('jobs')
        .select('*')
        .eq('id', jobId)
        .maybeSingle();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find job: ${error.message}`);
      if (!data) return null;

      return { id: data.id, title: data.title, description: data.description };
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findQuestionById(questionId: string): Promise<QuestionData | null> {
    try {
      const { data, error } = await supabase
        .from('questions')
        .select('*')
        .eq('id', questionId)
        .maybeSingle();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find question: ${error.message}`);
      if (!data) return null;

      return { id: data.id, text: data.text };
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findSessionById(sessionId: string): Promise<SessionData | null> {
    try {
      const { data, error } = await supabase
        .from('sessions')
        .select('*')
        .eq('id', sessionId)
        .maybeSingle();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find session: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        durationMs: data.duration_ms,
        startedAt: data.started_at,
        endedAt: data.ended_at,
      };
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findTruthChecksByDraftId(draftId: string): Promise<TruthCheck[]> {
    try {
      const { data, error } = await supabase
        .from('truth_checks')
        .select('*')
        .eq('draft_id', draftId);

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find truth checks: ${error.message}`);
      return data ?? [];
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findDraftVersionsByDraftId(draftId: string): Promise<DraftVersion[]> {
    try {
      const { data, error } = await supabase
        .from('draft_versions')
        .select('*')
        .eq('draft_id', draftId);

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find draft versions: ${error.message}`);
      return data ?? [];
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findMetricsBySessionId(sessionId: string): Promise<StoryMetrics | null> {
    try {
      const { data, error } = await supabase
        .from('story_metrics')
        .select('*')
        .eq('session_id', sessionId)
        .maybeSingle();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to find metrics: ${error.message}`);
      return data ?? null;
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async insertStoryRecord(record: StoryRecord): Promise<string> {
    try {
      const { data, error } = await supabase
        .from('story_records')
        .insert({
          draft_id: record.draftId,
          resume_id: record.resumeId,
          job_id: record.jobId,
          question_id: record.questionId,
          voice_session_id: record.voiceSessionId,
          user_id: record.userId,
          status: record.status,
          content: record.content,
        })
        .select('id')
        .single();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to insert story record: ${error.message}`);
      if (!data) throw StoryErrors.PERSISTENCE_FAILED('No data returned from insert');

      return data.id;
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async insertTruthChecks(checks: TruthCheck[]): Promise<void> {
    try {
      const { error } = await supabase
        .from('truth_checks')
        .insert(checks);

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to insert truth checks: ${error.message}`);
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async insertDraftVersions(versions: DraftVersion[]): Promise<void> {
    try {
      const { error } = await supabase
        .from('draft_versions')
        .insert(versions);

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to insert draft versions: ${error.message}`);
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async insertMetrics(metrics: StoryMetrics): Promise<void> {
    try {
      const { error } = await supabase
        .from('story_metrics')
        .insert(metrics);

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to insert metrics: ${error.message}`);
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  // -------------------------------------------------------------------------
  // Path 325: generate-draft-from-confirmed-claims
  // -------------------------------------------------------------------------

  async getClaimsBySetId(claimSetId: string): Promise<StoryClaim[] | null> {
    try {
      const { data, error } = await supabase
        .from('claims')
        .select('*')
        .eq('claim_set_id', claimSetId)
        .order('section', { ascending: true })
        .order('order', { ascending: true });

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to get claims: ${error.message}`);
      if (!data) return null;

      return data.map((row: Record<string, unknown>) => ({
        id: row.id as string,
        claimSetId: row.claim_set_id as string,
        content: row.content as string,
        status: row.status as string,
        section: row.section as string,
        order: row.order as number,
        createdAt: row.created_at as string,
        updatedAt: row.updated_at as string,
      })) as StoryClaim[];
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },

  async saveDraft(draft: StructuredDraft): Promise<StructuredDraft> {
    try {
      const { data, error } = await supabase
        .from('drafts')
        .insert({
          id: draft.id,
          claim_set_id: draft.claimSetId,
          sections: draft.sections,
          created_at: draft.createdAt,
        })
        .select()
        .single();

      if (error) throw StoryErrors.PERSISTENCE_FAILED(`Failed to save draft: ${error.message}`);
      if (!data) throw StoryErrors.PERSISTENCE_FAILED('No data returned from insert');

      return {
        id: data.id,
        claimSetId: data.claim_set_id,
        sections: data.sections,
        createdAt: data.created_at,
      };
    } catch (err) {
      if (err instanceof StoryError) throw err;
      throw StoryErrors.PERSISTENCE_FAILED(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
