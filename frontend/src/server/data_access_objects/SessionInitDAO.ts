/**
 * SessionInitDAO - Handles database persistence of session initialization objects.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 294-parse-and-store-session-input-objects
 *
 * In production, each method performs Supabase queries against
 * resumes, jobs, questions, and sessions tables.
 * For TDD, methods are designed to be mockable.
 */

import type {
  ResumeObject,
  JobObject,
  QuestionObject,
  SessionObject,
} from '@/server/data_structures/SessionObjects';
import { supabase } from '@/lib/supabase';
import { SessionErrors, SessionError } from '@/server/error_definitions/SessionErrors';

export const SessionInitDAO = {
  /**
   * Insert a resume record and return its generated UUID.
   */
  async insertResume(resume: ResumeObject): Promise<string> {
    try {
      const { data, error } = await supabase
        .from('resumes')
        .insert({
          content: resume.content,
          name: resume.name,
          word_count: resume.wordCount,
        })
        .select('id')
        .single();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to insert resume: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.PersistenceFailure('No data returned from resume insert');
      }
      return data.id;
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Insert a job record and return its generated UUID.
   */
  async insertJob(job: JobObject): Promise<string> {
    try {
      const { data, error } = await supabase
        .from('jobs')
        .insert({
          title: job.title,
          description: job.description,
          source_type: job.sourceType,
          source_value: job.sourceValue,
        })
        .select('id')
        .single();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to insert job: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.PersistenceFailure('No data returned from job insert');
      }
      return data.id;
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Insert a question record and return its generated UUID.
   */
  async insertQuestion(question: QuestionObject): Promise<string> {
    try {
      const { data, error } = await supabase
        .from('questions')
        .insert({
          text: question.text,
        })
        .select('id')
        .single();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to insert question: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.PersistenceFailure('No data returned from question insert');
      }
      return data.id;
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },

  /**
   * Insert a session record linking resume, job, and question, and return its generated UUID.
   */
  async insertSession(session: Omit<SessionObject, 'id'>): Promise<string> {
    try {
      const { data, error } = await supabase
        .from('sessions')
        .insert({
          resume_id: session.resumeId,
          job_id: session.jobId,
          question_id: session.questionId,
          status: session.status,
        })
        .select('id')
        .single();

      if (error) {
        throw SessionErrors.PersistenceFailure(`Failed to insert session: ${error.message}`);
      }
      if (!data) {
        throw SessionErrors.PersistenceFailure('No data returned from session insert');
      }
      return data.id;
    } catch (err) {
      if (err instanceof SessionError) throw err;
      throw SessionErrors.PersistenceFailure(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
