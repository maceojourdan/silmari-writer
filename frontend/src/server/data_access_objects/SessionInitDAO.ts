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

export const SessionInitDAO = {
  /**
   * Insert a resume record and return its generated UUID.
   */
  async insertResume(resume: ResumeObject): Promise<string> {
    // Supabase: supabase.from('resumes').insert(resume).select('id').single()
    throw new Error('SessionInitDAO.insertResume not yet wired to Supabase');
  },

  /**
   * Insert a job record and return its generated UUID.
   */
  async insertJob(job: JobObject): Promise<string> {
    // Supabase: supabase.from('jobs').insert(job).select('id').single()
    throw new Error('SessionInitDAO.insertJob not yet wired to Supabase');
  },

  /**
   * Insert a question record and return its generated UUID.
   */
  async insertQuestion(question: QuestionObject): Promise<string> {
    // Supabase: supabase.from('questions').insert(question).select('id').single()
    throw new Error('SessionInitDAO.insertQuestion not yet wired to Supabase');
  },

  /**
   * Insert a session record linking resume, job, and question, and return its generated UUID.
   */
  async insertSession(session: Omit<SessionObject, 'id'>): Promise<string> {
    // Supabase: supabase.from('sessions').insert(session).select('id').single()
    throw new Error('SessionInitDAO.insertSession not yet wired to Supabase');
  },
} as const;
