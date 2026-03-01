/**
 * InitializedSession - Data structures for Path 310:
 * initialize-new-session-with-provided-objects.
 *
 * Unlike Path 294 (which stores objects separately and links by ID),
 * Path 310 embeds ResumeObject, JobObject, and QuestionObject directly
 * within the session entity, with state "initialized".
 *
 * Resource: cfg-d2q3 (common_structure)
 * Path: 310-initialize-new-session-with-provided-objects
 */

import { z } from 'zod';
import {
  ResumeObjectSchema,
  JobObjectSchema,
  QuestionObjectSchema,
} from '@/server/data_structures/SessionObjects';

// ---------------------------------------------------------------------------
// Request Schema — structured objects provided by the client
// ---------------------------------------------------------------------------

export const InitializeSessionRequestSchema = z.object({
  resume: ResumeObjectSchema,
  job: JobObjectSchema,
  question: QuestionObjectSchema,
});

export type InitializeSessionRequest = z.infer<typeof InitializeSessionRequestSchema>;

// ---------------------------------------------------------------------------
// InitializedSession — session entity with embedded objects
// ---------------------------------------------------------------------------

export const InitializedSessionSchema = z.object({
  id: z.string().uuid(),
  resume: ResumeObjectSchema,
  job: JobObjectSchema,
  question: QuestionObjectSchema,
  state: z.literal('initialized'),
  createdAt: z.string(),
});

export type InitializedSession = z.infer<typeof InitializedSessionSchema>;

// ---------------------------------------------------------------------------
// Response Schema — returned to the client
// ---------------------------------------------------------------------------

export const InitializeSessionResponseSchema = z.object({
  id: z.string().uuid(),
  resume: ResumeObjectSchema,
  job: JobObjectSchema,
  question: QuestionObjectSchema,
  state: z.literal('initialized'),
});

export type InitializeSessionResponse = z.infer<typeof InitializeSessionResponseSchema>;
