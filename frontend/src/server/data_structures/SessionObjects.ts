/**
 * SessionObjects - TypeScript interfaces and Zod schemas for session
 * initialization objects: Resume, Job, Question, and Session.
 *
 * Resource: cfg-d2q3 (common_structure)
 * Path: 294-parse-and-store-session-input-objects
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Zod Schemas
// ---------------------------------------------------------------------------

export const ResumeObjectSchema = z.object({
  id: z.string().uuid().optional(),
  content: z.string().min(1, 'Resume content is required'),
  name: z.string().min(1, 'Resume name is required'),
  wordCount: z.number().int().nonnegative(),
  createdAt: z.string().optional(),
});

export const JobObjectSchema = z.object({
  id: z.string().uuid().optional(),
  title: z.string().min(1, 'Job title is required'),
  description: z.string().min(1, 'Job description is required'),
  sourceType: z.enum(['link', 'text']),
  sourceValue: z.string().min(1, 'Job source value is required'),
  createdAt: z.string().optional(),
});

export const QuestionObjectSchema = z.object({
  id: z.string().uuid().optional(),
  text: z.string().min(1, 'Question text is required'),
  category: z.string().optional(),
  createdAt: z.string().optional(),
});

export const SessionObjectSchema = z.object({
  id: z.string().uuid().optional(),
  resumeId: z.string().uuid(),
  jobId: z.string().uuid(),
  questionId: z.string().uuid(),
  status: z.enum(['INITIALIZED', 'ACTIVE', 'COMPLETED', 'FAILED']),
  createdAt: z.string().optional(),
  updatedAt: z.string().optional(),
});

// ---------------------------------------------------------------------------
// TypeScript Types (inferred from Zod schemas)
// ---------------------------------------------------------------------------

export type ResumeObject = z.infer<typeof ResumeObjectSchema>;
export type JobObject = z.infer<typeof JobObjectSchema>;
export type QuestionObject = z.infer<typeof QuestionObjectSchema>;
export type SessionObject = z.infer<typeof SessionObjectSchema>;

export type SessionStatus = 'INITIALIZED' | 'ACTIVE' | 'COMPLETED' | 'FAILED';

// ---------------------------------------------------------------------------
// Aggregated types for processor → service handoff
// ---------------------------------------------------------------------------

/**
 * ParsedSessionInput — validated objects from the processor,
 * ready for persistence via SessionInitService.
 */
export interface ParsedSessionInput {
  resume: ResumeObject;
  job: JobObject;
  question: QuestionObject;
}

/**
 * SessionInitResult — returned after successful session initialization.
 */
export interface SessionInitResult {
  sessionId: string;
  resumeId: string;
  jobId: string;
  questionId: string;
}
