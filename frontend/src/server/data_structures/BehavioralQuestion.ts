/**
 * BehavioralQuestion - TypeScript interfaces and Zod schemas for behavioral
 * question entities, including the draft state and status transitions.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 */

import { z } from 'zod';

export type BehavioralQuestionStatus = 'DRAFT' | 'VERIFY';

/**
 * Zod schema for a BehavioralQuestion entity.
 * Enforces minimum slot requirements at the schema level:
 * - objective: non-empty string
 * - actions: array of at least 3 non-empty strings
 * - obstacles: array of at least 1 non-empty string
 * - outcome: non-empty string
 * - roleClarity: non-empty string
 */
export const BehavioralQuestionSchema = z.object({
  id: z.string().min(1).optional(),
  sessionId: z.string().min(1),
  objective: z.string().min(1, 'Objective is required'),
  actions: z.array(z.string().min(1)).min(3, 'At least 3 actions are required'),
  obstacles: z.array(z.string().min(1)).min(1, 'At least 1 obstacle is required'),
  outcome: z.string().min(1, 'Outcome is required'),
  roleClarity: z.string().min(1, 'Role clarity is required'),
  status: z.enum(['DRAFT', 'VERIFY']).default('DRAFT'),
  createdAt: z.string().optional(),
  updatedAt: z.string().optional(),
});

export type BehavioralQuestion = z.infer<typeof BehavioralQuestionSchema>;

/**
 * BehavioralQuestionDraft - The frontend draft state before submission.
 * Fields may be empty/partial until user completes them.
 */
export interface BehavioralQuestionDraft {
  objective: string;
  actions: string[];
  obstacles: string[];
  outcome: string;
  roleClarity: string;
}

/**
 * EvaluateCommand - Validated command sent from request handler to service.
 */
export interface EvaluateCommand {
  sessionId: string;
  objective: string;
  actions: string[];
  obstacles: string[];
  outcome: string;
  roleClarity: string;
}

/**
 * EvaluateResult - Result from the backend evaluation.
 */
export interface EvaluateResult {
  eligible: boolean;
  questionId: string;
  status: BehavioralQuestionStatus;
  updatedAt: string;
}
