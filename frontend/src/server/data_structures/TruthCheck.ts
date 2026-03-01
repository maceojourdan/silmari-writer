/**
 * TruthCheck - TypeScript interfaces and Zod schemas for truth check
 * entities, including confirmed/denied status.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 297-confirm-metric-claim-truth-check
 * Maps to: truth_checks table
 */

import { z } from 'zod';

export type TruthCheckStatus = 'confirmed' | 'denied';

/**
 * Zod schema for a TruthCheck entity.
 */
export const TruthCheckSchema = z.object({
  id: z.string().min(1),
  claim_id: z.string().min(1),
  status: z.enum(['confirmed', 'denied']),
  source: z.string().min(1),
  created_at: z.string(),
});

export type TruthCheck = z.infer<typeof TruthCheckSchema>;

/**
 * ConfirmCommand - Validated command sent from request handler to service.
 */
export interface ConfirmCommand {
  claim_id: string;
  status: TruthCheckStatus;
  source: string;
}

/**
 * ConfirmResult - Result from the backend confirmation.
 */
export interface ConfirmResult {
  id: string;
  claim_id: string;
  status: TruthCheckStatus;
  source: string;
  created_at: string;
}
