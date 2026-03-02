/**
 * exportFinalizedAnswer - Typed API contract for the export finalized answer endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 334-export-or-copy-finalized-answer
 */

import { z } from 'zod';
import { ExportFormatSchema } from '@/server/data_structures/ExportFormat';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const ExportFinalizedAnswerRequestSchema = z.object({
  answerId: z.string().min(1),
  format: ExportFormatSchema,
});

export type ExportFinalizedAnswerRequest = z.infer<typeof ExportFinalizedAnswerRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const ExportFinalizedAnswerResponseSchema = z.object({
  content: z.string(),
  format: ExportFormatSchema,
  answerId: z.string().min(1),
});

export type ExportFinalizedAnswerResponse = z.infer<typeof ExportFinalizedAnswerResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the export finalized answer request.
 * Validates response via Zod schema on receipt.
 */
export async function exportFinalizedAnswer(
  payload: ExportFinalizedAnswerRequest,
): Promise<ExportFinalizedAnswerResponse> {
  const response = await fetch(`/api/answers/${payload.answerId}/export?format=${payload.format}`, {
    method: 'GET',
    headers: { 'Content-Type': 'application/json' },
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Export answer failed with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = ExportFinalizedAnswerResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from export answer: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
