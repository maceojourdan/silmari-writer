/**
 * approveContent - Typed API contract for the content approval endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const ApproveContentRequestSchema = z.object({
  contentId: z.string().min(1, 'contentId is required'),
});

export type ApproveContentRequest = z.infer<typeof ApproveContentRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const ApproveContentResponseSchema = z.object({
  entity: z.object({
    id: z.string(),
    status: z.literal('APPROVED'),
    workflowStage: z.string(),
    createdAt: z.string(),
    updatedAt: z.string(),
  }),
  workflowStage: z.string(),
});

export type ApproveContentResponse = z.infer<typeof ApproveContentResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the content approval request.
 * Validates response via Zod schema.
 * Logs errors via frontendLogger on failure.
 */
export async function approveContent(
  contentId: string,
): Promise<ApproveContentResponse> {
  try {
    const response = await fetch('/api/review/approve', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ contentId }),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      const error = new Error(
        errorBody.message || `Content approval failed with status ${response.status}`,
      );
      (error as any).code = errorBody.code;
      throw error;
    }

    const data = await response.json();
    const parsed = ApproveContentResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from content approval: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Content approval request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'approveContent', module: 'api_contracts' },
    );
    throw error;
  }
}
