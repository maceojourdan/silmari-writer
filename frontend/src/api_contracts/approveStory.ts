/**
 * approveStory - Typed API contract for the approve-story endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

import { z } from 'zod';

/**
 * Request payload (mirrors ApproveDraftPayload from verifier).
 */
export interface ApproveStoryRequest {
  draftId: string;
  resumeId: string;
  jobId: string;
  questionId: string;
  voiceSessionId: string;
}

/**
 * Response schema for successful story approval.
 */
export const ApproveStoryResponseSchema = z.object({
  storyRecordId: z.string().min(1),
  status: z.enum(['DRAFT', 'APPROVED', 'FINALIZED']),
  persistedAt: z.string(),
});

export type ApproveStoryResponse = z.infer<typeof ApproveStoryResponseSchema>;

/**
 * Typed function that sends the approval request.
 */
export async function approveStory(
  payload: ApproveStoryRequest,
): Promise<ApproveStoryResponse> {
  const response = await fetch('/api/approve-story', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Approve story failed with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = ApproveStoryResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from approve-story: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
