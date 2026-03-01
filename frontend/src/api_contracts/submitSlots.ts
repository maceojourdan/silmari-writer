/**
 * submitSlots - Typed API contract for the slot submission endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 320-re-prompt-unfilled-required-slots
 *
 * Sends a POST request with slot values for the current session's
 * missing required slots. Returns the updated prompt state with
 * remaining missing slots and optional guidance hint.
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const SubmitSlotsRequestSchema = z.object({
  sessionId: z.string().uuid('sessionId must be a valid UUID'),
  questionType: z.string().min(1, 'questionType must be non-empty'),
  slotValues: z.record(z.string(), z.string()),
  attemptCount: z.number().int().min(0, 'attemptCount must be non-negative'),
});

export type SubmitSlotsRequest = z.infer<typeof SubmitSlotsRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const SlotPromptSchema = z.object({
  name: z.string().min(1),
  promptLabel: z.string().min(1),
});

export type SlotPrompt = z.infer<typeof SlotPromptSchema>;

export const SubmitSlotsResponseSchema = z.object({
  prompts: z.array(SlotPromptSchema),
  attemptCount: z.number().int().min(0),
  guidanceHint: z.boolean(),
});

export type SubmitSlotsResponse = z.infer<typeof SubmitSlotsResponseSchema>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Submit slot values for validation and re-prompt generation.
 *
 * @param payload - SubmitSlotsRequest with sessionId, questionType, slotValues, attemptCount
 * @returns SubmitSlotsResponse with remaining prompts and guidance hint flag
 */
export async function submitSlots(
  payload: SubmitSlotsRequest,
): Promise<SubmitSlotsResponse> {
  const response = await fetch('/api/session/submit-slots', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Slot submission failed with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = SubmitSlotsResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from session/submit-slots: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
