/**
 * CompleteOnboardingStep - Typed API contract for the onboarding step
 * completion endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Custom Error
// ---------------------------------------------------------------------------

export class CompleteOnboardingStepApiError extends Error {
  code: string;

  constructor(code: string, message: string) {
    super(message);
    this.name = 'CompleteOnboardingStepApiError';
    this.code = code;
  }
}

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const CompleteOnboardingStepRequestSchema = z.object({
  userId: z.string().min(1),
  step: z.number().int().min(1),
  metadata: z.record(z.string(), z.any()).optional(),
});

export type CompleteOnboardingStepRequest = z.infer<
  typeof CompleteOnboardingStepRequestSchema
>;

// ---------------------------------------------------------------------------
// Response Schema
// ---------------------------------------------------------------------------

export const CompleteOnboardingStepResponseSchema = z.object({
  status: z.literal('completed'),
  onboardingId: z.string().min(1),
  step: z.number().int().min(1),
  analyticsRecorded: z.boolean(),
});

export type CompleteOnboardingStepResponse = z.infer<
  typeof CompleteOnboardingStepResponseSchema
>;

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the onboarding step completion request.
 * Validates response via Zod schema on receipt.
 */
export async function completeOnboardingStep(
  payload: CompleteOnboardingStepRequest,
): Promise<CompleteOnboardingStepResponse> {
  const response = await fetch('/api/onboarding/complete', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new CompleteOnboardingStepApiError(
      errorBody.code || 'UNKNOWN_ERROR',
      errorBody.message ||
        `Complete onboarding step failed with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = CompleteOnboardingStepResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from complete onboarding step: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
