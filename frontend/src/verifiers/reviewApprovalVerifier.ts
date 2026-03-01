/**
 * reviewApprovalVerifier - Validates client-side selection before approval.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Ensures that a content item is selected before allowing the approval
 * action. Returns a typed validation result.
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Validation Schema
// ---------------------------------------------------------------------------

export const ReviewApprovalPayloadSchema = z.object({
  contentId: z.string().min(1, 'contentId is required'),
});

export type ReviewApprovalPayload = z.infer<typeof ReviewApprovalPayloadSchema>;

// ---------------------------------------------------------------------------
// Validation Result Types
// ---------------------------------------------------------------------------

type ValidationSuccess = { success: true; data: ReviewApprovalPayload };
type ValidationFailure = { success: false; errors: string[] };
export type ValidationResult = ValidationSuccess | ValidationFailure;

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

export const reviewApprovalVerifier = {
  /**
   * Validate that a content ID is provided and non-empty.
   * Returns typed success/failure result.
   */
  validateSelection(contentId?: string): ValidationResult {
    const result = ReviewApprovalPayloadSchema.safeParse({ contentId });

    if (result.success) {
      return { success: true, data: result.data };
    }

    const errors = result.error.issues.map(
      (issue) => `${issue.path.join('.')}: ${issue.message}`,
    );
    return { success: false, errors };
  },
} as const;
