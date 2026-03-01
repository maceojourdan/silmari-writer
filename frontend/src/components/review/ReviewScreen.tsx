'use client';

/**
 * ReviewScreen - Captures user Approve action for reviewed content.
 *
 * Resource: ui-w8p2 (component)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * On click:
 *   1. Run reviewApprovalVerifier.validateSelection(contentId)
 *   2. If valid → call approveContent API contract
 *   3. If invalid → set local validation error state
 */

import { useState } from 'react';
import { reviewApprovalVerifier } from '@/verifiers/reviewApprovalVerifier';
import { approveContent } from '@/api_contracts/approveContent';
import type { ApproveContentResponse } from '@/api_contracts/approveContent';

export interface ReviewScreenProps {
  selectedContentId?: string;
  onApproved?: (response: ApproveContentResponse) => void;
  onError?: (error: Error) => void;
}

export default function ReviewScreen({
  selectedContentId,
  onApproved,
  onError,
}: ReviewScreenProps) {
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isApproved, setIsApproved] = useState(false);

  const handleApprove = async () => {
    setError(null);

    // Step 1: Validate selection via verifier
    const validation = reviewApprovalVerifier.validateSelection(selectedContentId);

    if (!validation.success) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 2: Call API contract
    setIsSubmitting(true);
    try {
      const result = await approveContent(validation.data.contentId);
      setIsApproved(true);
      onApproved?.(result);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
      onError?.(err instanceof Error ? err : new Error(message));
    } finally {
      setIsSubmitting(false);
    }
  };

  if (isApproved) {
    return (
      <div className="flex items-center gap-2 text-green-600" data-testid="approve-success">
        <span>Content approved successfully.</span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2" data-testid="review-screen">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        onClick={handleApprove}
        disabled={isSubmitting}
        aria-label={isSubmitting ? 'Approving...' : 'Approve'}
      >
        {isSubmitting ? 'Approving...' : 'Approve'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
