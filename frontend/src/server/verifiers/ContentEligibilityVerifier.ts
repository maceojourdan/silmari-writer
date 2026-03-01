/**
 * ContentEligibilityVerifier - Validates that content is eligible for approval.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Ensures that content is in REVIEW status before allowing approval.
 * Throws ApprovalEligibilityError on validation failure.
 */

import type { ContentEntity } from '@/server/data_structures/ContentEntity';
import { ApprovalEligibilityError } from '@/server/error_definitions/ApprovalErrors';

export const ContentEligibilityVerifier = {
  /**
   * Assert that the content entity is in REVIEW status and eligible for approval.
   *
   * @throws ApprovalEligibilityError.CONTENT_NOT_ELIGIBLE if status !== REVIEW
   */
  assertApprovable(entity: ContentEntity): void {
    if (entity.status !== 'REVIEW') {
      throw ApprovalEligibilityError.CONTENT_NOT_ELIGIBLE(
        `Content '${entity.id}' is in '${entity.status}' status, expected 'REVIEW'`,
      );
    }
  },
} as const;
