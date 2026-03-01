/**
 * ApproveContentService - Orchestrates content approval and workflow advancement.
 *
 * Resource: db-h2s4 (service)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Validates that the content exists and is in REVIEW state,
 * updates status to APPROVED, advances workflow to FINALIZE,
 * and triggers the workflow chain.
 *
 * Throws errors from ApprovalErrors on failure.
 */

import { ContentDAO } from '@/server/data_access_objects/ContentDAO';
import { ContentEligibilityVerifier } from '@/server/verifiers/ContentEligibilityVerifier';
import { ApprovalWorkflowChain } from '@/server/process_chains/ApprovalWorkflowChain';
import { ApprovalEligibilityError } from '@/server/error_definitions/ApprovalErrors';
import type { ContentEntity } from '@/server/data_structures/ContentEntity';

export interface ApproveContentResult {
  entity: ContentEntity;
  workflowStage: string;
}

export const ApproveContentService = {
  /**
   * Approve content for transition from REVIEW to APPROVED.
   *
   * 1. Load content via DAO
   * 2. Validate eligibility (must be in REVIEW state)
   * 3. Persist status update to APPROVED + workflowStage to FINALIZE
   * 4. Trigger workflow chain for progression
   * 5. Return updated entity + workflow stage
   *
   * Throws CONTENT_NOT_FOUND if content doesn't exist.
   * Throws CONTENT_NOT_ELIGIBLE if content is not in REVIEW state.
   */
  async approveContent(contentId: string): Promise<ApproveContentResult> {
    // Step 1: Retrieve content entity
    const content = await ContentDAO.findById(contentId);

    if (!content) {
      throw ApprovalEligibilityError.CONTENT_NOT_FOUND(
        `Content '${contentId}' not found`,
      );
    }

    // Step 2: Validate eligibility
    ContentEligibilityVerifier.assertApprovable(content);

    // Step 3: Persist approved status and advanced workflow stage
    const updatedEntity = await ContentDAO.update(contentId, 'APPROVED', 'FINALIZE');

    // Step 4: Trigger workflow chain
    const workflowResult = await ApprovalWorkflowChain.trigger(updatedEntity);

    // Step 5: Return result
    return {
      entity: updatedEntity,
      workflowStage: workflowResult.nextStage,
    };
  },
} as const;
