/**
 * ApprovalWorkflowChain - Handles ordered workflow progression after approval.
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Triggers workflow advancement from REVIEW to FINALIZE stage
 * after content approval is validated.
 */

import type { ContentEntity } from '@/server/data_structures/ContentEntity';
import { ApprovalEligibilityError } from '@/server/error_definitions/ApprovalErrors';

export interface WorkflowTriggerResult {
  contentId: string;
  previousStage: string;
  nextStage: string;
  triggered: boolean;
}

export const ApprovalWorkflowChain = {
  /**
   * Trigger workflow progression for approved content.
   *
   * Validates entity is in APPROVED status, then signals
   * the workflow to advance to FINALIZE stage.
   *
   * @throws ApprovalEligibilityError.CONTENT_NOT_ELIGIBLE if not APPROVED
   */
  async trigger(entity: ContentEntity): Promise<WorkflowTriggerResult> {
    if (entity.status !== 'APPROVED') {
      throw ApprovalEligibilityError.CONTENT_NOT_ELIGIBLE(
        `Cannot trigger workflow for content '${entity.id}' in '${entity.status}' status`,
      );
    }

    return {
      contentId: entity.id,
      previousStage: 'REVIEW',
      nextStage: 'FINALIZE',
      triggered: true,
    };
  },
} as const;
