/**
 * ApproveContentHandler - Orchestrates content approval flow:
 * service (validate + update + workflow chain) → response.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Known errors (ApprovalError) are rethrown as-is.
 * Unknown errors are logged and wrapped in GenericErrors.InternalError.
 */

import { ApproveContentService } from '@/server/services/ApproveContentService';
import type { ApproveContentResult } from '@/server/services/ApproveContentService';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export const ApproveContentHandler = {
  /**
   * Handle the full content approval flow:
   * 1. Delegate to service (validate + update + workflow chain)
   * 2. Return updated entity + workflow stage
   */
  async handle(contentId: string): Promise<ApproveContentResult> {
    try {
      // Delegate to service which handles:
      // - DAO lookup
      // - Eligibility verification
      // - Status + workflow stage update
      // - Workflow chain trigger
      return await ApproveContentService.approveContent(contentId);
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof ApprovalError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during content approval',
        error,
        { path: '329-approve-reviewed-content-and-advance-workflow', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during content approval: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
