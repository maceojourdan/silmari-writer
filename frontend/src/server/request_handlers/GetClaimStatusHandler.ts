/**
 * GetClaimStatusHandler - Bridges the claim status endpoint
 * to the data access layer for Path 324.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * Known errors (DomainError) are rethrown as-is.
 * Unknown errors are logged and wrapped in DomainErrors.CLAIM_STATUS_LOAD_ERROR.
 */

import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { DraftingWorkflowDAO } from '@/server/data_access_objects/DraftingWorkflowDAO';
import {
  DomainError,
  DomainErrors,
} from '@/server/error_definitions/DomainErrors';
import { logger } from '@/server/logging/logger';
import type { ClaimStatusResponse } from '@/server/data_structures/DraftingWorkflow';

const PATH = '324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold';
const RESOURCE = 'api-n8k2';

export const GetClaimStatusHandler = {
  /**
   * Handle a GET claim status request by loading claim and drafting data.
   *
   * @param claimId - The claim ID to retrieve status for.
   * @returns ClaimStatusResponse with claim and drafting statuses.
   * @throws DomainError for known errors (rethrown)
   * @throws DomainError CLAIM_STATUS_LOAD_ERROR for unexpected errors
   */
  async handle(claimId: string): Promise<ClaimStatusResponse> {
    try {
      const claim = await ClaimDAO.findById(claimId);
      if (!claim) {
        throw DomainErrors.DOMAIN_INTEGRITY_ERROR(
          `Claim ${claimId} not found`,
        );
      }

      const drafting = await DraftingWorkflowDAO.findByClaimId(claimId);

      const response: ClaimStatusResponse = {
        claimStatus: claim.status,
        draftingStatus: drafting?.status ?? 'Unknown',
        timedOut: claim.status === 'UNVERIFIED' && drafting?.status === 'On Hold',
      };

      return response;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof DomainError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error loading claim status',
        error,
        { path: PATH, resource: RESOURCE, claimId },
      );

      throw DomainErrors.CLAIM_STATUS_LOAD_ERROR(
        `Failed to load claim status: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
