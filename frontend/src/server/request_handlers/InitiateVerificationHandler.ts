/**
 * InitiateVerificationHandler - Bridges the verification initiation endpoint
 * to the VerificationService for Path 323.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 323-fail-verification-when-no-contact-method
 *
 * Known errors (VerificationError) are rethrown as-is.
 * Unknown errors are logged and wrapped in VerificationErrors.GENERIC_VERIFICATION_FAILURE.
 */

import { VerificationService } from '@/server/services/VerificationService';
import {
  VerificationError,
  VerificationErrors,
} from '@/server/error_definitions/VerificationErrors';
import { verificationLogger } from '@/server/logging/verificationLogger';
import type { InitiateVerificationRequest, InitiateVerificationResponse } from '@/server/data_structures/VerificationAttempt';

export const InitiateVerificationHandler = {
  /**
   * Handle a verification initiation request by delegating to VerificationService.
   *
   * @param payload - Validated payload { claimantId: uuid }
   * @returns InitiateVerificationResponse with status and drafting eligibility
   * @throws VerificationError for known errors (rethrown)
   * @throws VerificationError GENERIC_VERIFICATION_FAILURE for unexpected errors
   */
  async handle(payload: InitiateVerificationRequest): Promise<InitiateVerificationResponse> {
    try {
      const result = await VerificationService.initiateContactVerification(
        payload.claimantId,
      );

      return result;
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof VerificationError) {
        throw error;
      }

      // Unknown errors → log and wrap
      verificationLogger.error(
        'Unexpected error during verification initiation',
        error,
        {
          path: '323-fail-verification-when-no-contact-method',
          resource: 'api-n8k2',
        },
      );

      throw VerificationErrors.GENERIC_VERIFICATION_FAILURE(
        `Failed to initiate verification: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
