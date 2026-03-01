/**
 * VerificationService - Orchestrates the claim verification via voice/SMS path.
 *
 * Implements sequential steps:
 * 1. Detect unverified key claims
 * 2. Initiate voice or SMS verification request
 * 3. Receive and validate claimant confirmation
 * 4. Mark claims as verified
 * 5. Enable drafting process
 *
 * Path 323 additions:
 * - loadClaimant: Load claimant data by ID
 * - recordVerificationFailure: Persist a failed verification attempt
 * - startDrafting: Guard drafting based on verification status
 * - initiateContactVerification: Full path orchestration for 323
 *
 * Resource: db-h2s4 (service)
 * Paths:
 *   - 321-verify-key-claims-via-voice-or-sms
 *   - 323-fail-verification-when-no-contact-method
 */

import type { ClaimRecord, EligibilityResult } from '@/server/data_structures/ClaimRecord';
import type {
  VerificationRequest,
  ConfirmationResult,
  InboundConfirmationPayload,
} from '@/server/data_structures/VerificationRequest';
import type { Session } from '@/server/data_structures/Session';
import type { Claimant } from '@/server/data_structures/Claimant';
import type { VerificationAttempt } from '@/server/data_structures/VerificationAttempt';
import type { InitiateVerificationResponse, StartDraftingResult } from '@/server/data_structures/VerificationAttempt';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { VerificationRequestDAO } from '@/server/data_access_objects/VerificationRequestDAO';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { VerificationDAO } from '@/server/data_access_objects/VerificationDAO';
import { ClaimEligibilityVerifier } from '@/server/verifiers/ClaimEligibilityVerifier';
import { ContactMethodVerifier } from '@/server/verifiers/ContactMethodVerifier';
import { VerificationErrors } from '@/server/error_definitions/VerificationErrors';
import { verificationLogger } from '@/server/logging/verificationLogger';

// ---------------------------------------------------------------------------
// SMS/Voice Client Interface (mockable)
// ---------------------------------------------------------------------------

export interface VerificationClient {
  sendMessage(to: string, body: string): Promise<{ sid: string }>;
}

// ---------------------------------------------------------------------------
// Timer interface for mockable delays
// ---------------------------------------------------------------------------

export interface VerificationTimer {
  delay(ms: number): Promise<void>;
}

const defaultTimer: VerificationTimer = {
  async delay(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  },
};

// ---------------------------------------------------------------------------
// Token generator (mockable)
// ---------------------------------------------------------------------------

export interface TokenGenerator {
  generate(): string;
}

const defaultTokenGenerator: TokenGenerator = {
  generate(): string {
    return `vrf-${Date.now()}-${Math.random().toString(36).substring(2, 10)}`;
  },
};

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const VerificationService = {
  // -------------------------------------------------------------------------
  // Step 1: Detect unverified key claims
  // -------------------------------------------------------------------------

  /**
   * Detect whether a session has all required key claims ready for verification.
   *
   * Retrieves unverified claims from the DAO and validates that all required
   * categories (metrics, scope, production, security) are present.
   *
   * @throws VerificationErrors.CLAIM_ELIGIBILITY_ERROR if categories are missing or malformed
   */
  async detectEligibility(sessionId: string): Promise<EligibilityResult> {
    verificationLogger.info('Detecting claim eligibility', { sessionId });

    const claims = await ClaimDAO.getUnverifiedClaimsBySession(sessionId);

    // Validate using the eligibility verifier (throws on failure)
    ClaimEligibilityVerifier.validate(claims);

    verificationLogger.info('Claims eligible for verification', {
      sessionId,
      claimCount: claims.length,
    });

    return { eligible: true, claims };
  },

  // -------------------------------------------------------------------------
  // Step 2: Initiate voice or SMS verification request
  // -------------------------------------------------------------------------

  /**
   * Initiate a verification request via SMS or voice.
   *
   * Creates a verification request record, then sends the message
   * with retry logic (up to 3 attempts).
   *
   * @throws VerificationErrors.INVALID_CONTACT if contact details are missing
   * @throws VerificationErrors.DELIVERY_FAILED if delivery fails after retries
   */
  async initiateVerification(
    sessionId: string,
    client: VerificationClient,
    timer: VerificationTimer = defaultTimer,
    tokenGenerator: TokenGenerator = defaultTokenGenerator,
  ): Promise<VerificationRequest> {
    verificationLogger.info('Initiating verification', { sessionId });

    // Get eligible claims
    const { claims } = await this.detectEligibility(sessionId);

    // Validate contact details
    const contactClaim = claims.find(c => c.contactPhone);
    if (!contactClaim || !contactClaim.contactPhone) {
      throw VerificationErrors.INVALID_CONTACT(
        `No contact phone number found for session ${sessionId}`,
      );
    }

    const token = tokenGenerator.generate();
    const contactMethod = contactClaim.contactMethod || 'sms';
    const claimIds = claims.map(c => c.id);

    // Create verification request record
    const request = await VerificationRequestDAO.create({
      sessionId,
      claimIds,
      contactPhone: contactClaim.contactPhone,
      contactMethod,
      token,
    });

    // Compose message
    const claimSummary = claims.map(c => `- ${c.category}: ${c.content}`).join('\n');
    const message = `Verification request for your claims:\n${claimSummary}\n\nPlease confirm all claims using token: ${token}`;

    // Send with retry logic (up to 3 attempts)
    const maxAttempts = 3;
    let lastError: Error | null = null;

    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
      try {
        const result = await client.sendMessage(contactClaim.contactPhone, message);

        // Log successful delivery
        await VerificationRequestDAO.logDeliveryAttempt({
          requestId: request.id,
          attemptNumber: attempt,
          status: 'success',
          externalId: result.sid,
        });

        verificationLogger.info('Verification request delivered', {
          sessionId,
          requestId: request.id,
          attemptNumber: attempt,
        });

        return request;
      } catch (error) {
        lastError = error instanceof Error ? error : new Error(String(error));

        // Log failed delivery attempt
        await VerificationRequestDAO.logDeliveryAttempt({
          requestId: request.id,
          attemptNumber: attempt,
          status: 'failed',
          errorMessage: lastError.message,
        });

        verificationLogger.error(
          `Verification delivery attempt ${attempt}/${maxAttempts} failed`,
          error,
          { sessionId, requestId: request.id },
        );

        if (attempt === maxAttempts) {
          // Mark request as failed
          await VerificationRequestDAO.updateStatus(request.id, 'failed', attempt);

          throw VerificationErrors.DELIVERY_FAILED(
            `Failed to deliver verification after ${maxAttempts} attempts for session ${sessionId}`,
          );
        }

        // Exponential backoff
        await timer.delay(Math.pow(2, attempt - 1) * 1000);
      }
    }

    // Unreachable but TypeScript needs this
    throw VerificationErrors.DELIVERY_FAILED();
  },

  // -------------------------------------------------------------------------
  // Step 3: Receive and validate claimant confirmation
  // -------------------------------------------------------------------------

  /**
   * Handle an inbound confirmation response.
   *
   * Matches the confirmation to a pending request and validates that
   * all claim items are explicitly confirmed.
   *
   * @throws VerificationErrors.CONFIRMATION_FAILED if partial or mismatched
   */
  async handleInboundConfirmation(
    payload: InboundConfirmationPayload,
    client?: VerificationClient,
    timer?: VerificationTimer,
    tokenGenerator?: TokenGenerator,
  ): Promise<ConfirmationResult> {
    verificationLogger.info('Handling inbound confirmation', { token: payload.token });

    // Find the pending request by token
    const request = await VerificationRequestDAO.findByToken(payload.token);

    if (!request) {
      throw VerificationErrors.CONFIRMATION_FAILED(
        `No pending verification request found for token ${payload.token}`,
      );
    }

    // Check all claim IDs are confirmed
    const allConfirmed = request.claimIds.every(
      id => payload.confirmedClaimIds.includes(id),
    );

    if (!allConfirmed) {
      const missingIds = request.claimIds.filter(
        id => !payload.confirmedClaimIds.includes(id),
      );

      verificationLogger.warn('Partial confirmation received', {
        requestId: request.id,
        missingClaimIds: missingIds,
        attemptCount: request.attemptCount,
      });

      // Update request status to failed
      const newAttemptCount = request.attemptCount + 1;
      await VerificationRequestDAO.updateStatus(request.id, 'failed', newAttemptCount);

      // If retry limit not exceeded, re-initiate
      if (newAttemptCount < 3 && client) {
        verificationLogger.info('Re-initiating verification after partial confirmation', {
          sessionId: request.sessionId,
          attemptCount: newAttemptCount,
        });
        await this.initiateVerification(
          request.sessionId,
          client,
          timer,
          tokenGenerator,
        );
      }

      throw VerificationErrors.CONFIRMATION_FAILED(
        `Partial confirmation: missing claim IDs: ${missingIds.join(', ')}`,
      );
    }

    // Full confirmation - update request status
    await VerificationRequestDAO.updateStatus(request.id, 'confirmed', request.attemptCount);

    verificationLogger.info('Full confirmation received', {
      requestId: request.id,
      sessionId: request.sessionId,
    });

    return {
      fullConfirmation: true,
      confirmedClaimIds: payload.confirmedClaimIds,
      requestId: request.id,
    };
  },

  // -------------------------------------------------------------------------
  // Step 4: Mark claims as verified
  // -------------------------------------------------------------------------

  /**
   * Mark all session claims as verified.
   *
   * Updates claim status to 'verified' with timestamp.
   *
   * @throws VerificationErrors.DATA_ACCESS_ERROR on persistence failure
   */
  async markClaimsVerified(sessionId: string): Promise<ClaimRecord[]> {
    verificationLogger.info('Marking claims as verified', { sessionId });

    try {
      const claims = await ClaimDAO.getUnverifiedClaimsBySession(sessionId);
      const claimIds = claims.map(c => c.id);
      const updatedClaims = await ClaimDAO.updateStatusToVerified(claimIds);

      verificationLogger.info('Claims marked as verified', {
        sessionId,
        claimCount: updatedClaims.length,
      });

      return updatedClaims;
    } catch (error) {
      verificationLogger.error('Failed to mark claims as verified', error, { sessionId });

      throw VerificationErrors.DATA_ACCESS_ERROR(
        `Failed to update claim status for session ${sessionId}: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },

  // -------------------------------------------------------------------------
  // Step 5: Enable drafting process
  // -------------------------------------------------------------------------

  /**
   * Enable the drafting process after all claims are verified.
   *
   * Checks that all claims for the session are verified, then
   * updates the session state to DRAFT_ENABLED.
   *
   * @throws VerificationErrors.VERIFICATION_STATE_INCONSISTENT if not all claims verified
   */
  async enableDrafting(sessionId: string): Promise<Session> {
    verificationLogger.info('Enabling drafting process', { sessionId });

    // Get all claims for the session (both verified and unverified)
    const unverifiedClaims = await ClaimDAO.getUnverifiedClaimsBySession(sessionId);

    if (unverifiedClaims.length > 0) {
      verificationLogger.error('Cannot enable drafting: unverified claims remain', undefined, {
        sessionId,
        unverifiedCount: unverifiedClaims.length,
      });

      throw VerificationErrors.VERIFICATION_STATE_INCONSISTENT(
        `Cannot enable drafting: ${unverifiedClaims.length} unverified claim(s) remain for session ${sessionId}`,
      );
    }

    // Update session state to DRAFT_ENABLED
    const updatedSession = await SessionDAO.updateState(sessionId, 'DRAFT_ENABLED');

    verificationLogger.info('Drafting process enabled', {
      sessionId,
      newState: updatedSession.state,
    });

    return updatedSession;
  },

  // =========================================================================
  // Path 323: fail-verification-when-no-contact-method
  // =========================================================================

  // -------------------------------------------------------------------------
  // Step 2 (Path 323): Load Claimant Data
  // -------------------------------------------------------------------------

  /**
   * Load claimant profile including key claims and contact methods.
   *
   * @throws VerificationErrors.CLAIMANT_NOT_FOUND if claimant record does not exist
   */
  async loadClaimant(claimantId: string): Promise<Claimant> {
    verificationLogger.info('Loading claimant data', {
      claimantId,
      path: '323-fail-verification-when-no-contact-method',
    });

    const claimant = await VerificationDAO.getClaimantById(claimantId);

    if (!claimant) {
      throw VerificationErrors.CLAIMANT_NOT_FOUND(
        `Claimant not found for id: ${claimantId}`,
      );
    }

    return claimant;
  },

  // -------------------------------------------------------------------------
  // Step 4 (Path 323): Record Verification Failure
  // -------------------------------------------------------------------------

  /**
   * Create or update a verification attempt with status FAILED.
   *
   * @throws VerificationErrors.VERIFICATION_PERSISTENCE_FAILED on persistence error
   */
  async recordVerificationFailure(
    claimantId: string,
    reason: string,
  ): Promise<VerificationAttempt> {
    verificationLogger.info('Recording verification failure', {
      claimantId,
      reason,
      path: '323-fail-verification-when-no-contact-method',
    });

    try {
      const attempt = await VerificationDAO.createVerificationAttempt(
        claimantId,
        'FAILED',
        reason,
      );

      verificationLogger.info('Verification failure recorded', {
        claimantId,
        attemptId: attempt.id,
      });

      return attempt;
    } catch (error) {
      verificationLogger.error(
        'Failed to persist verification failure',
        error,
        {
          claimantId,
          reason,
          path: '323-fail-verification-when-no-contact-method',
        },
      );

      throw VerificationErrors.VERIFICATION_PERSISTENCE_FAILED(
        `Failed to persist verification attempt for claimant ${claimantId}: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },

  // -------------------------------------------------------------------------
  // Step 5 (Path 323): Prevent Drafting From Starting
  // -------------------------------------------------------------------------

  /**
   * Guard against starting drafting when verification has failed.
   *
   * If latest verification attempt is FAILED, return rejection.
   * If drafting is already IN_PROGRESS, mark as BLOCKED and log.
   */
  async startDrafting(claimantId: string): Promise<StartDraftingResult> {
    verificationLogger.info('Checking drafting eligibility', {
      claimantId,
      path: '323-fail-verification-when-no-contact-method',
    });

    const attempt = await VerificationDAO.getLatestVerificationAttempt(claimantId);

    if (attempt && attempt.status === 'FAILED') {
      // If drafting was already in progress, mark as blocked
      if (attempt.draftingStatus === 'IN_PROGRESS') {
        verificationLogger.warn('Drafting was IN_PROGRESS but verification failed; marking BLOCKED', {
          claimantId,
          attemptId: attempt.id,
          path: '323-fail-verification-when-no-contact-method',
        });

        await VerificationDAO.updateDraftingStatus(attempt.id, 'BLOCKED');
      }

      return {
        draftingAllowed: false,
        reason: 'VERIFICATION_FAILED',
      };
    }

    return {
      draftingAllowed: true,
    };
  },

  // -------------------------------------------------------------------------
  // Full Path 323 orchestration: Initiate Contact Verification
  // -------------------------------------------------------------------------

  /**
   * Orchestrate the full Path 323 flow:
   * 1. Load claimant data
   * 2. Validate contact method availability
   * 3. Record verification failure if no contact method
   * 4. Return structured response
   *
   * @throws VerificationErrors.CLAIMANT_NOT_FOUND if claimant not found
   * @throws VerificationErrors.VERIFICATION_PERSISTENCE_FAILED on persistence error
   */
  async initiateContactVerification(
    claimantId: string,
  ): Promise<InitiateVerificationResponse> {
    verificationLogger.info('Initiating contact verification', {
      claimantId,
      path: '323-fail-verification-when-no-contact-method',
    });

    // Step 2: Load claimant data
    const claimant = await this.loadClaimant(claimantId);

    // Step 3: Validate contact method availability
    const { hasContactMethod } = ContactMethodVerifier.validate(claimant);

    if (!hasContactMethod) {
      // Step 4: Record verification failure
      await this.recordVerificationFailure(claimantId, 'MISSING_CONTACT_METHOD');

      // Step 5: Drafting is not allowed
      return {
        verificationStatus: 'FAILED',
        reason: 'MISSING_CONTACT_METHOD',
        draftingAllowed: false,
      };
    }

    // If contact method exists, verification is pending (other paths handle this)
    return {
      verificationStatus: 'PENDING',
      draftingAllowed: false, // Drafting waits until verification completes
    };
  },
} as const;
