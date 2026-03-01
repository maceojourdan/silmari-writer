/**
 * SessionModificationService - Orchestrates session modification validation.
 *
 * Resource: db-h2s4 (service)
 * Path: 309-reject-modifications-to-finalized-session
 *
 * Loads a StoryRecord via DAO, applies the StoryRecordStateVerifier,
 * and rejects modifications to FINALIZED sessions.
 * Does NOT invoke DAO persistence methods on rejection.
 */

import { StoryRecordDAO } from '@/server/data_access_objects/StoryRecordDAO';
import { StoryRecordStateVerifier } from '@/server/verifiers/StoryRecordStateVerifier';
import { SessionErrors, SessionError } from '@/server/error_definitions/SessionErrors';
import type { StoryRecord } from '@/server/data_structures/StoryRecord';

export type ModificationAction = 'ADD_VOICE' | 'FINALIZE';

export type ModificationResult =
  | { success: true; record: StoryRecord }
  | { success: false; error: SessionError };

export const SessionModificationService = {
  /**
   * Process a modification request for a session.
   *
   * 1. Load StoryRecord via DAO
   * 2. Apply StoryRecordStateVerifier
   * 3. If verifier disallows → return error (no DAO.update call)
   * 4. If verifier allows → return success with record
   *
   * Throws SessionErrors.NotFound if session doesn't exist.
   * Returns error result with SESSION_ALREADY_FINALIZED for finalized sessions.
   * Falls back to CONFLICT_GENERIC if error mapping fails.
   */
  async processModification(
    sessionId: string,
    _action: ModificationAction,
  ): Promise<ModificationResult> {
    // Step 3: Load StoryRecord via DAO
    const record = await StoryRecordDAO.findById(sessionId);

    if (!record) {
      throw SessionErrors.NotFound(`Session ${sessionId} not found`);
    }

    // Cast to StoryRecord type for the verifier
    const storyRecord = record as unknown as StoryRecord;

    // Step 4 + 5: Verify state and reject if finalized
    try {
      const verification = StoryRecordStateVerifier.canModify(storyRecord);

      if (!verification.allowed) {
        // Step 5: Reject — do NOT call DAO.update
        return {
          success: false,
          error: SessionErrors.SessionAlreadyFinalized(),
        };
      }

      // Modification is allowed
      return { success: true, record: storyRecord };
    } catch {
      // Fallback to generic conflict error if error mapping fails
      return {
        success: false,
        error: SessionErrors.ConflictGeneric(),
      };
    }
  },
} as const;
