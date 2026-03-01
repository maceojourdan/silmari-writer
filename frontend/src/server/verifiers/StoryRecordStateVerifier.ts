/**
 * StoryRecordStateVerifier - Enforces immutability rule for FINALIZED sessions.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 309-reject-modifications-to-finalized-session
 *
 * When a StoryRecord is in FINALIZED state, no further modifications
 * are allowed. This verifier checks the state and returns a result
 * indicating whether modification is permitted.
 */

import type { StoryRecord } from '@/server/data_structures/StoryRecord';

export interface ModificationVerifierResult {
  allowed: boolean;
  reason?: string;
}

export const StoryRecordStateVerifier = {
  /**
   * Check whether a StoryRecord can be modified.
   *
   * Returns { allowed: false, reason: 'SESSION_ALREADY_FINALIZED' }
   * when the record is in FINALIZED state.
   *
   * Returns { allowed: true } for all other states.
   */
  canModify(record: StoryRecord): ModificationVerifierResult {
    if (record.status === 'FINALIZED') {
      return { allowed: false, reason: 'SESSION_ALREADY_FINALIZED' };
    }

    return { allowed: true };
  },
} as const;
