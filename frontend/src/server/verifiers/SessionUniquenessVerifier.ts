/**
 * SessionUniquenessVerifier - Enforces the business rule that only one
 * active session may exist at a time.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 311-reject-duplicate-session-initialization
 *
 * If an active session already exists, throws SESSION_ALREADY_ACTIVE.
 * If no active session exists, returns void (no-op).
 */

import { SessionErrors } from '@/server/error_definitions/SessionErrors';

export const SessionUniquenessVerifier = {
  /**
   * Verify that no active session exists before allowing a new one.
   *
   * @param activeSessionExists - Whether an active session currently exists
   * @throws SessionError with SESSION_ALREADY_ACTIVE if activeSessionExists is true
   */
  verify(activeSessionExists: boolean): void {
    if (activeSessionExists) {
      throw SessionErrors.SessionAlreadyActive();
    }
  },
} as const;
