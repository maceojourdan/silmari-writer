/**
 * sessionStateVerifier - Validates client-side session state preconditions.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * Asserts that a session is in the expected state before allowing
 * actions like approval. Throws InvalidStateTransitionError if not.
 */

import { StateTransitionErrors } from '@/server/error_definitions/StateTransitionErrors';

interface SessionWithState {
  id: string;
  state: string;
}

/**
 * Assert that the session is in DRAFT state.
 * Throws InvalidStateTransitionError if not DRAFT.
 */
export function assertDraft(session: SessionWithState): void {
  if (session.state !== 'DRAFT') {
    throw StateTransitionErrors.InvalidStateTransition(session.state, 'DRAFT');
  }
}
