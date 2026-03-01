/**
 * StateTransitionErrors - Shared error definitions for invalid state transitions.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

export type StateTransitionErrorCode =
  | 'INVALID_STATE_TRANSITION'
  | 'SESSION_NOT_FOUND';

export class StateTransitionError extends Error {
  code: StateTransitionErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: StateTransitionErrorCode,
    statusCode: number = 400,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'StateTransitionError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const StateTransitionErrors = {
  InvalidStateTransition: (currentState: string, targetState: string) =>
    new StateTransitionError(
      `Cannot transition from ${currentState} to ${targetState}`,
      'INVALID_STATE_TRANSITION',
      409,
      false,
    ),

  SessionNotFound: (sessionId: string) =>
    new StateTransitionError(
      `Session not found: ${sessionId}`,
      'SESSION_NOT_FOUND',
      404,
      false,
    ),
} as const;
