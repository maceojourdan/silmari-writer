/**
 * ConsentErrors - Shared error definitions for consent-required failures.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 */

export type ConsentErrorCode = 'CONSENT_REQUIRED';

export class ConsentError extends Error {
  code: ConsentErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: ConsentErrorCode,
    statusCode: number = 400,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'ConsentError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const ConsentErrors = {
  ConsentRequired: () =>
    new ConsentError(
      'Affirmative consent is required before starting voice session',
      'CONSENT_REQUIRED',
      400,
      false,
    ),
} as const;
