/**
 * WebhookErrors - Shared error definitions for webhook validation failures.
 *
 * Covers claim correlation failures and invalid webhook payloads.
 *
 * Resource: cfg-j9w2 (shared_error_definitions)
 * Path: 305-followup-sms-for-uncertain-claim
 */

export type WebhookErrorCode =
  | 'CLAIM_NOT_FOUND'
  | 'INVALID_WEBHOOK_PAYLOAD';

export class WebhookError extends Error {
  code: WebhookErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: WebhookErrorCode,
    statusCode: number = 400,
    retryable: boolean = false,
  ) {
    super(message);
    this.name = 'WebhookError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const WebhookErrors = {
  CLAIM_NOT_FOUND: (message = 'Cannot correlate SMS reply to a claim') =>
    new WebhookError(message, 'CLAIM_NOT_FOUND', 400, false),

  INVALID_WEBHOOK_PAYLOAD: (message = 'Webhook payload is malformed or missing required fields') =>
    new WebhookError(message, 'INVALID_WEBHOOK_PAYLOAD', 400, false),
} as const;
