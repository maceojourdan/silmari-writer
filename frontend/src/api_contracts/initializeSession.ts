/**
 * initializeSession - Typed API contract for session initialization
 * with provided ResumeObject, JobObject, and QuestionObject.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Paths:
 *   - 310-initialize-new-session-with-provided-objects
 *   - 311-reject-duplicate-session-initialization
 *
 * Sends a POST request to create a new session with structured objects
 * and validates the response against the InitializeSessionResponse Zod schema.
 *
 * On duplicate session (409), throws a typed SessionAlreadyActiveError
 * that the frontend can handle to display appropriate UI feedback.
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import {
  ResumeObjectSchema,
  JobObjectSchema,
  QuestionObjectSchema,
} from '@/server/data_structures/SessionObjects';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const InitializeSessionRequestSchema = z.object({
  resume: ResumeObjectSchema,
  job: JobObjectSchema,
  question: QuestionObjectSchema,
});

export type InitializeSessionRequest = z.infer<typeof InitializeSessionRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema (success)
// ---------------------------------------------------------------------------

export const InitializeSessionResponseSchema = z.object({
  id: z.string().uuid(),
  resume: ResumeObjectSchema,
  job: JobObjectSchema,
  question: QuestionObjectSchema,
  state: z.literal('initialized'),
});

export type InitializeSessionResponse = z.infer<typeof InitializeSessionResponseSchema>;

// ---------------------------------------------------------------------------
// Error Response Schema (Path 311: reject-duplicate-session-initialization)
// ---------------------------------------------------------------------------

export const SessionInitErrorResponseSchema = z.object({
  code: z.string(),
  message: z.string(),
});

export type SessionInitErrorResponse = z.infer<typeof SessionInitErrorResponseSchema>;

/**
 * Typed error for SESSION_ALREADY_ACTIVE (HTTP 409).
 * Thrown by initializeSession() when a duplicate session is detected.
 */
export class SessionAlreadyActiveError extends Error {
  code: string;
  statusCode: number;

  constructor(message: string) {
    super(message);
    this.name = 'SessionAlreadyActiveError';
    this.code = 'SESSION_ALREADY_ACTIVE';
    this.statusCode = 409;
  }
}

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the session initialization request
 * with structured ResumeObject, JobObject, and QuestionObject.
 * Validates response via Zod schema.
 * Logs errors via frontendLogger on failure.
 */
export async function initializeSession(
  request: InitializeSessionRequest,
): Promise<InitializeSessionResponse> {
  try {
    const response = await fetch('/api/sessions/initialize', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(request),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));

      // Path 311: Handle SESSION_ALREADY_ACTIVE (HTTP 409) specifically
      if (response.status === 409 && errorBody.code === 'SESSION_ALREADY_ACTIVE') {
        throw new SessionAlreadyActiveError(
          errorBody.message || 'A session is already active.',
        );
      }

      throw new Error(
        errorBody.message || `Session initialization failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = InitializeSessionResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from sessions/initialize: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Session initialization request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'initializeSession', module: 'api_contracts' },
    );

    throw error;
  }
}
