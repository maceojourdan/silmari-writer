/**
 * POST /api/sessions/initialize
 *
 * Resource: api-m5g7 (endpoint)
 * Paths:
 *   - 310-initialize-new-session-with-provided-objects
 *   - 312-reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Accepts structured ResumeObject, JobObject, and QuestionObject in the
 * request body. Validates the shape with Zod, then delegates to the
 * InitializeSessionRequestHandler.
 *
 * Returns the newly created session with state "initialized" and
 * all embedded objects, or a structured error response on failure.
 */

import { NextRequest, NextResponse } from 'next/server';
import { InitializeSessionRequestSchema, InitializeSessionResponseSchema } from '@/server/data_structures/InitializedSession';
import { InitializeSessionRequestHandler } from '@/server/request_handlers/InitializeSessionRequestHandler';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Parse raw JSON — catch malformed JSON (Path 312)
    let rawBody: unknown;
    try {
      rawBody = await request.json();
    } catch {
      return NextResponse.json(
        { code: 'INVALID_REQUEST_FORMAT', message: 'Request body is not valid JSON' },
        { status: 400 },
      );
    }

    // 2. Validate body against InitializeSessionRequestSchema (Path 312)
    const validation = InitializeSessionRequestSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'INVALID_REQUEST_FORMAT', message: `Invalid request payload: ${details}` },
        { status: 400 },
      );
    }

    // 3. Delegate to handler → service → DAO
    const session = await InitializeSessionRequestHandler.handle(validation.data);

    // 4. Validate response before sending
    const responseData = {
      id: session.id,
      resume: session.resume,
      job: session.job,
      question: session.question,
      state: session.state,
    };

    const responseValidation = InitializeSessionResponseSchema.safeParse(responseData);
    if (!responseValidation.success) {
      return NextResponse.json(
        { code: 'SERVICE_ERROR', message: 'Failed to construct valid response' },
        { status: 500 },
      );
    }

    return NextResponse.json(responseValidation.data, { status: 200 });
  } catch (error) {
    // Known session errors → use their status code
    if (error instanceof SessionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Known generic errors → use their status code
    if (error instanceof GenericError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors → generic user-safe error (Path 312)
    console.error('[sessions/initialize] Unexpected error:', error);
    return NextResponse.json(
      { code: 'GENERIC_USER_ERROR', message: 'An error occurred during session initialization' },
      { status: 500 },
    );
  }
}
