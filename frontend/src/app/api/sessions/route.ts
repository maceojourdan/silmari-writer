/**
 * POST /api/sessions
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Creates a new voice-assisted answer session.
 * Applies AuthFilter to validate authentication,
 * then delegates to CreateSessionHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { AuthAndValidationFilter } from '@/server/filters/AuthAndValidationFilter';
import { CreateSessionHandler } from '@/server/request_handlers/CreateSessionHandler';
import { CreateSessionResponseSchema } from '@/server/data_structures/AnswerSession';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { HttpError, HttpErrors } from '@/server/error_definitions/HttpErrors';
import { StoryError } from '@/server/error_definitions/StoryErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Authenticate via AuthFilter
    const authHeader = request.headers.get('authorization');
    const authContext = AuthAndValidationFilter.authenticate(authHeader);

    // 2. Delegate to handler
    const result = await CreateSessionHandler.handle({
      userId: authContext.userId,
    });

    // 3. Validate response before sending
    const responseData = {
      sessionId: result.sessionId,
      state: result.state,
    };

    const validation = CreateSessionResponseSchema.safeParse(responseData);
    if (!validation.success) {
      throw HttpErrors.internal('Failed to construct valid response');
    }

    return NextResponse.json(validation.data, { status: 200 });
  } catch (error) {
    // Auth errors from filter (StoryError.UNAUTHORIZED)
    if (error instanceof StoryError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Known session errors
    if (error instanceof SessionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Known HTTP errors
    if (error instanceof HttpError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors
    console.error('[sessions] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
