/**
 * POST /api/approve-story
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * Applies AuthAndValidationFilter, then delegates to ApproveStoryRequestHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { AuthAndValidationFilter } from '@/server/filters/AuthAndValidationFilter';
import { ApproveStoryRequestHandler } from '@/server/request_handlers/ApproveStoryRequestHandler';
import { StoryError } from '@/server/error_definitions/StoryErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Authenticate
    const authHeader = request.headers.get('authorization');
    const auth = AuthAndValidationFilter.authenticate(authHeader);

    // 2. Parse and validate body
    const rawBody = await request.json();
    const validatedBody = AuthAndValidationFilter.validateBody(rawBody);

    // 3. Handle request → processor → service → DAO
    const result = await ApproveStoryRequestHandler.handle(validatedBody, auth);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    if (error instanceof StoryError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[approve-story] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
