/**
 * POST /api/sessions/[id]/finalize
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 *
 * Finalizes a voice session and persists the associated StoryRecord.
 * Delegates to FinalizeSessionRequestHandler for the full flow:
 * handler → service → DAO → response.
 */

import { NextRequest, NextResponse } from 'next/server';
import { FinalizeSessionRequestHandler } from '@/server/request_handlers/FinalizeSessionRequestHandler';
import { FinalizeSessionError } from '@/server/error_definitions/FinalizeSessionErrors';
import { HttpError } from '@/server/error_definitions/HttpErrors';
import { FinalizeSessionResponseSchema } from '@/api_contracts/finalizeSession';

export async function POST(
  request: NextRequest,
  { params }: { params: Promise<{ id: string }> },
) {
  try {
    const { id } = await params;

    if (!id) {
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: 'Session ID is required' },
        { status: 400 },
      );
    }

    // Delegate to handler → service → DAO
    const result = await FinalizeSessionRequestHandler.handle(id);

    // Validate response before sending
    const validation = FinalizeSessionResponseSchema.safeParse(result);
    if (!validation.success) {
      console.error('[sessions/finalize] Response validation failed:', validation.error);
      return NextResponse.json(
        { code: 'INTERNAL_ERROR', message: 'Failed to construct valid response' },
        { status: 500 },
      );
    }

    return NextResponse.json(validation.data, { status: 200 });
  } catch (error) {
    // Known finalize session errors
    if (error instanceof FinalizeSessionError) {
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
    console.error('[sessions/finalize] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
