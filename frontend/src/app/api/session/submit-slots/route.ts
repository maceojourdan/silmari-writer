/**
 * POST /api/session/submit-slots
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 320-re-prompt-unfilled-required-slots
 *
 * Receives slot submission payload (sessionId, questionType, slotValues,
 * attemptCount), delegates to SubmitSlotsHandler, and returns the
 * re-prompt response with missing slot prompts.
 */

import { NextRequest, NextResponse } from 'next/server';
import { SubmitSlotsHandler } from '@/server/request_handlers/SubmitSlotsHandler';
import { SlotError } from '@/server/error_definitions/SlotErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Parse request body
    const rawBody = await request.json();

    // 2. Delegate to handler (validates payload + processes)
    const result = await SubmitSlotsHandler.handle(rawBody);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known slot errors → use their status code
    if (error instanceof SlotError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors → 500
    console.error('[session/submit-slots] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
