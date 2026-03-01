/**
 * POST /api/session/init
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 294-parse-and-store-session-input-objects
 *
 * Validates request body with SessionInitInputSchema, then delegates
 * to InitSessionRequestHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { SessionInitInputSchema } from '@/verifiers/SessionInitVerifier';
import { InitSessionRequestHandler } from '@/server/request_handlers/InitSessionRequestHandler';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Parse and validate body
    const rawBody = await request.json();
    const validation = SessionInitInputSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: `Invalid request payload: ${details}` },
        { status: 400 },
      );
    }

    // 2. Handle request → processor → service → DAO
    const result = await InitSessionRequestHandler.handle(validation.data);

    return NextResponse.json(result, { status: 200 });
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

    // Completely unexpected errors → 500
    console.error('[session/init] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
