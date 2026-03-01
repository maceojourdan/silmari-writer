/**
 * POST /api/orient/story
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 295-orient-state-creates-single-story-record
 *
 * Validates request body with OrientEventSchema, then delegates
 * to CreateStoryRecordHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { OrientEventSchema } from '@/server/data_structures/OrientStoryRecord';
import { CreateStoryRecordHandler } from '@/server/request_handlers/CreateStoryRecordHandler';
import { OrientError } from '@/server/error_definitions/OrientErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Parse and validate body
    const rawBody = await request.json();
    const validation = OrientEventSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: `Invalid request payload: ${details}` },
        { status: 400 },
      );
    }

    // 2. Handle request → process chain → verifier → DAO
    const result = await CreateStoryRecordHandler.handle(validation.data);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known orient errors → use their status code
    if (error instanceof OrientError) {
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
    console.error('[orient/story] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
