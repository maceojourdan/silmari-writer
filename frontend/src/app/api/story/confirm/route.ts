/**
 * POST /api/story/confirm
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 313-confirm-aligned-story-selection
 *
 * Validates request body with ConfirmStoryRequestSchema,
 * delegates to ConfirmStoryService.
 */

import { NextRequest, NextResponse } from 'next/server';
import { ConfirmStoryRequestSchema } from '@/server/data_structures/ConfirmStory';
import { ConfirmStoryService } from '@/server/services/ConfirmStoryService';
import { ConfirmStoryError } from '@/server/error_definitions/ConfirmStoryErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Parse and validate body
    const rawBody = await request.json();
    const validation = ConfirmStoryRequestSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: `Invalid request payload: ${details}` },
        { status: 400 },
      );
    }

    // 2. Delegate to service
    const result = await ConfirmStoryService.confirm(validation.data);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known confirm story errors → use their status code
    if (error instanceof ConfirmStoryError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors → 500
    console.error('[story/confirm] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
