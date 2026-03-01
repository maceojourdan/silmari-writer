/**
 * POST /api/edit-by-voice
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 330-edit-content-by-voice-from-review-screen
 *
 * Validates request body via Zod schema, then delegates to
 * EditByVoiceRequestHandler for the voice edit flow:
 * handler → service → DAO → response with updated content.
 */

import { NextRequest, NextResponse } from 'next/server';
import { z } from 'zod';
import { EditByVoiceRequestHandler } from '@/server/request_handlers/EditByVoiceRequestHandler';
import { EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

const EditByVoiceRequestSchema = z.object({
  contentId: z.string().min(1, 'contentId is required'),
  instructionText: z.string().min(1, 'instructionText is required'),
});

// ---------------------------------------------------------------------------
// Route Handler
// ---------------------------------------------------------------------------

export async function POST(request: NextRequest) {
  try {
    // Step 1: Parse and validate request body
    const body = await request.json();
    const parsed = EditByVoiceRequestSchema.safeParse(body);

    if (!parsed.success) {
      return NextResponse.json(
        {
          code: 'INVALID_REQUEST',
          message: parsed.error.issues.map((i) => `${i.path.join('.')}: ${i.message}`).join(', '),
        },
        { status: 400 },
      );
    }

    // Step 2: Delegate to handler → service → DAO
    const result = await EditByVoiceRequestHandler.handle(
      parsed.data.contentId,
      parsed.data.instructionText,
    );

    // Step 3: Return success response with updated content
    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known domain errors → return with appropriate status
    if (error instanceof EditByVoiceError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Unexpected errors → 500
    console.error('[edit-by-voice] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
