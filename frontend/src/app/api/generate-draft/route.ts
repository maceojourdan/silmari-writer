/**
 * POST /api/generate-draft
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 325-generate-draft-from-confirmed-claims
 *
 * Accepts a claimSetId in the request body, validates with Zod,
 * then delegates to generateDraftHandler.
 *
 * Returns the structured draft or a structured error response.
 */

import { NextRequest, NextResponse } from 'next/server';
import { GenerateDraftRequestSchema } from '@/server/data_structures/StoryStructures';
import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { DraftError } from '@/server/error_definitions/DraftErrors';
import { SharedError } from '@/server/error_definitions/SharedErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Parse raw JSON
    let rawBody: unknown;
    try {
      rawBody = await request.json();
    } catch {
      return NextResponse.json(
        { code: 'INVALID_PARAMETERS', message: 'Request body is not valid JSON' },
        { status: 400 },
      );
    }

    // 2. Validate body against GenerateDraftRequestSchema
    const validation = GenerateDraftRequestSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'INVALID_PARAMETERS', message: `Invalid request payload: ${details}` },
        { status: 400 },
      );
    }

    // 3. Delegate to handler
    const result = await generateDraftHandler.handle(validation.data.claimSetId);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known DraftErrors → use their status code
    if (error instanceof DraftError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Known SharedErrors → use their status code
    if (error instanceof SharedError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Unexpected errors → generic 500
    console.error('[generate-draft] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An error occurred during draft generation' },
      { status: 500 },
    );
  }
}
