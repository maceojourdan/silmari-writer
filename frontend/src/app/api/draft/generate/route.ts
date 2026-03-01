/**
 * POST /api/draft/generate
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 326-generate-draft-with-only-confirmed-claims
 *
 * Accepts a caseId in the request body, validates with Zod,
 * then delegates to generateDraftHandler.handleCaseDraft.
 *
 * Returns the case draft (caseId, content, claimsUsed) or a structured error.
 */

import { NextRequest, NextResponse } from 'next/server';
import { GenerateCaseDraftRequestSchema } from '@/server/data_structures/Claim';
import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';
import { DraftError } from '@/server/error_definitions/DraftErrors';

export async function POST(request: NextRequest) {
  try {
    // 1. Parse raw JSON
    let rawBody: unknown;
    try {
      rawBody = await request.json();
    } catch {
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: 'Request body is not valid JSON' },
        { status: 400 },
      );
    }

    // 2. Validate body against GenerateCaseDraftRequestSchema
    const validation = GenerateCaseDraftRequestSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: `Invalid request payload: ${details}` },
        { status: 400 },
      );
    }

    // 3. Delegate to handler
    const result = await generateDraftHandler.handleCaseDraft(validation.data.caseId);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known DraftErrors → use their status code
    if (error instanceof DraftError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Unexpected errors → generic 500
    console.error('[draft/generate] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An error occurred during case draft generation' },
      { status: 500 },
    );
  }
}
