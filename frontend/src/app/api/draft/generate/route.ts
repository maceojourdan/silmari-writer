/**
 * POST /api/draft/generate
 *
 * Resource: api-m5g7 (endpoint)
 * Paths:
 *   - 326-generate-draft-with-only-confirmed-claims
 *   - 327-prevent-draft-generation-without-confirmed-claims
 *
 * Accepts either:
 *   - { caseId } → delegates to handleCaseDraft (path 326)
 *   - { storyRecordId } → delegates to handleStoryDraft (path 327)
 *
 * Returns the draft response or a structured error.
 */

import { NextRequest, NextResponse } from 'next/server';
import {
  GenerateCaseDraftRequestSchema,
  GenerateStoryDraftRequestSchema,
} from '@/server/data_structures/Claim';
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

    // 2. Determine request type and validate
    const body = rawBody as Record<string, unknown>;

    // Path 327: storyRecordId-based request
    if (body && typeof body === 'object' && 'storyRecordId' in body) {
      const validation = GenerateStoryDraftRequestSchema.safeParse(rawBody);

      if (!validation.success) {
        const details = validation.error.issues
          .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
          .join('; ');
        return NextResponse.json(
          { code: 'VALIDATION_ERROR', message: `Invalid request payload: ${details}` },
          { status: 400 },
        );
      }

      const result = await generateDraftHandler.handleStoryDraft(validation.data.storyRecordId);
      return NextResponse.json(result, { status: 200 });
    }

    // Path 326: caseId-based request (default)
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
      { code: 'INTERNAL_ERROR', message: 'An error occurred during draft generation' },
      { status: 500 },
    );
  }
}
