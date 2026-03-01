/**
 * POST /api/review/approve
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Validates request body via Zod schema, then delegates to
 * ApproveContentHandler for the approval flow:
 * handler → service → DAO → workflow chain → response.
 */

import { NextRequest, NextResponse } from 'next/server';
import { z } from 'zod';
import { ApproveContentHandler } from '@/server/request_handlers/ApproveContentHandler';
import { ApprovalError } from '@/server/error_definitions/ApprovalErrors';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

const ApproveRequestSchema = z.object({
  contentId: z.string().min(1, 'contentId is required'),
});

// ---------------------------------------------------------------------------
// Route Handler
// ---------------------------------------------------------------------------

export async function POST(request: NextRequest) {
  try {
    // Step 1: Parse and validate request body
    const body = await request.json();
    const parsed = ApproveRequestSchema.safeParse(body);

    if (!parsed.success) {
      return NextResponse.json(
        {
          code: 'INVALID_REQUEST',
          message: parsed.error.issues.map((i) => `${i.path.join('.')}: ${i.message}`).join(', '),
        },
        { status: 400 },
      );
    }

    // Step 2: Delegate to handler → service → DAO → workflow chain
    const result = await ApproveContentHandler.handle(parsed.data.contentId);

    // Step 3: Return success response with workflow stage
    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known domain errors → return with appropriate status
    if (error instanceof ApprovalError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Unexpected errors → 500
    console.error('[review/approve] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
