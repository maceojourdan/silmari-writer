/**
 * POST /api/finalize
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 300-finalize-approved-draft-and-log-metrics
 *
 * Delegates to FinalizeRequestHandler for the full finalization flow:
 * handler → processor → DAO → logger → response.
 */

import { NextRequest, NextResponse } from 'next/server';
import { FinalizeRequestHandler } from '@/server/request_handlers/FinalizeRequestHandler';
import { FinalizeError } from '@/server/error_definitions/FinalizeErrors';
import { FinalizeRequestSchema } from '@/api_contracts/finalize';

export async function POST(request: NextRequest) {
  try {
    const body = await request.json();

    // Validate request body
    const parseResult = FinalizeRequestSchema.safeParse(body);
    if (!parseResult.success) {
      return NextResponse.json(
        {
          code: 'MALFORMED_REQUEST',
          message: `Invalid request: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
        },
        { status: 400 },
      );
    }

    const { draftId, userId } = parseResult.data;

    // Delegate to handler
    const response = await FinalizeRequestHandler.handle(draftId, userId);

    return NextResponse.json(response, { status: 200 });
  } catch (error) {
    if (error instanceof FinalizeError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[finalize] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
