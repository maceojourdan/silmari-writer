/**
 * POST /api/answers/[id]/finalize
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 333-finalize-answer-locks-editing
 *
 * Finalizes an answer, setting finalized=true and editable=false.
 * Validates auth header, then delegates to FinalizeAnswerRequestHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { FinalizeAnswerRequestHandler } from '@/server/request_handlers/FinalizeAnswerRequestHandler';
import { FinalizeAnswerError, FinalizeAnswerErrors } from '@/server/error_definitions/FinalizeAnswerErrors';
import { FinalizeAnswerResultSchema } from '@/server/data_structures/Answer';

export async function POST(
  request: NextRequest,
  { params }: { params: Promise<{ id: string }> },
) {
  try {
    const { id } = await params;

    // 1. Validate answer ID
    if (!id) {
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: 'Answer ID is required' },
        { status: 400 },
      );
    }

    // 2. Authenticate
    const authHeader = request.headers.get('authorization');
    if (!authHeader || authHeader.trim() === '') {
      return NextResponse.json(
        { code: 'UNAUTHORIZED', message: 'Missing or empty authorization header' },
        { status: 401 },
      );
    }

    // 3. Handle request → handler → service → DAO
    const result = await FinalizeAnswerRequestHandler.handle(id);

    // 4. Validate response before sending
    const validation = FinalizeAnswerResultSchema.safeParse(result);
    if (!validation.success) {
      console.error('[answers/finalize] Response validation failed:', validation.error);
      return NextResponse.json(
        { code: 'INTERNAL_ERROR', message: 'Failed to construct valid response' },
        { status: 500 },
      );
    }

    return NextResponse.json(validation.data, { status: 200 });
  } catch (error) {
    // Known finalize answer errors
    if (error instanceof FinalizeAnswerError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors
    console.error('[answers/finalize] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
