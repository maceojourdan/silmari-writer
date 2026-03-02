/**
 * PUT /api/answers/[id]
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 337-prevent-edit-of-locked-answer
 *
 * Updates the content of an answer, rejecting if the answer is locked/finalized.
 * Validates auth header and request body, then delegates to UpdateAnswerRequestHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { z } from 'zod';
import { UpdateAnswerRequestHandler } from '@/server/request_handlers/UpdateAnswerRequestHandler';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';

// ---------------------------------------------------------------------------
// Request Body Schema
// ---------------------------------------------------------------------------

const UpdateAnswerBodySchema = z.object({
  content: z.string().min(1, 'Content must not be empty'),
});

// ---------------------------------------------------------------------------
// PUT Handler
// ---------------------------------------------------------------------------

export async function PUT(
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

    // 3. Parse and validate request body
    let body: unknown;
    try {
      body = await request.json();
    } catch {
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: 'Invalid JSON body' },
        { status: 400 },
      );
    }

    const validation = UpdateAnswerBodySchema.safeParse(body);
    if (!validation.success) {
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: validation.error.issues[0]?.message ?? 'Request validation failed' },
        { status: 400 },
      );
    }

    const { content } = validation.data;

    // 4. Delegate to request handler
    const result = await UpdateAnswerRequestHandler.handle(id, content);

    // 5. Return success response
    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known answer errors
    if (error instanceof AnswerError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors
    console.error('[answers/[id]] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
