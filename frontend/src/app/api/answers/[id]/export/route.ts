/**
 * GET /api/answers/[id]/export
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 334-export-or-copy-finalized-answer
 *
 * Retrieves finalized answer content in the requested export format.
 * Query params: ?format=markdown|plain_text
 *
 * Delegates to ExportFinalizedAnswerHandler → FinalizedAnswerExportService → DAO.
 * Transforms content via AnswerExportTransformer.
 */

import { NextRequest, NextResponse } from 'next/server';
import { ExportFinalizedAnswerHandler } from '@/server/request_handlers/ExportFinalizedAnswerHandler';
import { AnswerExportTransformer } from '@/server/transformers/AnswerExportTransformer';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';
import { SharedError } from '@/server/error_definitions/SharedErrors';
import { ExportFormatSchema } from '@/server/data_structures/ExportFormat';

export async function GET(
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

    // 2. Validate format query parameter
    const format = request.nextUrl.searchParams.get('format');
    if (!format) {
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: 'format query parameter is required' },
        { status: 400 },
      );
    }

    const formatValidation = ExportFormatSchema.safeParse(format);
    if (!formatValidation.success) {
      return NextResponse.json(
        { code: 'UNSUPPORTED_EXPORT_FORMAT', message: `Unsupported export format: ${format}` },
        { status: 400 },
      );
    }

    // 3. Get finalized answer via handler → service → DAO
    const answer = await ExportFinalizedAnswerHandler.handle(id);

    // 4. Transform content to requested format
    const transformedContent = AnswerExportTransformer.transform(answer, formatValidation.data);

    // 5. Return structured response
    return NextResponse.json(
      {
        content: transformedContent,
        format: formatValidation.data,
        answerId: id,
      },
      { status: 200 },
    );
  } catch (error) {
    // Known answer errors (not found, not locked)
    if (error instanceof AnswerError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Shared errors (unsupported format, transformation failure)
    if (error instanceof SharedError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors
    console.error('[answers/export] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
