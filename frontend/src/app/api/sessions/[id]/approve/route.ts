/**
 * POST /api/sessions/[id]/approve
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * Delegates to ApproveSessionHandler for session approval flow:
 * handler → service → DAO → logger → response.
 */

import { NextRequest, NextResponse } from 'next/server';
import { ApproveSessionHandler } from '@/server/request_handlers/ApproveSessionHandler';
import { StateTransitionError } from '@/server/error_definitions/StateTransitionErrors';
import { PersistenceError } from '@/server/error_definitions/PersistenceErrors';

export async function POST(
  request: NextRequest,
  { params }: { params: Promise<{ id: string }> },
) {
  try {
    const { id } = await params;

    if (!id) {
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: 'Session ID is required' },
        { status: 400 },
      );
    }

    // Delegate to handler → service → DAO → logger
    const updatedSession = await ApproveSessionHandler.handle(id);

    return NextResponse.json(updatedSession, { status: 200 });
  } catch (error) {
    if (error instanceof StateTransitionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    if (error instanceof PersistenceError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[sessions/approve] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
