import { NextResponse } from 'next/server';
import { z } from 'zod';
import { GetSessionHandler } from '@/server/request_handlers/GetSessionHandler';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import { SessionViewSchema } from '@/server/data_structures/SessionView';

const SessionIdSchema = z.string().uuid();

export async function GET(
  _request: Request,
  { params }: { params: Promise<{ id: string }> },
) {
  try {
    const { id } = await params;

    const parsedId = SessionIdSchema.safeParse(id);
    if (!parsedId.success) {
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: 'Session ID must be a valid UUID' },
        { status: 400 },
      );
    }

    const session = await GetSessionHandler.handle(parsedId.data);

    const parsedResponse = SessionViewSchema.safeParse(session);
    if (!parsedResponse.success) {
      return NextResponse.json(
        { code: 'INTERNAL_ERROR', message: 'Failed to construct valid session response' },
        { status: 500 },
      );
    }

    return NextResponse.json(parsedResponse.data, { status: 200 });
  } catch (error) {
    if (error instanceof SessionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[sessions/[id]] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}

