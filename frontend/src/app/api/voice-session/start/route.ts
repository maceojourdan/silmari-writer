/**
 * POST /api/voice-session/start
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 *
 * Delegates to StartVoiceSessionHandler for consent validation:
 * handler → service → response.
 */

import { NextRequest, NextResponse } from 'next/server';
import { StartVoiceSessionHandler } from '@/server/request_handlers/StartVoiceSessionHandler';
import { ConsentError } from '@/server/error_definitions/ConsentErrors';

export async function POST(request: NextRequest) {
  try {
    const body = await request.json();

    const result = await StartVoiceSessionHandler.handle({
      consent: body.consent,
    });

    return NextResponse.json(
      { sessionStatus: result.sessionStatus },
      { status: 200 },
    );
  } catch (error) {
    if (error instanceof ConsentError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[voice-session/start] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
