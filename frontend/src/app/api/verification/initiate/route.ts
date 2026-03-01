/**
 * POST /api/verification/initiate
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 323-fail-verification-when-no-contact-method
 *
 * Validates the request body (claimantId as UUID) and delegates
 * to InitiateVerificationHandler for Path 323 orchestration.
 */

import { NextResponse } from 'next/server';
import { InitiateVerificationHandler } from '@/server/request_handlers/InitiateVerificationHandler';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import { InitiateVerificationRequestSchema } from '@/server/data_structures/VerificationAttempt';
import { verificationLogger } from '@/server/logging/verificationLogger';

export async function POST(request: Request) {
  try {
    // 1. Parse and validate body
    const rawBody = await request.json();
    const validation = InitiateVerificationRequestSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'VERIFICATION_REQUEST_INVALID', message: `Invalid request: ${details}` },
        { status: 400 },
      );
    }

    // 2. Handle request → handler → service → DAO
    const result = await InitiateVerificationHandler.handle(validation.data);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known VerificationError → map to HTTP response
    if (error instanceof VerificationError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Unknown error → 500 generic failure
    verificationLogger.error(
      'Unexpected error in /api/verification/initiate',
      error,
      {
        path: '323-fail-verification-when-no-contact-method',
        resource: 'api-m5g7',
      },
    );

    return NextResponse.json(
      { code: 'GENERIC_VERIFICATION_FAILURE', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
