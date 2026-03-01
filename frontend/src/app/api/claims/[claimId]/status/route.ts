/**
 * GET /api/claims/[claimId]/status
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * Serves the current claim verification and drafting status
 * so the frontend can retrieve and reflect the updated state.
 */

import { NextResponse } from 'next/server';
import { GetClaimStatusHandler } from '@/server/request_handlers/GetClaimStatusHandler';
import { DomainError } from '@/server/error_definitions/DomainErrors';
import { logger } from '@/server/logging/logger';

const PATH = '324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold';
const RESOURCE = 'api-m5g7';

export async function GET(
  _request: Request,
  { params }: { params: Promise<{ claimId: string }> },
) {
  try {
    const { claimId } = await params;

    if (!claimId || claimId.trim() === '') {
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: 'claimId is required' },
        { status: 400 },
      );
    }

    const result = await GetClaimStatusHandler.handle(claimId);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    // Known DomainError → map to HTTP response
    if (error instanceof DomainError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Unknown error → 500 generic failure
    logger.error(
      'Unexpected error in /api/claims/[claimId]/status',
      error,
      { path: PATH, resource: RESOURCE },
    );

    return NextResponse.json(
      { code: 'CLAIM_STATUS_LOAD_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
