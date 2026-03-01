/**
 * POST /api/sms/dispute
 *
 * Receives inbound SMS dispute webhooks and processes them
 * to mark disputed claims as not_verified and block drafting.
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 322-handle-disputed-claims-and-block-drafting
 *
 * Validates the webhook payload, then delegates to the request handler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { parseSmsDisputeWebhook } from '@/server/endpoints/smsDisputeWebhook';
import { HandleSmsDisputeRequestHandler } from '@/server/request_handlers/HandleSmsDisputeRequestHandler';
import { DisputeError } from '@/server/error_definitions/DisputeErrors';

export async function POST(request: NextRequest) {
  try {
    // Parse request body
    const payload = await request.json();

    // Step 1: Validate and parse webhook
    const disputeData = await parseSmsDisputeWebhook(payload);

    // Step 2-4: Handle dispute (mark claims, block drafting)
    const result = await HandleSmsDisputeRequestHandler.handle(disputeData);

    return NextResponse.json(
      {
        status: 'ok',
        claimsUpdated: result.updatedClaims.length,
        caseBlocked: result.caseBlocked,
      },
      { status: 200 },
    );
  } catch (error) {
    if (error instanceof DisputeError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[sms/dispute] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
