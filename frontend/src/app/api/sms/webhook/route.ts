/**
 * POST /api/sms/webhook
 *
 * Receives inbound SMS replies from Twilio and processes them
 * as truth-check updates for claims.
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 305-followup-sms-for-uncertain-claim
 *
 * Validates the request body and delegates to SmsWebhookHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { SmsWebhookHandler } from '@/server/request_handlers/SmsWebhookHandler';
import { WebhookError } from '@/server/error_definitions/WebhookErrors';
import { SmsError } from '@/server/error_definitions/SmsErrors';

export async function POST(request: NextRequest) {
  try {
    // Twilio sends form-encoded data or JSON
    let payload: unknown;

    const contentType = request.headers.get('content-type') || '';
    if (contentType.includes('application/x-www-form-urlencoded')) {
      const formData = await request.formData();
      payload = Object.fromEntries(formData.entries());
    } else {
      payload = await request.json();
    }

    // Delegate to handler
    const updatedClaim = await SmsWebhookHandler.handle(payload);

    // Twilio expects TwiML or 200 OK
    return NextResponse.json(
      { status: 'ok', claimId: updatedClaim.id, newStatus: updatedClaim.status },
      { status: 200 },
    );
  } catch (error) {
    if (error instanceof WebhookError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    if (error instanceof SmsError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[sms/webhook] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
