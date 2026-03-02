/**
 * POST /api/onboarding/complete
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * Completes an onboarding step and records the corresponding leading KPI
 * analytics event. Validates auth header and request body via Zod schema,
 * then delegates to CompleteOnboardingStepHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { CompleteOnboardingStepHandler } from '@/server/request_handlers/CompleteOnboardingStepHandler';
import { BackendError } from '@/server/error_definitions/BackendErrors';
import {
  CompleteOnboardingStepRequestSchema,
  CompleteOnboardingStepResponseSchema,
} from '@/server/data_structures/Onboarding';

export async function POST(request: NextRequest) {
  try {
    // 1. Authenticate
    const authHeader = request.headers.get('authorization');
    if (!authHeader || authHeader.trim() === '') {
      return NextResponse.json(
        { code: 'UNAUTHORIZED', message: 'Missing or empty authorization header' },
        { status: 401 },
      );
    }

    // 2. Parse and validate request body
    let body: unknown;
    try {
      body = await request.json();
    } catch {
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: 'Invalid JSON in request body' },
        { status: 400 },
      );
    }

    const parsed = CompleteOnboardingStepRequestSchema.safeParse(body);
    if (!parsed.success) {
      return NextResponse.json(
        {
          code: 'INVALID_REQUEST',
          message: `Request validation failed: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
        },
        { status: 400 },
      );
    }

    const { userId, step, metadata } = parsed.data;

    // 3. Delegate to handler → processor → service → DAO
    const result = await CompleteOnboardingStepHandler.handle(
      userId,
      step,
      metadata,
    );

    // 4. Validate response before sending
    const validation = CompleteOnboardingStepResponseSchema.safeParse({
      status: result.status,
      onboardingId: result.onboardingId,
      step: result.step,
      analyticsRecorded: result.analyticsRecorded,
    });

    if (!validation.success) {
      console.error(
        '[onboarding/complete] Response validation failed:',
        validation.error,
      );
      return NextResponse.json(
        { code: 'INTERNAL_ERROR', message: 'Failed to construct valid response' },
        { status: 500 },
      );
    }

    return NextResponse.json(validation.data, { status: 200 });
  } catch (error) {
    // Known backend errors
    if (error instanceof BackendError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors
    console.error('[onboarding/complete] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
