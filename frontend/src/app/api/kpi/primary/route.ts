/**
 * POST /api/kpi/primary
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * Records a primary KPI analytics event. Validates auth header and request
 * body via Zod schema, then delegates to RecordPrimaryKpiHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { RecordPrimaryKpiHandler } from '@/server/request_handlers/RecordPrimaryKpiHandler';
import { KpiError } from '@/server/error_definitions/KpiErrors';
import {
  RecordPrimaryKpiRequestSchema,
  RecordPrimaryKpiResponseSchema,
} from '@/server/data_structures/PrimaryKpiRecord';

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
        { code: 'VALIDATION_ERROR', message: 'Invalid JSON in request body' },
        { status: 400 },
      );
    }

    const parsed = RecordPrimaryKpiRequestSchema.safeParse(body);
    if (!parsed.success) {
      return NextResponse.json(
        {
          code: 'VALIDATION_ERROR',
          message: `Request validation failed: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
        },
        { status: 400 },
      );
    }

    // 3. Delegate to handler → service → DAO
    const result = await RecordPrimaryKpiHandler.handle(parsed.data);

    // 4. Validate response before sending
    const responseData = {
      id: result.record.id,
      status: result.record.status,
      analyticsEmitted: result.analyticsEmitted,
    };
    const validation = RecordPrimaryKpiResponseSchema.safeParse(responseData);

    if (!validation.success) {
      console.error(
        '[kpi/primary] Response validation failed:',
        validation.error,
      );
      return NextResponse.json(
        { code: 'INTERNAL_ERROR', message: 'Failed to construct valid response' },
        { status: 500 },
      );
    }

    return NextResponse.json(validation.data, { status: 200 });
  } catch (error) {
    // Known KPI errors
    if (error instanceof KpiError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    // Completely unexpected errors
    console.error('[kpi/primary] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
