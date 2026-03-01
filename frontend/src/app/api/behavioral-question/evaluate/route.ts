/**
 * POST /api/behavioral-question/evaluate
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Validates the request body and delegates to BehavioralQuestionEvaluateHandler.
 */

import { NextRequest, NextResponse } from 'next/server';
import { BehavioralQuestionEvaluateHandler } from '@/server/request_handlers/BehavioralQuestionEvaluateHandler';
import { BehavioralQuestionError } from '@/server/error_definitions/BehavioralQuestionErrors';
import { z } from 'zod';

/**
 * Zod schema for validating the request body.
 */
const EvaluateRequestSchema = z.object({
  sessionId: z.string().min(1, 'sessionId is required'),
  objective: z.string().min(1, 'objective is required'),
  actions: z.array(z.string().min(1)).min(1, 'at least one action is required'),
  obstacles: z.array(z.string().min(1)).min(1, 'at least one obstacle is required'),
  outcome: z.string().min(1, 'outcome is required'),
  roleClarity: z.string().min(1, 'roleClarity is required'),
});

export async function POST(request: NextRequest) {
  try {
    // 1. Parse and validate body
    const rawBody = await request.json();
    const validation = EvaluateRequestSchema.safeParse(rawBody);

    if (!validation.success) {
      const details = validation.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      return NextResponse.json(
        { code: 'VALIDATION_ERROR', message: `Invalid request: ${details}` },
        { status: 400 },
      );
    }

    // 2. Handle request → service → DAO
    const result = await BehavioralQuestionEvaluateHandler.handle(validation.data);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    if (error instanceof BehavioralQuestionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[behavioral-question/evaluate] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
