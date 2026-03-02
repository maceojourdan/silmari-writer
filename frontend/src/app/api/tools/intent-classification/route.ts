import { NextRequest, NextResponse } from 'next/server';

import { IntentClassificationError } from '@/lib/types';

import {
  ClassificationApiError,
  DEFAULT_TIMEOUT_MS,
  classifyIntent,
} from './classifier';

/**
 * POST /api/tools/intent-classification
 * REQ_006.1: HTTP endpoint for intent classification
 */
export async function POST(request: NextRequest) {
  try {
    const body = await request.json();

    const { userMessage, conversationHistory, timeout } = body as {
      userMessage?: string;
      conversationHistory?: Array<{ role: 'user' | 'assistant'; content: string }>;
      timeout?: number;
    };

    if (!userMessage || typeof userMessage !== 'string') {
      return NextResponse.json(
        { error: 'userMessage is required and must be a string', code: 'INVALID_INPUT' },
        { status: 400 }
      );
    }

    if (!userMessage.trim()) {
      return NextResponse.json(
        { error: 'userMessage cannot be empty or whitespace only', code: 'INVALID_INPUT' },
        { status: 400 }
      );
    }

    // Validate conversationHistory if provided
    if (conversationHistory !== undefined) {
      if (!Array.isArray(conversationHistory)) {
        return NextResponse.json(
          { error: 'conversationHistory must be an array', code: 'VALIDATION_ERROR' },
          { status: 400 }
        );
      }

      for (const msg of conversationHistory) {
        if (
          typeof msg !== 'object' ||
          !msg ||
          !['user', 'assistant'].includes(msg.role) ||
          typeof msg.content !== 'string'
        ) {
          return NextResponse.json(
            { error: 'Invalid conversationHistory entry', code: 'VALIDATION_ERROR' },
            { status: 400 }
          );
        }
      }
    }

    const effectiveTimeout = typeof timeout === 'number' && timeout > 0 ? timeout : DEFAULT_TIMEOUT_MS;

    const result = await classifyIntent(userMessage, conversationHistory, effectiveTimeout);

    return NextResponse.json(result, { status: 200 });
  } catch (error) {
    if (error instanceof IntentClassificationError) {
      const statusCode = error.code === 'INVALID_INPUT' ? 400 :
                         error.code === 'RATE_LIMIT' ? 429 :
                         error.code === 'TIMEOUT' ? 408 :
                         error.code === 'INVALID_API_KEY' ? 401 : 500;

      return NextResponse.json(
        { error: error.message, code: error.code, retryable: error.retryable },
        { status: statusCode }
      );
    }

    if (error instanceof ClassificationApiError) {
      return NextResponse.json(
        { error: error.message, code: error.code, retryable: error.retryable },
        { status: error.statusCode }
      );
    }

    console.error('[IntentClassification] Unexpected error:', error);
    return NextResponse.json(
      { error: 'Internal server error', code: 'API_ERROR', retryable: true },
      { status: 500 }
    );
  }
}
