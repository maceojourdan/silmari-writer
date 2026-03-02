/**
 * CompleteOnboardingStepResponse.test.ts - Step 6: Success Response
 *
 * TLA+ Properties:
 * - Reachability: Full request -> expect 200 { status: "completed" }
 * - TypeInvariant: Response matches CompleteOnboardingStepResponseSchema
 * - ErrorConsistency: Handler throw -> appropriate error response; idempotency (409)
 *
 * Tests the POST /api/onboarding/complete route handler to verify it returns
 * a well-formed success response, validates the response against the Zod schema,
 * and handles error and idempotency cases correctly.
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import {
  CompleteOnboardingStepResponseSchema,
} from '@/server/data_structures/Onboarding';
import {
  BackendError,
} from '@/server/error_definitions/BackendErrors';

// ---------------------------------------------------------------------------
// Mock Handler (the endpoint delegates to this)
// ---------------------------------------------------------------------------

vi.mock('@/server/request_handlers/CompleteOnboardingStepHandler', () => ({
  CompleteOnboardingStepHandler: {
    handle: vi.fn(),
  },
}));

import { CompleteOnboardingStepHandler } from '@/server/request_handlers/CompleteOnboardingStepHandler';
import { POST } from '@/app/api/onboarding/complete/route';

const mockHandler = vi.mocked(CompleteOnboardingStepHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function createMockRequest(body: unknown, headers: Record<string, string> = {}) {
  return new NextRequest('http://localhost:3000/api/onboarding/complete', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', ...headers },
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const validBody = {
  userId: 'user-resp-001',
  step: 1,
  metadata: { step: 1 },
};

const onboardingId = '550e8400-e29b-41d4-a716-446655440099';

const handlerSuccessResult = {
  status: 'completed' as const,
  onboardingId,
  step: 1,
  analyticsRecorded: true,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/onboarding/complete - Step 6: Success Response', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with status "completed" on successful request', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.status).toBe('completed');
    });

    it('should return full response payload with onboardingId, step, and analyticsRecorded', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(data).toEqual({
        status: 'completed',
        onboardingId,
        step: 1,
        analyticsRecorded: true,
      });
    });

    it('should return analyticsRecorded: false when analytics persistence failed', async () => {
      mockHandler.handle.mockResolvedValue({
        ...handlerSuccessResult,
        analyticsRecorded: false,
      });

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.status).toBe('completed');
      expect(data.analyticsRecorded).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a response matching CompleteOnboardingStepResponseSchema', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      const parsed = CompleteOnboardingStepResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });

    it('should return valid schema for step 2 completion', async () => {
      const step2Result = {
        status: 'completed' as const,
        onboardingId: '660e8400-e29b-41d4-a716-446655440077',
        step: 2,
        analyticsRecorded: true,
      };
      mockHandler.handle.mockResolvedValue(step2Result);

      const request = createMockRequest(
        { userId: 'user-resp-002', step: 2 },
        { Authorization: 'Bearer test-token-abc123' },
      );
      const response = await POST(request);
      const data = await response.json();

      const parsed = CompleteOnboardingStepResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
      expect(data.step).toBe(2);
    });

    it('should return 500 when handler produces a response that fails schema validation', async () => {
      mockHandler.handle.mockResolvedValue({
        status: 'bad-status',
        onboardingId: 'not-a-uuid',
        step: -1,
        analyticsRecorded: 'not-boolean',
      } as never);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
      expect(data.message).toBe('Failed to construct valid response');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return appropriate error response when handler throws a BackendError', async () => {
      mockHandler.handle.mockRejectedValue(
        new BackendError('Persistence failed', 'PERSISTENCE_FAILED', 500, true),
      );

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('PERSISTENCE_FAILED');
      expect(data.message).toBe('Persistence failed');
    });

    it('should return 409 for STEP_ALREADY_COMPLETED (idempotency)', async () => {
      mockHandler.handle.mockRejectedValue(
        new BackendError(
          'Onboarding step 1 already completed for user',
          'STEP_ALREADY_COMPLETED',
          409,
          false,
        ),
      );

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(409);
      expect(data.code).toBe('STEP_ALREADY_COMPLETED');
    });

    it('should return 500 with INTERNAL_ERROR for unexpected (non-BackendError) exceptions', async () => {
      mockHandler.handle.mockRejectedValue(new TypeError('Cannot read properties of undefined'));

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
      expect(data.message).toBe('An unexpected error occurred');
    });

    it('should return 422 for USER_NOT_ELIGIBLE error from handler', async () => {
      mockHandler.handle.mockRejectedValue(
        new BackendError('User is not eligible', 'USER_NOT_ELIGIBLE', 422, false),
      );

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-abc123',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('USER_NOT_ELIGIBLE');
    });

    it('should return 500 for KPI_IDENTIFIER_MISSING error from handler', async () => {
      mockHandler.handle.mockRejectedValue(
        new BackendError('No KPI identifier found for step 99', 'KPI_IDENTIFIER_MISSING', 500, false),
      );

      const request = createMockRequest(
        { userId: 'user-resp-001', step: 99 },
        { Authorization: 'Bearer test-token-abc123' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('KPI_IDENTIFIER_MISSING');
    });
  });
});
