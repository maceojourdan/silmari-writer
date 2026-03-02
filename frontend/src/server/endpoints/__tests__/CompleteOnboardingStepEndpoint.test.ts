/**
 * CompleteOnboardingStepEndpoint.test.ts - Step 2: Backend endpoint receives completion request
 *
 * TLA+ Properties:
 * - Reachability: POST valid body -> handler invoked, 200 returned with correct payload
 * - TypeInvariant: Request body parsed with Zod schema (validated internally by endpoint)
 * - ErrorConsistency: Malformed body -> 400 with INVALID_REQUEST, processor not invoked
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import { z } from 'zod';

// ---------------------------------------------------------------------------
// Mock Handler
// ---------------------------------------------------------------------------

vi.mock('@/server/request_handlers/CompleteOnboardingStepHandler', () => ({
  CompleteOnboardingStepHandler: {
    handle: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock Onboarding Schemas
//
// Zod v4 classic compatibility layer has an internal bug with
// z.record(z.unknown()) that causes safeParse to throw instead of returning
// { success: false }. We provide equivalent schemas here to isolate the
// endpoint logic under test from that runtime issue.
// ---------------------------------------------------------------------------

vi.mock('@/server/data_structures/Onboarding', () => {
  const { z: zod } = require('zod');

  return {
    CompleteOnboardingStepRequestSchema: zod.object({
      userId: zod.string().min(1),
      step: zod.number().int().min(1),
      metadata: zod.record(zod.string(), zod.any()).optional(),
    }),
    CompleteOnboardingStepResponseSchema: zod.object({
      status: zod.literal('completed'),
      onboardingId: zod.string().uuid(),
      step: zod.number().int().min(1),
      analyticsRecorded: zod.boolean(),
    }),
  };
});

import { CompleteOnboardingStepHandler } from '@/server/request_handlers/CompleteOnboardingStepHandler';
import { BackendError } from '@/server/error_definitions/BackendErrors';
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
  userId: 'user-abc-123',
  step: 1,
  metadata: { source: 'welcome-flow' },
};

const onboardingId = '550e8400-e29b-41d4-a716-446655440000';

const handlerSuccessResult = {
  status: 'completed' as const,
  onboardingId,
  step: 1,
  analyticsRecorded: true,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/onboarding/complete - Step 2: Backend endpoint receives completion request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should invoke handler with userId, step, and metadata from request body', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith(
        validBody.userId,
        validBody.step,
        validBody.metadata,
      );
    });

    it('should return 200 with correct response payload on success', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data).toEqual({
        status: 'completed',
        onboardingId,
        step: 1,
        analyticsRecorded: true,
      });
    });

    it('should invoke handler when metadata is omitted (optional field)', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const bodyWithoutMetadata = { userId: 'user-abc-123', step: 1 };
      const request = createMockRequest(bodyWithoutMetadata, {
        Authorization: 'Bearer test-token-12345678',
      });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith(
        'user-abc-123',
        1,
        undefined,
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return 400 when userId is missing from body', async () => {
      const request = createMockRequest(
        { step: 1 },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 when step is missing from body', async () => {
      const request = createMockRequest(
        { userId: 'user-abc-123' },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 when step is not a positive integer', async () => {
      const request = createMockRequest(
        { userId: 'user-abc-123', step: 0 },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 when userId is an empty string', async () => {
      const request = createMockRequest(
        { userId: '', step: 1 },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 with validation message details', async () => {
      const request = createMockRequest(
        { step: 'not-a-number' },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(data.message).toContain('Request validation failed');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 400 with INVALID_REQUEST for malformed JSON body', async () => {
      const request = new NextRequest(
        'http://localhost:3000/api/onboarding/complete',
        {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
            Authorization: 'Bearer test-token-12345678',
          },
          body: '{ invalid json',
        },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(data.message).toContain('Invalid JSON');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 401 when authorization header is missing', async () => {
      const request = createMockRequest(validBody);
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 401 when authorization header is empty', async () => {
      const request = createMockRequest(validBody, { Authorization: '   ' });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return BackendError status code and code for known errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new BackendError('User is not eligible', 'USER_NOT_ELIGIBLE', 422),
      );

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('USER_NOT_ELIGIBLE');
      expect(data.message).toBe('User is not eligible');
    });

    it('should return 409 for STEP_ALREADY_COMPLETED errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new BackendError('Step already completed', 'STEP_ALREADY_COMPLETED', 409),
      );

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(409);
      expect(data.code).toBe('STEP_ALREADY_COMPLETED');
    });

    it('should return 500 with INTERNAL_ERROR for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Unexpected DB failure'));

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
      expect(data.message).toBe('An unexpected error occurred');
    });

    it('should return 500 when handler result fails response schema validation', async () => {
      mockHandler.handle.mockResolvedValue({
        status: 'invalid-status',
        onboardingId: 'not-a-uuid',
        step: -1,
        analyticsRecorded: 'not-boolean',
      } as never);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
      expect(data.message).toBe('Failed to construct valid response');
    });

    it('should not invoke handler when body validation fails', async () => {
      const request = createMockRequest(
        { invalid: 'data' },
        { Authorization: 'Bearer test-token-12345678' },
      );
      await POST(request);

      expect(mockHandler.handle).not.toHaveBeenCalled();
    });
  });
});
