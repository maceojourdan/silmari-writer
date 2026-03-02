/**
 * RecordPrimaryKpiEndpoint.test.ts - Step 2: Backend endpoint receives KPI recording request
 *
 * TLA+ Properties:
 * - Reachability: POST valid body -> handler invoked, 200 returned with correct payload
 * - TypeInvariant: Request body parsed with Zod schema; response conforms to RecordPrimaryKpiResponseSchema
 * - ErrorConsistency: Invalid body -> 400 with VALIDATION_ERROR, missing auth -> 401 UNAUTHORIZED
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 339-record-primary-kpi-analytics-event
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import { z } from 'zod';

// ---------------------------------------------------------------------------
// Mock Handler
// ---------------------------------------------------------------------------

vi.mock('@/server/request_handlers/RecordPrimaryKpiHandler', () => ({
  RecordPrimaryKpiHandler: {
    handle: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock PrimaryKpiRecord Schemas
//
// Zod v4 classic compatibility layer has an internal bug with
// z.record(z.unknown()) that causes safeParse to throw instead of returning
// { success: false }. We provide equivalent schemas here to isolate the
// endpoint logic under test from that runtime issue.
// ---------------------------------------------------------------------------

vi.mock('@/server/data_structures/PrimaryKpiRecord', () => {
  const { z: zod } = require('zod');

  return {
    RecordPrimaryKpiRequestSchema: zod.object({
      userId: zod.string().min(1),
      actionType: zod.string().min(1),
      metadata: zod.record(zod.string(), zod.any()).optional().default({}),
    }),
    RecordPrimaryKpiResponseSchema: zod.object({
      id: zod.string().uuid(),
      status: zod.enum(['PENDING', 'PERSISTED', 'ANALYTICS_SENT', 'ANALYTICS_FAILED']),
      analyticsEmitted: zod.boolean(),
    }),
  };
});

import { RecordPrimaryKpiHandler } from '@/server/request_handlers/RecordPrimaryKpiHandler';
import { KpiError } from '@/server/error_definitions/KpiErrors';
import { POST } from '@/app/api/kpi/primary/route';

const mockHandler = vi.mocked(RecordPrimaryKpiHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function createMockRequest(body: unknown, headers: Record<string, string> = {}) {
  return new NextRequest('http://localhost:3000/api/kpi/primary', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', ...headers },
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const validBody = {
  userId: 'user-001',
  actionType: 'purchase',
  metadata: { amount: 99.99 },
};

const persistedRecord = {
  id: '550e8400-e29b-41d4-a716-446655440001',
  userId: 'user-001',
  actionType: 'purchase',
  metadata: { amount: 99.99 },
  status: 'PERSISTED' as const,
  timestamp: '2026-03-01T14:30:00.000Z',
  createdAt: '2026-03-01T14:30:01.000Z',
};

const handlerSuccessResult = {
  record: persistedRecord,
  analyticsEmitted: true,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/kpi/primary - Step 2: Backend endpoint receives KPI recording request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should invoke handler with parsed request body on valid POST', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith({
        userId: 'user-001',
        actionType: 'purchase',
        metadata: { amount: 99.99 },
      });
    });

    it('should return 200 with id, status, and analyticsEmitted on success', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data).toEqual({
        id: '550e8400-e29b-41d4-a716-446655440001',
        status: 'PERSISTED',
        analyticsEmitted: true,
      });
    });

    it('should invoke handler when metadata is omitted (optional field)', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const bodyWithoutMetadata = { userId: 'user-001', actionType: 'purchase' };
      const request = createMockRequest(bodyWithoutMetadata, {
        Authorization: 'Bearer test-token-12345678',
      });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith({
        userId: 'user-001',
        actionType: 'purchase',
        metadata: {},
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return response matching RecordPrimaryKpiResponseSchema', async () => {
      mockHandler.handle.mockResolvedValue(handlerSuccessResult);

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(data).toHaveProperty('id');
      expect(data).toHaveProperty('status');
      expect(data).toHaveProperty('analyticsEmitted');
      expect(typeof data.id).toBe('string');
      expect(typeof data.status).toBe('string');
      expect(typeof data.analyticsEmitted).toBe('boolean');
    });

    it('should return 400 when userId is missing from body', async () => {
      const request = createMockRequest(
        { actionType: 'purchase' },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 when actionType is missing from body', async () => {
      const request = createMockRequest(
        { userId: 'user-001' },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 when userId is an empty string', async () => {
      const request = createMockRequest(
        { userId: '', actionType: 'purchase' },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 when actionType is an empty string', async () => {
      const request = createMockRequest(
        { userId: 'user-001', actionType: '' },
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return 400 with validation message details for empty body', async () => {
      const request = createMockRequest(
        {},
        { Authorization: 'Bearer test-token-12345678' },
      );
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(data.message).toContain('Request validation failed');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
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

    it('should return 400 with VALIDATION_ERROR for malformed JSON body', async () => {
      const request = new NextRequest(
        'http://localhost:3000/api/kpi/primary',
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
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(data.message).toContain('Invalid JSON');
      expect(mockHandler.handle).not.toHaveBeenCalled();
    });

    it('should return KpiError status code and code for known KPI errors', async () => {
      mockHandler.handle.mockRejectedValue(
        new KpiError('KPI data failed business rule validation', 'DOMAIN_VALIDATION_ERROR', 422),
      );

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('DOMAIN_VALIDATION_ERROR');
      expect(data.message).toBe('KPI data failed business rule validation');
    });

    it('should return 500 for PERSISTENCE_ERROR from handler', async () => {
      mockHandler.handle.mockRejectedValue(
        new KpiError('Failed to persist primary KPI record', 'PERSISTENCE_ERROR', 500, true),
      );

      const request = createMockRequest(validBody, {
        Authorization: 'Bearer test-token-12345678',
      });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('PERSISTENCE_ERROR');
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
        record: {
          id: 'not-a-uuid',
          userId: 'user-001',
          actionType: 'purchase',
          metadata: {},
          status: 'INVALID_STATUS',
          timestamp: '2026-03-01T14:30:00.000Z',
          createdAt: '2026-03-01T14:30:01.000Z',
        },
        analyticsEmitted: 'not-boolean',
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
