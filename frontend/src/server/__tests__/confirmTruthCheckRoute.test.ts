/**
 * Integration test for POST /api/truth-checks/confirm route
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Properties tested:
 * - Reachability: POST valid body → handler invoked with normalized command
 * - TypeInvariant: Zod schema validation for request body
 * - ErrorConsistency: POST missing status → 400 with structured error
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import { TruthCheckService } from '@/server/services/TruthCheckService';
import type { ConfirmResult } from '@/server/data_structures/TruthCheck';

vi.mock('@/server/services/TruthCheckService', () => ({
  TruthCheckService: {
    confirm: vi.fn(),
  },
}));

const mockService = vi.mocked(TruthCheckService);

// Helper to create a NextRequest with JSON body
function createRequest(body: unknown): NextRequest {
  return new NextRequest('http://localhost:3000/api/truth-checks/confirm', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

const successResult: ConfirmResult = {
  id: 'tc-001',
  claim_id: 'claim-001',
  status: 'confirmed',
  source: 'Annual Revenue Report 2025',
  created_at: '2026-02-28T12:00:00.000Z',
};

describe('POST /api/truth-checks/confirm', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: valid request → handler invoked', () => {
    it('should return 200 with persisted result on valid request', async () => {
      mockService.confirm.mockResolvedValue(successResult);

      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.claim_id).toBe('claim-001');
      expect(data.status).toBe('confirmed');
      expect(data.source).toBe('Annual Revenue Report 2025');
    });

    it('should pass validated data to service', async () => {
      mockService.confirm.mockResolvedValue(successResult);

      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
      });

      await POST(request);

      expect(mockService.confirm).toHaveBeenCalledTimes(1);
    });
  });

  describe('TypeInvariant: Zod schema validation', () => {
    it('should validate claim_id is a non-empty string', async () => {
      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: '',
        status: 'confirmed',
        source: 'Some source',
      });

      const response = await POST(request);

      expect(response.status).toBe(400);
      const data = await response.json();
      expect(data.code).toBe('TRUTH_CHECK_VALIDATION_ERROR');
    });

    it('should validate status is confirmed or denied', async () => {
      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        status: 'invalid_status',
        source: 'Some source',
      });

      const response = await POST(request);

      expect(response.status).toBe(400);
      const data = await response.json();
      expect(data.code).toBe('TRUTH_CHECK_VALIDATION_ERROR');
    });

    it('should validate source is a non-empty string', async () => {
      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: '',
      });

      const response = await POST(request);

      expect(response.status).toBe(400);
      const data = await response.json();
      expect(data.code).toBe('TRUTH_CHECK_VALIDATION_ERROR');
    });

    it('should accept denied status', async () => {
      const deniedResult: ConfirmResult = {
        ...successResult,
        status: 'denied',
      };
      mockService.confirm.mockResolvedValue(deniedResult);

      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        status: 'denied',
        source: 'Some source',
      });

      const response = await POST(request);

      expect(response.status).toBe(200);
    });
  });

  describe('ErrorConsistency: missing/invalid fields → structured error', () => {
    it('should return 400 when status is missing', async () => {
      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        source: 'Some source',
      });

      const response = await POST(request);

      expect(response.status).toBe(400);
      const data = await response.json();
      expect(data.code).toBe('TRUTH_CHECK_VALIDATION_ERROR');
      expect(data.message).toBeDefined();
    });

    it('should return 400 when claim_id is missing', async () => {
      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        status: 'confirmed',
        source: 'Some source',
      });

      const response = await POST(request);

      expect(response.status).toBe(400);
      const data = await response.json();
      expect(data.code).toBe('TRUTH_CHECK_VALIDATION_ERROR');
    });

    it('should return structured error from service failures', async () => {
      const { TruthCheckErrors } = await import('@/server/error_definitions/TruthCheckErrors');
      mockService.confirm.mockRejectedValue(
        TruthCheckErrors.PERSISTENCE_ERROR('DB write failed'),
      );

      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Some source',
      });

      const response = await POST(request);

      expect(response.status).toBe(500);
      const data = await response.json();
      expect(data.code).toBe('TRUTH_CHECK_PERSISTENCE_ERROR');
    });

    it('should return 500 on unexpected errors', async () => {
      mockService.confirm.mockRejectedValue(new Error('Something went wrong'));

      const { POST } = await import('@/app/api/truth-checks/confirm/route');
      const request = createRequest({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Some source',
      });

      const response = await POST(request);

      expect(response.status).toBe(500);
      const data = await response.json();
      expect(data.code).toBe('INTERNAL_ERROR');
    });
  });
});
