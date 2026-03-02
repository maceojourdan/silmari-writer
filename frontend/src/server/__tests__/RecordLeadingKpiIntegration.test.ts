/**
 * RecordLeadingKpiIntegration.test.ts — Integration (Terminal Condition)
 *
 * Full integration test for the record-leading-kpi-analytics-event path.
 * Only the DAO layer is mocked (database boundary). Everything above runs
 * with real implementations: route handler -> handler -> processor -> service -> DAO.
 *
 * Proves:
 * - Reachability: POST request -> handler -> processor -> service -> DAO -> 200 response
 * - TypeInvariant: Response matches CompleteOnboardingStepResponseSchema
 * - ErrorConsistency: All error branches return structured error objects
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import {
  CompleteOnboardingStepResponseSchema,
} from '@/server/data_structures/Onboarding';
import { AnalyticsEventInsertSchema } from '@/server/data_structures/AnalyticsEvent';
import type { AnalyticsEvent } from '@/server/data_structures/AnalyticsEvent';
import type { Onboarding } from '@/server/data_structures/Onboarding';

// ---------------------------------------------------------------------------
// Only mock the DAO layer (database boundary) and logger
// Everything else (route, handler, processor, service) runs with real code
// ---------------------------------------------------------------------------

vi.mock('../data_access_objects/OnboardingDao', () => ({
  OnboardingDao: {
    findByUserAndStep: vi.fn(),
    updateOnboardingStep: vi.fn(),
    createOnboarding: vi.fn(),
    insertAnalyticsEvent: vi.fn(),
    findAnalyticsEvent: vi.fn(),
  },
}));

vi.mock('../logging/onboardingLogger', () => ({
  onboardingLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

import { OnboardingDao } from '../data_access_objects/OnboardingDao';
import { onboardingLogger } from '../logging/onboardingLogger';
import { POST } from '@/app/api/onboarding/complete/route';

const mockDao = vi.mocked(OnboardingDao);
const mockLogger = vi.mocked(onboardingLogger);

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

const userId = 'user-integration-001';
const step = 1;
const onboardingId = '550e8400-e29b-41d4-a716-446655440050';
const completedAt = '2026-03-01T14:30:00.000Z';

const updatedOnboardingRecord: Onboarding = {
  id: onboardingId,
  userId,
  step,
  status: 'COMPLETED',
  completedAt,
  createdAt: '2026-03-01T14:00:00.000Z',
  updatedAt: completedAt,
};

const persistedAnalyticsEvent: AnalyticsEvent = {
  id: '770e8400-e29b-41d4-a716-446655440060',
  kpiId: 'leading_kpi.onboarding_step_1',
  userId,
  timestamp: completedAt,
  metadata: { step: 1 },
  createdAt: '2026-03-01T14:30:01.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Record Leading KPI Analytics Event — Integration (Terminal Condition)', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default mocks: user not yet completed this step, update succeeds, analytics insert succeeds
    mockDao.findByUserAndStep.mockResolvedValue(null);
    mockDao.updateOnboardingStep.mockResolvedValue(updatedOnboardingRecord);
    mockDao.insertAnalyticsEvent.mockResolvedValue(persistedAnalyticsEvent);
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path from POST to 200 response
  // -------------------------------------------------------------------------

  describe('Reachability: POST -> Handler -> Processor -> Service -> DAO -> 200', () => {
    it('should complete onboarding step 1 and record analytics event', async () => {
      const request = createMockRequest(
        { userId, step: 1, metadata: { step: 1 } },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.status).toBe('completed');
      expect(data.analyticsRecorded).toBe(true);
    });

    it('should call OnboardingDao.findByUserAndStep to check eligibility', async () => {
      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockDao.findByUserAndStep).toHaveBeenCalledWith(userId, 1);
    });

    it('should call OnboardingDao.updateOnboardingStep with correct args', async () => {
      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockDao.updateOnboardingStep).toHaveBeenCalledTimes(1);
      const [calledUserId, calledStep, calledFields] =
        mockDao.updateOnboardingStep.mock.calls[0];
      expect(calledUserId).toBe(userId);
      expect(calledStep).toBe(1);
      expect(calledFields.status).toBe('COMPLETED');
      expect(calledFields.completedAt).toBeDefined();
      expect(calledFields.updatedAt).toBeDefined();
    });

    it('should call OnboardingDao.insertAnalyticsEvent with correct kpiId and userId', async () => {
      const request = createMockRequest(
        { userId, step: 1, metadata: { step: 1 } },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockDao.insertAnalyticsEvent).toHaveBeenCalledTimes(1);
      const insertArg = mockDao.insertAnalyticsEvent.mock.calls[0][0];
      expect(insertArg.kpiId).toBe('leading_kpi.onboarding_step_1');
      expect(insertArg.userId).toBe(userId);
      expect(insertArg.metadata).toEqual(expect.objectContaining({ step: 1 }));
    });

    it('should produce analytics event insert data with a valid timestamp', async () => {
      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      const insertArg = mockDao.insertAnalyticsEvent.mock.calls[0][0];
      expect(insertArg.timestamp).toBeDefined();
      // Timestamp should be a valid ISO date string
      expect(new Date(insertArg.timestamp).toISOString()).toBe(insertArg.timestamp);
    });

    it('should produce analytics event insert data passing AnalyticsEventInsertSchema', async () => {
      const request = createMockRequest(
        { userId, step: 1, metadata: { step: 1 } },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      const insertArg = mockDao.insertAnalyticsEvent.mock.calls[0][0];
      const parsed = AnalyticsEventInsertSchema.safeParse(insertArg);
      expect(parsed.success).toBe(true);
    });

    it('should return 200 with confirmation to the frontend', async () => {
      const request = createMockRequest(
        { userId, step: 1, metadata: { step: 1 } },
        { Authorization: 'Bearer integration-test-token' },
      );

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
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Response matches schema
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Response matches CompleteOnboardingStepResponseSchema', () => {
    it('should return a response conforming to the schema when analytics succeeds', async () => {
      const request = createMockRequest(
        { userId, step: 1, metadata: { step: 1 } },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      const parsed = CompleteOnboardingStepResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });

    it('should return a response conforming to the schema when analytics fails', async () => {
      mockDao.insertAnalyticsEvent.mockRejectedValue(new Error('DB unavailable'));

      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      const parsed = CompleteOnboardingStepResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
      expect(data.analyticsRecorded).toBe(false);
    });

    it('should have onboardingId as a valid UUID in the response', async () => {
      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      const uuidRegex =
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
      expect(data.onboardingId).toMatch(uuidRegex);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: All error branches return structured errors
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Structured error responses', () => {
    it('should return 401 when authorization header is missing', async () => {
      const request = createMockRequest({ userId, step: 1 });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
      expect(mockDao.findByUserAndStep).not.toHaveBeenCalled();
    });

    it('should return 400 for invalid request body', async () => {
      const request = createMockRequest(
        { step: 'not-a-number' },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      expect(mockDao.findByUserAndStep).not.toHaveBeenCalled();
    });

    it('should return 409 when step is already completed (idempotency)', async () => {
      mockDao.findByUserAndStep.mockResolvedValue({
        ...updatedOnboardingRecord,
        status: 'COMPLETED',
      });

      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(409);
      expect(data.code).toBe('STEP_ALREADY_COMPLETED');
      // DAO update should not have been attempted
      expect(mockDao.updateOnboardingStep).not.toHaveBeenCalled();
      expect(mockDao.insertAnalyticsEvent).not.toHaveBeenCalled();
    });

    it('should return 500 when onboarding persistence fails', async () => {
      mockDao.updateOnboardingStep.mockRejectedValue(new Error('Connection refused'));

      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      // Analytics should not have been attempted
      expect(mockDao.insertAnalyticsEvent).not.toHaveBeenCalled();
    });

    it('should return 200 with analyticsRecorded: false when analytics persistence fails but onboarding succeeds', async () => {
      mockDao.insertAnalyticsEvent.mockRejectedValue(new Error('Analytics DB timeout'));

      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.status).toBe('completed');
      expect(data.analyticsRecorded).toBe(false);

      // Logger should record the analytics failure
      expect(mockLogger.error).toHaveBeenCalledWith(
        'Failed to persist analytics event',
        expect.any(Error),
        expect.objectContaining({
          userId,
          step: 1,
          kpiId: 'leading_kpi.onboarding_step_1',
        }),
      );
    });

    it('should not leave partial state when the flow fails at the service layer', async () => {
      mockDao.updateOnboardingStep.mockRejectedValue(new Error('Transaction rolled back'));

      const request = createMockRequest(
        { userId, step: 1 },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      // No analytics event should have been created
      expect(mockDao.insertAnalyticsEvent).not.toHaveBeenCalled();
      // Only one attempt to update onboarding was made
      expect(mockDao.updateOnboardingStep).toHaveBeenCalledTimes(1);
    });
  });
});
