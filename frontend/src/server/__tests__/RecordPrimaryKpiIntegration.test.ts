/**
 * RecordPrimaryKpiIntegration.test.ts -- Integration (Terminal Condition)
 *
 * Full integration test for the record-primary-kpi-analytics-event path.
 * Only the DAO layer, logger, and analytics client are mocked (database/external
 * boundaries). Everything above runs with real implementations:
 * route handler -> handler -> service -> verifier -> DAO + analyticsClient.
 *
 * Proves:
 * - Reachability: POST request -> handler -> service -> DAO -> analytics -> 200 response
 * - TypeInvariant: Response matches RecordPrimaryKpiResponseSchema
 * - ErrorConsistency: All error branches return structured error objects;
 *   failures do not produce false KPI events
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 339-record-primary-kpi-analytics-event
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

// ---------------------------------------------------------------------------
// Only mock the DAO layer (database boundary), logger, and analytics client
// Everything else (route, handler, service, verifier) runs with real code
// ---------------------------------------------------------------------------

vi.mock('../data_access_objects/PrimaryKpiDAO', () => ({
  PrimaryKpiDAO: {
    insert: vi.fn(),
    findById: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

vi.mock('../logging/kpiLogger', () => ({
  kpiLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

vi.mock('../services/analyticsClient', () => ({
  sendAnalyticsEvent: vi.fn(),
}));

import { PrimaryKpiDAO } from '../data_access_objects/PrimaryKpiDAO';
import { kpiLogger } from '../logging/kpiLogger';
import { sendAnalyticsEvent } from '../services/analyticsClient';
import { POST } from '@/app/api/kpi/primary/route';
import { RecordPrimaryKpiResponseSchema } from '../data_structures/PrimaryKpiRecord';

const mockDAO = vi.mocked(PrimaryKpiDAO);
const mockLogger = vi.mocked(kpiLogger);
const mockSendAnalytics = vi.mocked(sendAnalyticsEvent);

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

const userId = 'user-integration-001';
const actionType = 'purchase';
const metadata = { amount: 99.99, currency: 'USD' };

const persistedRecord = {
  id: '550e8400-e29b-41d4-a716-446655440001',
  userId,
  actionType,
  metadata,
  status: 'PERSISTED' as const,
  timestamp: '2026-03-01T14:30:00.000Z',
  createdAt: '2026-03-01T14:30:01.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Record Primary KPI Analytics Event -- Integration (Terminal Condition)', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default mocks: DAO insert succeeds, analytics emission succeeds, status update succeeds
    mockDAO.insert.mockResolvedValue(persistedRecord);
    mockDAO.updateStatus.mockResolvedValue({
      ...persistedRecord,
      status: 'ANALYTICS_SENT',
    });
    mockSendAnalytics.mockResolvedValue(undefined);
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path from POST to 200 response
  // -------------------------------------------------------------------------

  describe('Reachability: POST -> Handler -> Service -> DAO -> Analytics -> 200', () => {
    it('should return 200 for a valid request', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.id).toBe(persistedRecord.id);
      expect(data.analyticsEmitted).toBe(true);
    });

    it('should call PrimaryKpiDAO.insert with userId, actionType, and metadata', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockDAO.insert).toHaveBeenCalledTimes(1);
      const insertArg = mockDAO.insert.mock.calls[0][0];
      expect(insertArg.userId).toBe(userId);
      expect(insertArg.actionType).toBe(actionType);
      expect(insertArg.metadata).toEqual(metadata);
      expect(insertArg.status).toBe('PENDING');
      expect(insertArg.timestamp).toBeDefined();
    });

    it('should call sendAnalyticsEvent after successful persistence', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockDAO.insert).toHaveBeenCalledTimes(1);
      expect(mockSendAnalytics).toHaveBeenCalledTimes(1);
    });

    it('should send analytics payload with eventId matching the persisted record id', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockSendAnalytics).toHaveBeenCalledTimes(1);
      const payload = mockSendAnalytics.mock.calls[0][0];
      expect(payload.eventId).toBe(persistedRecord.id);
      expect(payload.userId).toBe(userId);
      expect(payload.actionType).toBe(actionType);
      expect(payload.metadata).toEqual(metadata);
      expect(payload.timestamp).toBeDefined();
    });

    it('should call PrimaryKpiDAO.updateStatus with ANALYTICS_SENT on analytics success', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockDAO.updateStatus).toHaveBeenCalledWith(
        persistedRecord.id,
        'ANALYTICS_SENT',
      );
    });

    it('should return response with id, status, and analyticsEmitted fields', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data).toEqual({
        id: persistedRecord.id,
        status: persistedRecord.status,
        analyticsEmitted: true,
      });
    });

    it('should return 200 with analyticsEmitted: false when analytics emission fails', async () => {
      mockSendAnalytics.mockRejectedValue(new Error('Analytics provider down'));

      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.analyticsEmitted).toBe(false);
      expect(data.id).toBe(persistedRecord.id);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Response matches RecordPrimaryKpiResponseSchema
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Response conforms to RecordPrimaryKpiResponseSchema', () => {
    it('should return a response conforming to the schema on full success', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      const parsed = RecordPrimaryKpiResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });

    it('should return a response conforming to the schema when analytics succeeds', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      const parsed = RecordPrimaryKpiResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
      expect(data.analyticsEmitted).toBe(true);
    });

    it('should return a response conforming to the schema when analytics fails (analyticsEmitted: false, still 200)', async () => {
      mockSendAnalytics.mockRejectedValue(new Error('Analytics timeout'));

      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      const parsed = RecordPrimaryKpiResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
      expect(data.analyticsEmitted).toBe(false);
    });

    it('should have id as a valid UUID in the response', async () => {
      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      const uuidRegex =
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
      expect(data.id).toMatch(uuidRegex);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: All error branches return structured errors;
  // failures do not produce false KPI events
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Structured error responses', () => {
    it('should return 401 when authorization header is missing', async () => {
      const request = createMockRequest({ userId, actionType, metadata });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
      expect(mockDAO.insert).not.toHaveBeenCalled();
      expect(mockSendAnalytics).not.toHaveBeenCalled();
    });

    it('should return 400 for invalid request body (missing userId)', async () => {
      const request = createMockRequest(
        { actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(mockDAO.insert).not.toHaveBeenCalled();
      expect(mockSendAnalytics).not.toHaveBeenCalled();
    });

    it('should return 400 for invalid request body (missing actionType)', async () => {
      const request = createMockRequest(
        { userId, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(mockDAO.insert).not.toHaveBeenCalled();
      expect(mockSendAnalytics).not.toHaveBeenCalled();
    });

    it('should return 422 when PrimaryKpiVerifier rejects (invalid actionType)', async () => {
      const request = createMockRequest(
        { userId, actionType: 'not_a_valid_action', metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(422);
      expect(data.code).toBe('DOMAIN_VALIDATION_ERROR');
      expect(mockDAO.insert).not.toHaveBeenCalled();
      expect(mockSendAnalytics).not.toHaveBeenCalled();
    });

    it('should return 500 when PrimaryKpiDAO.insert throws a persistence error', async () => {
      mockDAO.insert.mockRejectedValue(new Error('Connection refused'));

      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('PERSISTENCE_ERROR');
      // Analytics should not have been attempted
      expect(mockSendAnalytics).not.toHaveBeenCalled();
    });

    it('should return 200 when analytics fails (non-fatal) and log the failure', async () => {
      mockSendAnalytics.mockRejectedValue(new Error('Analytics provider timeout'));

      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.analyticsEmitted).toBe(false);

      // Logger should record the analytics failure
      expect(mockLogger.error).toHaveBeenCalledWith(
        'Analytics emission final_failure',
        expect.any(Error),
        expect.objectContaining({ recordId: persistedRecord.id }),
      );
    });

    it('should not call PrimaryKpiDAO.insert when validation fails at the route level (missing fields)', async () => {
      const request = createMockRequest(
        { metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      expect(mockDAO.insert).not.toHaveBeenCalled();
      expect(mockSendAnalytics).not.toHaveBeenCalled();
    });

    it('should not leave partial state: no analytics event when persistence fails', async () => {
      mockDAO.insert.mockRejectedValue(new Error('Transaction rolled back'));

      const request = createMockRequest(
        { userId, actionType, metadata },
        { Authorization: 'Bearer integration-test-token' },
      );

      await POST(request);

      // Analytics event should never have been attempted
      expect(mockSendAnalytics).not.toHaveBeenCalled();
      // Only one attempt to insert was made
      expect(mockDAO.insert).toHaveBeenCalledTimes(1);
      // Status update should not have been attempted
      expect(mockDAO.updateStatus).not.toHaveBeenCalled();
    });
  });
});
