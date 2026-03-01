/**
 * StoreSessionMetricsProcessChain.integration.test.ts - Terminal Condition
 *
 * Integration test proving full Reachability from trigger to terminal condition:
 * 1. Seed with completed session + events (DRAFT, VERIFY, FINALIZE)
 * 2. Execute StoreSessionMetricsProcessChain.run(sessionId)
 * 3. Assert session_metrics row exists with all five metrics
 *
 * This test mocks only the DAO boundary (database layer).
 * All process chain logic, verifiers, and computations run with real implementations.
 *
 * Path: 301-store-session-metrics-on-pipeline-run
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoreSessionMetricsProcessChain } from '../StoreSessionMetricsProcessChain';
import { MetricsError } from '@/server/error_definitions/MetricsErrors';
import type { AggregatedSessionDataset, SessionMetrics } from '@/server/data_structures/SessionMetrics';

// ---------------------------------------------------------------------------
// Mock DAO at the module boundary (only external dependency)
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/SessionMetricsDAO', () => ({
  SessionMetricsDAO: {
    getSessionWithEvents: vi.fn(),
    upsertSessionMetrics: vi.fn(),
  },
}));

import { SessionMetricsDAO } from '@/server/data_access_objects/SessionMetricsDAO';
const mockDAO = vi.mocked(SessionMetricsDAO);

// ---------------------------------------------------------------------------
// Mock metricsLogger (side effect boundary)
// ---------------------------------------------------------------------------

vi.mock('../../logging/metricsLogger', () => ({
  metricsLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { metricsLogger } from '@/server/logging/metricsLogger';
const mockLogger = vi.mocked(metricsLogger);

// ---------------------------------------------------------------------------
// Seed Data — completed session with events covering draft, verify, finalize
// ---------------------------------------------------------------------------

const sessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const seededSessionDataset: AggregatedSessionDataset = {
  session: {
    id: sessionId,
    status: 'FINALIZED',
    createdAt: '2026-02-28T10:00:00.000Z',
    updatedAt: '2026-02-28T12:00:00.000Z',
    firstDraftAt: '2026-02-28T10:30:00.000Z',
    finalizedAt: '2026-02-28T12:00:00.000Z',
  },
  events: [
    // DRAFT events
    { id: '00000001-0000-1000-8000-000000000001', sessionId, category: 'DRAFT', timestamp: '2026-02-28T10:30:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000002', sessionId, category: 'DRAFT', timestamp: '2026-02-28T10:35:00.000Z' },
    // VERIFY events
    { id: '00000001-0000-1000-8000-000000000003', sessionId, category: 'VERIFY', timestamp: '2026-02-28T11:00:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000004', sessionId, category: 'VERIFY', timestamp: '2026-02-28T11:10:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000005', sessionId, category: 'VERIFY', timestamp: '2026-02-28T11:20:00.000Z' },
    // FINALIZE event
    { id: '00000001-0000-1000-8000-000000000006', sessionId, category: 'FINALIZE', timestamp: '2026-02-28T12:00:00.000Z' },
    // EDIT events
    { id: '00000001-0000-1000-8000-000000000007', sessionId, category: 'EDIT', timestamp: '2026-02-28T10:40:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000008', sessionId, category: 'EDIT', timestamp: '2026-02-28T10:50:00.000Z' },
    // REVISION event
    { id: '00000001-0000-1000-8000-000000000009', sessionId, category: 'REVISION', timestamp: '2026-02-28T11:30:00.000Z' },
    // SIGNAL events
    { id: '00000001-0000-1000-8000-000000000010', sessionId, category: 'SIGNAL', timestamp: '2026-02-28T11:05:00.000Z' },
    { id: '00000001-0000-1000-8000-000000000011', sessionId, category: 'SIGNAL', timestamp: '2026-02-28T11:15:00.000Z' },
  ],
};

// ---------------------------------------------------------------------------
// Tests — Terminal Condition
// ---------------------------------------------------------------------------

describe('StoreSessionMetricsProcessChain.run — Integration (Terminal Condition)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should execute full pipeline and produce session metrics with all five fields', async () => {
    // Arrange: seed DAO with completed session data
    mockDAO.getSessionWithEvents.mockResolvedValue(seededSessionDataset);

    // Mock upsert to capture and return what was passed
    let capturedMetrics: SessionMetrics | null = null;
    mockDAO.upsertSessionMetrics.mockImplementation(async (metrics: SessionMetrics) => {
      capturedMetrics = {
        ...metrics,
        id: '22222222-2222-2222-2222-222222222222',
        createdAt: '2026-02-28T12:05:00.000Z',
        updatedAt: '2026-02-28T12:05:00.000Z',
      };
      return capturedMetrics;
    });

    // Act: execute the full pipeline
    const result = await StoreSessionMetricsProcessChain.run(sessionId);

    // Assert: pipeline completed successfully
    expect(result.sessionId).toBe(sessionId);
    expect(result.status).toBe('SUCCESS');

    // Assert: session_metrics row exists (via captured metrics)
    expect(capturedMetrics).not.toBeNull();
    expect(capturedMetrics!.sessionId).toBe(sessionId);

    // Assert: contains all five metrics
    expect(capturedMetrics!.timeToFirstDraft).toBeDefined();
    expect(typeof capturedMetrics!.timeToFirstDraft).toBe('number');
    expect(capturedMetrics!.timeToFirstDraft).toBe(1_800_000); // 30 min

    expect(capturedMetrics!.completionRate).toBeDefined();
    expect(typeof capturedMetrics!.completionRate).toBe('number');
    expect(capturedMetrics!.completionRate).toBeCloseTo(1 / 11, 4);

    expect(capturedMetrics!.confirmationRate).toBeDefined();
    expect(typeof capturedMetrics!.confirmationRate).toBe('number');
    expect(capturedMetrics!.confirmationRate).toBeCloseTo(3 / 6, 4);

    expect(capturedMetrics!.signalDensity).toBeDefined();
    expect(typeof capturedMetrics!.signalDensity).toBe('number');
    expect(capturedMetrics!.signalDensity).toBeCloseTo(2 / 3, 4);

    expect(capturedMetrics!.dropOff).toBeDefined();
    expect(typeof capturedMetrics!.dropOff).toBe('number');
    expect(capturedMetrics!.dropOff).toBeCloseTo(1 - (1 / 11), 4);

    // Assert: DAO methods were called correctly
    expect(mockDAO.getSessionWithEvents).toHaveBeenCalledWith(sessionId);
    expect(mockDAO.upsertSessionMetrics).toHaveBeenCalledTimes(1);

    // Assert: success was logged
    expect(mockLogger.info).toHaveBeenCalledWith(
      expect.stringContaining('completed successfully'),
      expect.objectContaining({ sessionId }),
    );
  });

  it('should abort pipeline for invalid session ID', async () => {
    try {
      await StoreSessionMetricsProcessChain.run('not-a-uuid');
      expect.fail('Should have thrown');
    } catch (e) {
      expect(e).toBeInstanceOf(MetricsError);
      expect((e as MetricsError).code).toBe('INVALID_SESSION_IDENTIFIER');
    }

    // DAO should never be called
    expect(mockDAO.getSessionWithEvents).not.toHaveBeenCalled();
  });

  it('should abort pipeline when session not found', async () => {
    mockDAO.getSessionWithEvents.mockResolvedValue(null);

    try {
      await StoreSessionMetricsProcessChain.run(sessionId);
      expect.fail('Should have thrown');
    } catch (e) {
      expect(e).toBeInstanceOf(MetricsError);
      expect((e as MetricsError).code).toBe('SESSION_NOT_FOUND');
    }

    // Upsert should never be called
    expect(mockDAO.upsertSessionMetrics).not.toHaveBeenCalled();
  });

  it('should abort pipeline when persistence fails', async () => {
    mockDAO.getSessionWithEvents.mockResolvedValue(seededSessionDataset);
    mockDAO.upsertSessionMetrics.mockRejectedValue(new Error('DB write failed'));

    try {
      await StoreSessionMetricsProcessChain.run(sessionId);
      expect.fail('Should have thrown');
    } catch (e) {
      expect(e).toBeInstanceOf(MetricsError);
      expect((e as MetricsError).code).toBe('METRICS_PERSISTENCE_ERROR');
    }

    // Error should have been logged
    expect(mockLogger.error).toHaveBeenCalledTimes(1);
  });
});
