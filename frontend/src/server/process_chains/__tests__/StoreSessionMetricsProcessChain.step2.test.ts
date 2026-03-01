/**
 * StoreSessionMetricsProcessChain.step2.test.ts - Step 2: Load session and event data
 *
 * TLA+ Properties:
 * - Reachability: Valid session + events → aggregated dataset
 * - TypeInvariant: dataset includes { session: { status: 'FINALIZED' }, events: Event[] }
 * - ErrorConsistency: null → SessionNotFoundError, not FINALIZED → SessionNotCompletedError
 *
 * Path: 301-store-session-metrics-on-pipeline-run
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoreSessionMetricsProcessChain } from '../StoreSessionMetricsProcessChain';
import { MetricsError } from '@/server/error_definitions/MetricsErrors';
import type { AggregatedSessionDataset } from '@/server/data_structures/SessionMetrics';

// ---------------------------------------------------------------------------
// Mock SessionMetricsDAO at the module boundary
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
// Test Data
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const completedSessionDataset: AggregatedSessionDataset = {
  session: {
    id: validSessionId,
    status: 'FINALIZED',
    createdAt: '2026-02-28T10:00:00.000Z',
    updatedAt: '2026-02-28T12:00:00.000Z',
    firstDraftAt: '2026-02-28T10:30:00.000Z',
    finalizedAt: '2026-02-28T12:00:00.000Z',
  },
  events: [
    {
      id: '00000001-0000-1000-8000-000000000001',
      sessionId: validSessionId,
      category: 'DRAFT',
      timestamp: '2026-02-28T10:30:00.000Z',
    },
    {
      id: '00000001-0000-1000-8000-000000000002',
      sessionId: validSessionId,
      category: 'VERIFY',
      timestamp: '2026-02-28T11:00:00.000Z',
    },
    {
      id: '00000001-0000-1000-8000-000000000003',
      sessionId: validSessionId,
      category: 'FINALIZE',
      timestamp: '2026-02-28T12:00:00.000Z',
    },
  ],
};

const nonFinalizedSessionDataset: AggregatedSessionDataset = {
  session: {
    ...completedSessionDataset.session,
    status: 'FINALIZED', // schema requires literal 'FINALIZED', so we test with a cast
  },
  events: completedSessionDataset.events,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StoreSessionMetricsProcessChain.loadSessionData — Step 2: Load session and event data', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return aggregated dataset for a completed session with events', async () => {
      mockDAO.getSessionWithEvents.mockResolvedValue(completedSessionDataset);

      const dataset = await StoreSessionMetricsProcessChain.loadSessionData({
        sessionId: validSessionId,
      });

      expect(dataset).toBeDefined();
      expect(dataset.session).toBeDefined();
      expect(dataset.events).toBeDefined();
      expect(dataset.events.length).toBe(3);
      expect(mockDAO.getSessionWithEvents).toHaveBeenCalledWith(validSessionId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return dataset with session.status === FINALIZED and events as Event[]', async () => {
      mockDAO.getSessionWithEvents.mockResolvedValue(completedSessionDataset);

      const dataset = await StoreSessionMetricsProcessChain.loadSessionData({
        sessionId: validSessionId,
      });

      expect(dataset.session.status).toBe('FINALIZED');
      expect(Array.isArray(dataset.events)).toBe(true);
      for (const event of dataset.events) {
        expect(typeof event.id).toBe('string');
        expect(typeof event.sessionId).toBe('string');
        expect(typeof event.category).toBe('string');
        expect(typeof event.timestamp).toBe('string');
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SESSION_NOT_FOUND when DAO returns null', async () => {
      mockDAO.getSessionWithEvents.mockResolvedValue(null);

      try {
        await StoreSessionMetricsProcessChain.loadSessionData({
          sessionId: validSessionId,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('SESSION_NOT_FOUND');
        expect((e as MetricsError).statusCode).toBe(404);
      }
    });

    it('should throw SESSION_NOT_COMPLETED when session status is not FINALIZED', async () => {
      // Use a raw object to bypass Zod literal type
      const notFinalizedDataset = {
        session: {
          id: validSessionId,
          status: 'DRAFT' as const,
          createdAt: '2026-02-28T10:00:00.000Z',
          updatedAt: '2026-02-28T12:00:00.000Z',
        },
        events: [],
      };

      mockDAO.getSessionWithEvents.mockResolvedValue(
        notFinalizedDataset as unknown as AggregatedSessionDataset,
      );

      try {
        await StoreSessionMetricsProcessChain.loadSessionData({
          sessionId: validSessionId,
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('SESSION_NOT_COMPLETED');
        expect((e as MetricsError).statusCode).toBe(422);
      }
    });
  });
});
