/**
 * approvalLogger.test.ts - Step 5: Log Approval Event
 *
 * TLA+ Properties:
 * - Reachability: Mock primary logger success → log entry written
 * - TypeInvariant: Log entry shape { sessionId, action: 'APPROVE', timestamp }
 * - ErrorConsistency: Logger throw → fallback logger called → service returns logging failure
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 299-approve-draft-and-transition-to-finalize
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// ---------------------------------------------------------------------------
// Mock the backend logger (primary logger)
// ---------------------------------------------------------------------------

vi.mock('../logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock the shared/fallback logger (frontend logger used as fallback)
// ---------------------------------------------------------------------------

vi.mock('../../../logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { approvalLogger, type ApprovalLogEntry } from '../approvalLogger';
import { logger } from '../logger';
import { frontendLogger } from '../../../logging/index';

const mockLogger = vi.mocked(logger);
const mockFallbackLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('approvalLogger.logApproval — Step 5: Log Approval Event', () => {
  const sessionId = '550e8400-e29b-41d4-a716-446655440000';

  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should write log entry via primary logger on success', async () => {
      const result = await approvalLogger.logApproval(sessionId);

      expect(result).toBeDefined();
      expect(mockLogger.info).toHaveBeenCalledTimes(1);
      expect(mockLogger.info).toHaveBeenCalledWith(
        expect.stringContaining('Approval event logged'),
        expect.objectContaining({
          sessionId,
          action: 'APPROVE',
        }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return log entry with shape { sessionId, action, timestamp }', async () => {
      const result = await approvalLogger.logApproval(sessionId);

      expect(result.sessionId).toBe(sessionId);
      expect(result.action).toBe('APPROVE');
      expect(typeof result.timestamp).toBe('string');
      // Timestamp should be ISO format
      expect(() => new Date(result.timestamp)).not.toThrow();
      expect(new Date(result.timestamp).toISOString()).toBe(result.timestamp);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should call fallback logger when primary logger throws', async () => {
      mockLogger.info.mockImplementation(() => {
        throw new Error('Primary logger unavailable');
      });

      try {
        await approvalLogger.logApproval(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(mockFallbackLogger.error).toHaveBeenCalledTimes(1);
        expect(mockFallbackLogger.error).toHaveBeenCalledWith(
          expect.stringContaining('Primary approval logger failed'),
          expect.any(Error),
          expect.objectContaining({ sessionId }),
        );
      }
    });

    it('should rethrow error after calling fallback logger', async () => {
      mockLogger.info.mockImplementation(() => {
        throw new Error('Primary logger unavailable');
      });

      try {
        await approvalLogger.logApproval(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(Error);
        expect((e as Error).message).toBe('Primary logger unavailable');
      }
    });
  });
});
