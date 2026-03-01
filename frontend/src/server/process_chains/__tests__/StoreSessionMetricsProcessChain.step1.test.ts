/**
 * StoreSessionMetricsProcessChain.step1.test.ts - Step 1: Trigger metrics process chain
 *
 * TLA+ Properties:
 * - Reachability: Valid UUID → job context with sessionId
 * - TypeInvariant: jobContext.sessionId is string (UUID format)
 * - ErrorConsistency: undefined/malformed ID → InvalidSessionIdentifierError
 *
 * Path: 301-store-session-metrics-on-pipeline-run
 */

import { describe, it, expect } from 'vitest';
import { StoreSessionMetricsProcessChain } from '../StoreSessionMetricsProcessChain';
import { MetricsError } from '@/server/error_definitions/MetricsErrors';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';
const malformedSessionId = 'not-a-uuid';

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StoreSessionMetricsProcessChain.start — Step 1: Trigger metrics process chain', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return job context containing sessionId for a valid UUID', () => {
      const jobContext = StoreSessionMetricsProcessChain.start(validSessionId);

      expect(jobContext).toBeDefined();
      expect(jobContext.sessionId).toBe(validSessionId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return jobContext.sessionId as a string in UUID format', () => {
      const jobContext = StoreSessionMetricsProcessChain.start(validSessionId);

      expect(typeof jobContext.sessionId).toBe('string');
      // UUID v4 format check
      expect(jobContext.sessionId).toMatch(
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i,
      );
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw INVALID_SESSION_IDENTIFIER for undefined sessionId', () => {
      try {
        StoreSessionMetricsProcessChain.start(undefined as unknown as string);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('INVALID_SESSION_IDENTIFIER');
        expect((e as MetricsError).statusCode).toBe(400);
      }
    });

    it('should throw INVALID_SESSION_IDENTIFIER for malformed sessionId', () => {
      try {
        StoreSessionMetricsProcessChain.start(malformedSessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('INVALID_SESSION_IDENTIFIER');
        expect((e as MetricsError).statusCode).toBe(400);
      }
    });

    it('should throw INVALID_SESSION_IDENTIFIER for empty string', () => {
      try {
        StoreSessionMetricsProcessChain.start('');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(MetricsError);
        expect((e as MetricsError).code).toBe('INVALID_SESSION_IDENTIFIER');
        expect((e as MetricsError).statusCode).toBe(400);
      }
    });
  });
});
