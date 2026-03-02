/**
 * FinalizeProcessChain.step1.test.ts - Step 1: Handle finalize completion event
 *
 * TLA+ Properties:
 * - Reachability: simulate finalize event { answerId: "a1" } -> service invoked with context { answerId: "a1" }
 * - TypeInvariant: produced context matches { answerId: string }
 * - ErrorConsistency: call with {} or null -> finalizeLogger.error called, service NOT invoked, returns void
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { FinalizeCompletionContext } from '@/server/data_structures/FinalizeCompletion';
import { FinalizeCompletionContextSchema } from '@/server/data_structures/FinalizeCompletion';

// ---------------------------------------------------------------------------
// Mock the finalize logger
// ---------------------------------------------------------------------------

vi.mock('@/server/logging/finalizeLogger', () => ({
  finalizeLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock the FinalizeService (Step 2+ dependency)
// ---------------------------------------------------------------------------

vi.mock('@/server/services/FinalizeService', () => ({
  FinalizeService: {
    evaluatePostFinalize: vi.fn().mockResolvedValue({ smsDispatched: false }),
  },
}));

// ---------------------------------------------------------------------------
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { FinalizeProcessChain } from '../FinalizeProcessChain';
import { finalizeLogger } from '@/server/logging/finalizeLogger';
import { FinalizeService } from '@/server/services/FinalizeService';

const mockLogger = vi.mocked(finalizeLogger);
const mockService = vi.mocked(FinalizeService);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeProcessChain.handleFinalizeCompletion — Step 1: Handle finalize completion event', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should invoke FinalizeService.evaluatePostFinalize with context for a valid event', async () => {
      const event = { answerId: 'a1' };

      await FinalizeProcessChain.handleFinalizeCompletion(event);

      expect(mockService.evaluatePostFinalize).toHaveBeenCalledWith({ answerId: 'a1' });
    });

    it('should invoke FinalizeService.evaluatePostFinalize exactly once', async () => {
      const event = { answerId: 'a1' };

      await FinalizeProcessChain.handleFinalizeCompletion(event);

      expect(mockService.evaluatePostFinalize).toHaveBeenCalledTimes(1);
    });

    it('should return the workflow result from the service', async () => {
      const event = { answerId: 'a1' };

      const result = await FinalizeProcessChain.handleFinalizeCompletion(event);

      expect(result).toEqual({ smsDispatched: false });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass context matching FinalizeCompletionContext schema to the service', async () => {
      const event = { answerId: 'a1' };

      await FinalizeProcessChain.handleFinalizeCompletion(event);

      const passedContext = mockService.evaluatePostFinalize.mock.calls[0][0];
      const parseResult = FinalizeCompletionContextSchema.safeParse(passedContext);
      expect(parseResult.success).toBe(true);
    });

    it('should pass context with answerId as a string', async () => {
      const event = { answerId: 'answer-xyz-123' };

      await FinalizeProcessChain.handleFinalizeCompletion(event);

      const passedContext = mockService.evaluatePostFinalize.mock.calls[0][0];
      expect(typeof passedContext.answerId).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log error when event is an empty object', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({});

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should NOT invoke FinalizeService when event is an empty object', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({});

      expect(mockService.evaluatePostFinalize).not.toHaveBeenCalled();
    });

    it('should return undefined when event is an empty object', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion({});

      expect(result).toBeUndefined();
    });

    it('should log error when event is null', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion(null);

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should NOT invoke FinalizeService when event is null', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion(null);

      expect(mockService.evaluatePostFinalize).not.toHaveBeenCalled();
    });

    it('should return undefined when event is null', async () => {
      const result = await FinalizeProcessChain.handleFinalizeCompletion(null);

      expect(result).toBeUndefined();
    });

    it('should log error when answerId is an empty string', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId: '' });

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should NOT invoke FinalizeService when answerId is an empty string', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({ answerId: '' });

      expect(mockService.evaluatePostFinalize).not.toHaveBeenCalled();
    });

    it('should log error with validation context', async () => {
      await FinalizeProcessChain.handleFinalizeCompletion({});

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('validation'),
        expect.anything(),
        expect.any(Object),
      );
    });
  });
});
