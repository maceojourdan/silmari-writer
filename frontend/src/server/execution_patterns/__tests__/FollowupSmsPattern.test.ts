/**
 * FollowupSmsPattern.test.ts - Step 1: Trigger FOLLOWUP_SMS pattern
 *
 * TLA+ Properties:
 * - Reachability: Given event { type: 'FOLLOWUP_SMS', claimId } → backend chain called with { claimId }
 * - TypeInvariant: Assert output type FollowupSmsEvent contains claimId: string
 * - ErrorConsistency: Given non-matching event → backend chain not called, shared logger invoked with pattern_bypass
 *
 * Resource: mq-t2f7 (execution_pattern)
 * Path: 305-followup-sms-for-uncertain-claim
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock the backend process chain
vi.mock('@/server/process_chains/FollowupSmsProcessChain', () => ({
  FollowupSmsProcessChain: {
    start: vi.fn(),
  },
}));

// Mock the shared logger (frontend/src/logging)
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { FollowupSmsPattern } from '../FollowupSmsPattern';
import { FollowupSmsProcessChain } from '@/server/process_chains/FollowupSmsProcessChain';
import { frontendLogger } from '@/logging/index';

const mockProcessChain = vi.mocked(FollowupSmsProcessChain);
const mockLogger = vi.mocked(frontendLogger);

describe('FollowupSmsPattern.evaluate — Step 1: Trigger FOLLOWUP_SMS pattern', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call backend process chain with claimId when event type is FOLLOWUP_SMS', async () => {
      mockProcessChain.start.mockResolvedValue(undefined);

      await FollowupSmsPattern.evaluate({ type: 'FOLLOWUP_SMS', claimId: 'claim-123' });

      expect(mockProcessChain.start).toHaveBeenCalledOnce();
      expect(mockProcessChain.start).toHaveBeenCalledWith({ claimId: 'claim-123' });
    });

    it('should return MATCHED result on successful dispatch', async () => {
      mockProcessChain.start.mockResolvedValue(undefined);

      const result = await FollowupSmsPattern.evaluate({ type: 'FOLLOWUP_SMS', claimId: 'claim-456' });

      expect(result).toBe('MATCHED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass claimId as a string to the backend process chain', async () => {
      mockProcessChain.start.mockResolvedValue(undefined);

      await FollowupSmsPattern.evaluate({ type: 'FOLLOWUP_SMS', claimId: 'abc-def-ghi' });

      const callArg = mockProcessChain.start.mock.calls[0][0];
      expect(typeof callArg.claimId).toBe('string');
      expect(callArg.claimId).toBe('abc-def-ghi');
    });

    it('should only forward claimId, not extraneous fields', async () => {
      mockProcessChain.start.mockResolvedValue(undefined);

      await FollowupSmsPattern.evaluate({
        type: 'FOLLOWUP_SMS',
        claimId: 'claim-789',
        extraField: 'should-not-pass',
      });

      expect(mockProcessChain.start).toHaveBeenCalledWith({ claimId: 'claim-789' });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return BYPASS for non-matching event type', async () => {
      const result = await FollowupSmsPattern.evaluate({ type: 'OTHER_EVENT', claimId: 'claim-123' });

      expect(result).toBe('BYPASS');
    });

    it('should not call backend process chain for non-matching event', async () => {
      await FollowupSmsPattern.evaluate({ type: 'SOME_OTHER_EVENT', data: {} });

      expect(mockProcessChain.start).not.toHaveBeenCalled();
    });

    it('should log pattern_bypass via shared logger for non-matching event', async () => {
      await FollowupSmsPattern.evaluate({ type: 'UNRELATED', claimId: 'claim-999' });

      expect(mockLogger.info).toHaveBeenCalledWith(
        expect.stringContaining('pattern_bypass'),
        expect.objectContaining({
          path: '305-followup-sms-for-uncertain-claim',
          resource: 'cfg-p4b8',
        }),
      );
    });

    it('should return BYPASS when event has no type field', async () => {
      const result = await FollowupSmsPattern.evaluate({ claimId: 'claim-123' });

      expect(result).toBe('BYPASS');
    });

    it('should return BYPASS when event type is FOLLOWUP_SMS but claimId is missing', async () => {
      const result = await FollowupSmsPattern.evaluate({ type: 'FOLLOWUP_SMS' });

      expect(result).toBe('BYPASS');
    });
  });
});
