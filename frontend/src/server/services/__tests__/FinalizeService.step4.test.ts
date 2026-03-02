/**
 * FinalizeService.step4.test.ts - Step 4: Bypass SMS Dispatch
 *
 * TLA+ Properties:
 * - Reachability: mock SMS client; with { eligible: false }, assert smsClient.sendMessage NOT called
 * - TypeInvariant: assert returned result { smsDispatched: false }
 * - ErrorConsistency: force eligible=true branch (guard clause) -> assert:
 *   - logger critical called with high severity
 *   - smsClient.sendMessage not executed
 *   - returns { smsDispatched: false }
 *
 * Resource: db-h2s4 (service)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { PostFinalizeResultSchema } from '@/server/data_structures/FinalizeCompletion';

// ---------------------------------------------------------------------------
// Mock the finalizeLogger
// ---------------------------------------------------------------------------

vi.mock('../../logging/finalizeLogger', () => ({
  finalizeLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock DAOs and verifier (not used directly in this step but imported by service)
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/AnswerDAO', () => ({
  AnswerDAO: { findById: vi.fn() },
}));

vi.mock('../../data_access_objects/UserDAO', () => ({
  UserDAO: { findById: vi.fn() },
}));

vi.mock('../../verifiers/FinalizeEligibilityVerifier', () => ({
  FinalizeEligibilityVerifier: { verify: vi.fn() },
}));

// ---------------------------------------------------------------------------
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { FinalizeService } from '../FinalizeService';
import { finalizeLogger } from '../../logging/finalizeLogger';
import type { SmsClient } from '@/server/services/TriggerSmsFollowUpService';

const mockLogger = vi.mocked(finalizeLogger);

// ---------------------------------------------------------------------------
// Mock SMS Client
// ---------------------------------------------------------------------------

function createMockSmsClient(): SmsClient & { sendMessage: ReturnType<typeof vi.fn> } {
  return {
    sendMessage: vi.fn().mockResolvedValue({ sid: 'SM-test-123' }),
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeService.handleSmsDecision — Step 4: Bypass SMS Dispatch', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should NOT call smsClient.sendMessage when eligible is false', async () => {
      const smsClient = createMockSmsClient();

      await FinalizeService.handleSmsDecision({ eligible: false }, smsClient);

      expect(smsClient.sendMessage).not.toHaveBeenCalled();
    });

    it('should return result without calling SMS client', async () => {
      const smsClient = createMockSmsClient();

      const result = await FinalizeService.handleSmsDecision({ eligible: false }, smsClient);

      expect(result).toBeDefined();
      expect(smsClient.sendMessage).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return { smsDispatched: false } when eligible is false', async () => {
      const smsClient = createMockSmsClient();

      const result = await FinalizeService.handleSmsDecision({ eligible: false }, smsClient);

      expect(result).toEqual({ smsDispatched: false });
    });

    it('should return object matching PostFinalizeResultSchema', async () => {
      const smsClient = createMockSmsClient();

      const result = await FinalizeService.handleSmsDecision({ eligible: false }, smsClient);
      const parsed = PostFinalizeResultSchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log critical when eligible is true (inadvertent SMS dispatch guard)', async () => {
      const smsClient = createMockSmsClient();

      await FinalizeService.handleSmsDecision({ eligible: true }, smsClient);

      expect(mockLogger.critical).toHaveBeenCalledWith(
        expect.stringContaining('inadvertently triggered'),
        undefined,
        expect.objectContaining({ eligible: true }),
      );
    });

    it('should NOT call smsClient.sendMessage even when eligible is true (guard suppresses)', async () => {
      const smsClient = createMockSmsClient();

      await FinalizeService.handleSmsDecision({ eligible: true }, smsClient);

      expect(smsClient.sendMessage).not.toHaveBeenCalled();
    });

    it('should return { smsDispatched: false } even when eligible is true (guard suppresses)', async () => {
      const smsClient = createMockSmsClient();

      const result = await FinalizeService.handleSmsDecision({ eligible: true }, smsClient);

      expect(result).toEqual({ smsDispatched: false });
    });
  });
});
