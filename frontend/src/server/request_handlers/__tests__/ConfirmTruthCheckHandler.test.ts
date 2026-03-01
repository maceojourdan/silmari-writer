/**
 * ConfirmTruthCheckHandler Tests
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Properties tested:
 * - Reachability: POST valid body → handler invoked with normalized command
 * - TypeInvariant: handler receives { claim_id: string; status: "confirmed"|"denied"; source: string }
 * - ErrorConsistency: service error → propagated to caller
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ConfirmTruthCheckHandler } from '../ConfirmTruthCheckHandler';
import { TruthCheckService } from '@/server/services/TruthCheckService';
import type { ConfirmResult } from '@/server/data_structures/TruthCheck';

vi.mock('@/server/services/TruthCheckService', () => ({
  TruthCheckService: {
    confirm: vi.fn(),
  },
}));

const mockService = vi.mocked(TruthCheckService);

const validRequestBody = {
  claim_id: 'claim-001',
  status: 'confirmed' as const,
  source: 'Annual Revenue Report 2025',
};

const successResult: ConfirmResult = {
  id: 'tc-001',
  claim_id: 'claim-001',
  status: 'confirmed',
  source: 'Annual Revenue Report 2025',
  created_at: '2026-02-28T12:00:00.000Z',
};

describe('ConfirmTruthCheckHandler', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: handle() delegates to service', () => {
    it('should call TruthCheckService.confirm with normalized command', async () => {
      mockService.confirm.mockResolvedValue(successResult);

      await ConfirmTruthCheckHandler.handle(validRequestBody);

      expect(mockService.confirm).toHaveBeenCalledTimes(1);
      expect(mockService.confirm).toHaveBeenCalledWith({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
      });
    });

    it('should return the service result', async () => {
      mockService.confirm.mockResolvedValue(successResult);

      const result = await ConfirmTruthCheckHandler.handle(validRequestBody);

      expect(result).toEqual(successResult);
    });
  });

  describe('TypeInvariant: command structure', () => {
    it('should transform request body to ConfirmCommand correctly', () => {
      const command = ConfirmTruthCheckHandler.toCommand(validRequestBody);

      expect(command).toEqual({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
      });
    });

    it('should preserve denied status', () => {
      const deniedBody = {
        claim_id: 'claim-002',
        status: 'denied' as const,
        source: 'Quarterly Earnings Q3',
      };

      const command = ConfirmTruthCheckHandler.toCommand(deniedBody);

      expect(command.status).toBe('denied');
      expect(command.claim_id).toBe('claim-002');
    });

    it('should pass typed command to service', async () => {
      mockService.confirm.mockResolvedValue(successResult);

      await ConfirmTruthCheckHandler.handle(validRequestBody);

      const calledWith = mockService.confirm.mock.calls[0][0];
      expect(typeof calledWith.claim_id).toBe('string');
      expect(['confirmed', 'denied']).toContain(calledWith.status);
      expect(typeof calledWith.source).toBe('string');
    });
  });

  describe('ErrorConsistency: service errors propagated', () => {
    it('should propagate TruthCheckError from service', async () => {
      const { TruthCheckErrors } = await import('@/server/error_definitions/TruthCheckErrors');
      mockService.confirm.mockRejectedValue(
        TruthCheckErrors.PERSISTENCE_ERROR('DB write failed'),
      );

      try {
        await ConfirmTruthCheckHandler.handle(validRequestBody);
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect((e as any).code).toBe('TRUTH_CHECK_PERSISTENCE_ERROR');
      }
    });

    it('should propagate unexpected errors', async () => {
      mockService.confirm.mockRejectedValue(new Error('Unexpected crash'));

      await expect(
        ConfirmTruthCheckHandler.handle(validRequestBody),
      ).rejects.toThrow('Unexpected crash');
    });
  });
});
