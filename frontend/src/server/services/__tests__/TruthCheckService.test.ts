/**
 * TruthCheckService Tests
 *
 * Resource: db-h2s4 (service)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Properties tested:
 * - Reachability: mock DAO success → call service → assert DAO.create called with correct fields, returns persisted record
 * - TypeInvariant: returned object matches TruthCheck structure
 * - ErrorConsistency: mock DAO throws DB error → assert service throws PersistenceError
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { TruthCheckService } from '../TruthCheckService';
import { TruthCheckDAO } from '@/server/data_access_objects/TruthCheckDAO';
import { TruthCheckSchema } from '@/server/data_structures/TruthCheck';
import type { ConfirmCommand, TruthCheck } from '@/server/data_structures/TruthCheck';

vi.mock('@/server/data_access_objects/TruthCheckDAO', () => ({
  TruthCheckDAO: {
    create: vi.fn(),
  },
}));

const mockDAO = vi.mocked(TruthCheckDAO);

const seedCommand: ConfirmCommand = {
  claim_id: 'claim-001',
  status: 'confirmed',
  source: 'Annual Revenue Report 2025',
};

const seedResult: TruthCheck = {
  id: 'tc-001',
  claim_id: 'claim-001',
  status: 'confirmed',
  source: 'Annual Revenue Report 2025',
  created_at: '2026-02-28T12:00:00.000Z',
};

describe('TruthCheckService', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: confirm() creates truth check via DAO', () => {
    it('should call DAO.create with correct fields', async () => {
      mockDAO.create.mockResolvedValue(seedResult);

      await TruthCheckService.confirm(seedCommand);

      expect(mockDAO.create).toHaveBeenCalledTimes(1);
      expect(mockDAO.create).toHaveBeenCalledWith({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
      });
    });

    it('should return the persisted record', async () => {
      mockDAO.create.mockResolvedValue(seedResult);

      const result = await TruthCheckService.confirm(seedCommand);

      expect(result.id).toBe('tc-001');
      expect(result.claim_id).toBe('claim-001');
      expect(result.status).toBe('confirmed');
      expect(result.source).toBe('Annual Revenue Report 2025');
      expect(result.created_at).toBe('2026-02-28T12:00:00.000Z');
    });

    it('should handle denied status', async () => {
      const deniedCommand: ConfirmCommand = {
        claim_id: 'claim-002',
        status: 'denied',
        source: 'Quarterly Earnings Q3',
      };
      const deniedResult: TruthCheck = {
        id: 'tc-002',
        claim_id: 'claim-002',
        status: 'denied',
        source: 'Quarterly Earnings Q3',
        created_at: '2026-02-28T13:00:00.000Z',
      };
      mockDAO.create.mockResolvedValue(deniedResult);

      const result = await TruthCheckService.confirm(deniedCommand);

      expect(result.status).toBe('denied');
      expect(result.claim_id).toBe('claim-002');
    });
  });

  describe('TypeInvariant: returned object matches TruthCheck structure', () => {
    it('should return data conforming to TruthCheckSchema', async () => {
      mockDAO.create.mockResolvedValue(seedResult);

      const result = await TruthCheckService.confirm(seedCommand);

      const parsed = TruthCheckSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have id, claim_id, status, source, created_at', async () => {
      mockDAO.create.mockResolvedValue(seedResult);

      const result = await TruthCheckService.confirm(seedCommand);

      expect(typeof result.id).toBe('string');
      expect(typeof result.claim_id).toBe('string');
      expect(['confirmed', 'denied']).toContain(result.status);
      expect(typeof result.source).toBe('string');
      expect(typeof result.created_at).toBe('string');
    });
  });

  describe('ErrorConsistency: DAO failure → PersistenceError', () => {
    it('should throw TruthCheckError with TRUTH_CHECK_PERSISTENCE_ERROR code on DAO failure', async () => {
      mockDAO.create.mockRejectedValue(new Error('Database connection lost'));

      try {
        await TruthCheckService.confirm(seedCommand);
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect((e as Error).name).toBe('TruthCheckError');
        expect((e as any).code).toBe('TRUTH_CHECK_PERSISTENCE_ERROR');
        expect((e as any).statusCode).toBe(500);
        expect((e as any).retryable).toBe(true);
      }
    });

    it('should re-throw if error is already a TruthCheckError', async () => {
      const { TruthCheckErrors } = await import('@/server/error_definitions/TruthCheckErrors');
      const existingError = TruthCheckErrors.VALIDATION_ERROR('Invalid claim_id');
      mockDAO.create.mockRejectedValue(existingError);

      try {
        await TruthCheckService.confirm(seedCommand);
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect((e as any).code).toBe('TRUTH_CHECK_VALIDATION_ERROR');
        expect((e as any).statusCode).toBe(400);
      }
    });
  });
});
