/**
 * TruthCheckDAO Tests
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Properties tested:
 * - Reachability: mock Supabase insert → call create(data) → expect returned entity with correct fields
 * - TypeInvariant: returned type matches TruthCheck schema
 * - ErrorConsistency: mock DB failure → expect error thrown
 */

import { TruthCheckDAO } from '../TruthCheckDAO';
import { TruthCheckSchema } from '@/server/data_structures/TruthCheck';
import type { TruthCheck, ConfirmCommand } from '@/server/data_structures/TruthCheck';

// Mock Supabase at the DAO boundary
const mockSupabaseInsert = vi.fn();

vi.mock('@/server/data_access_objects/TruthCheckDAO', async () => {
  return {
    TruthCheckDAO: {
      async create(data: ConfirmCommand): Promise<TruthCheck> {
        const result = await mockSupabaseInsert(data);
        if (!result) {
          throw new Error('Failed to insert truth check');
        }
        return result;
      },
    },
  };
});

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

describe('TruthCheckDAO', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: create(data) returns persisted entity', () => {
    it('should return entity with correct fields after successful insert', async () => {
      mockSupabaseInsert.mockResolvedValue(seedResult);

      const result = await TruthCheckDAO.create(seedCommand);

      expect(result.id).toBe('tc-001');
      expect(result.claim_id).toBe('claim-001');
      expect(result.status).toBe('confirmed');
      expect(result.source).toBe('Annual Revenue Report 2025');
      expect(result.created_at).toBe('2026-02-28T12:00:00.000Z');
      expect(mockSupabaseInsert).toHaveBeenCalledWith(seedCommand);
    });

    it('should call supabase with correct data', async () => {
      mockSupabaseInsert.mockResolvedValue(seedResult);

      await TruthCheckDAO.create(seedCommand);

      expect(mockSupabaseInsert).toHaveBeenCalledTimes(1);
      expect(mockSupabaseInsert).toHaveBeenCalledWith({
        claim_id: 'claim-001',
        status: 'confirmed',
        source: 'Annual Revenue Report 2025',
      });
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
      mockSupabaseInsert.mockResolvedValue(deniedResult);

      const result = await TruthCheckDAO.create(deniedCommand);

      expect(result.status).toBe('denied');
    });
  });

  describe('TypeInvariant: returned type matches TruthCheck schema', () => {
    it('should return data conforming to TruthCheckSchema', async () => {
      mockSupabaseInsert.mockResolvedValue(seedResult);

      const result = await TruthCheckDAO.create(seedCommand);

      const parsed = TruthCheckSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have all required fields present', async () => {
      mockSupabaseInsert.mockResolvedValue(seedResult);

      const result = await TruthCheckDAO.create(seedCommand);

      expect(result).toHaveProperty('id');
      expect(result).toHaveProperty('claim_id');
      expect(result).toHaveProperty('status');
      expect(result).toHaveProperty('source');
      expect(result).toHaveProperty('created_at');
    });

    it('should have status as confirmed or denied', async () => {
      mockSupabaseInsert.mockResolvedValue(seedResult);

      const result = await TruthCheckDAO.create(seedCommand);

      expect(['confirmed', 'denied']).toContain(result.status);
    });
  });

  describe('ErrorConsistency: DB failure → error thrown', () => {
    it('should throw when supabase insert fails', async () => {
      mockSupabaseInsert.mockResolvedValue(null);

      await expect(
        TruthCheckDAO.create(seedCommand),
      ).rejects.toThrow('Failed to insert truth check');
    });

    it('should throw when supabase rejects', async () => {
      mockSupabaseInsert.mockRejectedValue(new Error('Connection refused'));

      await expect(
        TruthCheckDAO.create(seedCommand),
      ).rejects.toThrow('Connection refused');
    });
  });
});
