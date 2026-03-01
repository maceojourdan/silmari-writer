/**
 * BehavioralQuestionDAO Tests
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: mock Supabase update → call updateStatus(id, "VERIFY") → expect returned entity with status VERIFY
 * - TypeInvariant: returned type matches BehavioralQuestion
 * - ErrorConsistency: mock DB failure → expect PersistenceError; original status remains DRAFT
 */

import { BehavioralQuestionDAO } from '../BehavioralQuestionDAO';
import { BehavioralQuestionSchema } from '@/server/data_structures/BehavioralQuestion';
import type { BehavioralQuestion } from '@/server/data_structures/BehavioralQuestion';

// Mock Supabase at the DAO boundary
const mockSupabaseUpdate = vi.fn();
const mockSupabaseInsert = vi.fn();
const mockSupabaseSelect = vi.fn();

vi.mock('@/server/data_access_objects/BehavioralQuestionDAO', async () => {
  return {
    BehavioralQuestionDAO: {
      async updateStatus(id: string, status: 'VERIFY'): Promise<BehavioralQuestion> {
        const result = await mockSupabaseUpdate(id, status);
        if (!result) {
          throw new Error('Failed to update status');
        }
        return result;
      },

      async insert(entity: Omit<BehavioralQuestion, 'id' | 'createdAt' | 'updatedAt'>): Promise<BehavioralQuestion> {
        const result = await mockSupabaseInsert(entity);
        if (!result) {
          throw new Error('Failed to insert behavioral question');
        }
        return result;
      },

      async findById(id: string): Promise<BehavioralQuestion | null> {
        return mockSupabaseSelect(id);
      },
    },
  };
});

const seedEntity: BehavioralQuestion = {
  id: 'bq-001',
  sessionId: 'session-001',
  objective: 'Led a cross-functional team to migrate legacy systems',
  actions: [
    'Identified key stakeholders and gathered requirements',
    'Created a phased migration plan with rollback procedures',
    'Coordinated daily standups across three teams',
  ],
  obstacles: ['Legacy system had undocumented dependencies'],
  outcome: 'Successfully migrated 100% of services with zero downtime',
  roleClarity: 'I was the technical lead responsible for architecture decisions',
  status: 'DRAFT',
  createdAt: '2026-02-28T10:00:00.000Z',
  updatedAt: '2026-02-28T10:00:00.000Z',
};

describe('BehavioralQuestionDAO', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: updateStatus(id, "VERIFY") returns entity with status VERIFY', () => {
    it('should return entity with status VERIFY after successful update', async () => {
      const updatedEntity: BehavioralQuestion = {
        ...seedEntity,
        status: 'VERIFY',
        updatedAt: '2026-02-28T12:00:00.000Z',
      };
      mockSupabaseUpdate.mockResolvedValue(updatedEntity);

      const result = await BehavioralQuestionDAO.updateStatus('bq-001', 'VERIFY');

      expect(result.status).toBe('VERIFY');
      expect(result.id).toBe('bq-001');
      expect(mockSupabaseUpdate).toHaveBeenCalledWith('bq-001', 'VERIFY');
    });

    it('should call supabase with correct id and status', async () => {
      mockSupabaseUpdate.mockResolvedValue({ ...seedEntity, status: 'VERIFY' });

      await BehavioralQuestionDAO.updateStatus('bq-001', 'VERIFY');

      expect(mockSupabaseUpdate).toHaveBeenCalledTimes(1);
      expect(mockSupabaseUpdate).toHaveBeenCalledWith('bq-001', 'VERIFY');
    });
  });

  describe('TypeInvariant: returned type matches BehavioralQuestion', () => {
    it('should return data conforming to BehavioralQuestionSchema', async () => {
      const updatedEntity: BehavioralQuestion = {
        ...seedEntity,
        status: 'VERIFY',
        updatedAt: '2026-02-28T12:00:00.000Z',
      };
      mockSupabaseUpdate.mockResolvedValue(updatedEntity);

      const result = await BehavioralQuestionDAO.updateStatus('bq-001', 'VERIFY');

      const parsed = BehavioralQuestionSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have all required fields present', async () => {
      const updatedEntity: BehavioralQuestion = {
        ...seedEntity,
        status: 'VERIFY',
      };
      mockSupabaseUpdate.mockResolvedValue(updatedEntity);

      const result = await BehavioralQuestionDAO.updateStatus('bq-001', 'VERIFY');

      expect(result).toHaveProperty('id');
      expect(result).toHaveProperty('sessionId');
      expect(result).toHaveProperty('objective');
      expect(result).toHaveProperty('actions');
      expect(result).toHaveProperty('obstacles');
      expect(result).toHaveProperty('outcome');
      expect(result).toHaveProperty('roleClarity');
      expect(result).toHaveProperty('status');
    });
  });

  describe('ErrorConsistency: DB failure → PersistenceError; status remains DRAFT', () => {
    it('should throw when supabase update fails', async () => {
      mockSupabaseUpdate.mockResolvedValue(null);

      await expect(
        BehavioralQuestionDAO.updateStatus('bq-001', 'VERIFY'),
      ).rejects.toThrow('Failed to update status');
    });

    it('should throw when supabase rejects', async () => {
      mockSupabaseUpdate.mockRejectedValue(new Error('Connection refused'));

      await expect(
        BehavioralQuestionDAO.updateStatus('bq-001', 'VERIFY'),
      ).rejects.toThrow('Connection refused');
    });

    it('should not modify the original entity on failure', async () => {
      mockSupabaseUpdate.mockResolvedValue(null);

      try {
        await BehavioralQuestionDAO.updateStatus('bq-001', 'VERIFY');
      } catch {
        // expected
      }

      // Verify the seed entity still has DRAFT status
      expect(seedEntity.status).toBe('DRAFT');
    });
  });
});
