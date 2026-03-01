/**
 * BehavioralQuestionService Tests
 *
 * Resource: db-h2s4 (service)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: evaluateForVerify(validEntity) returns { eligible: true }
 * - TypeInvariant: entity matches BehavioralQuestion schema (Zod)
 * - ErrorConsistency: invalid entity → MinimumSlotsNotMetError from db-l1c3
 */

import { BehavioralQuestionService } from '../BehavioralQuestionService';
import { BehavioralQuestionDAO } from '@/server/data_access_objects/BehavioralQuestionDAO';
import { BehavioralQuestionError } from '@/server/error_definitions/BehavioralQuestionErrors';
import type { EvaluateCommand, EvaluateResult } from '@/server/data_structures/BehavioralQuestion';

vi.mock('@/server/data_access_objects/BehavioralQuestionDAO', () => ({
  BehavioralQuestionDAO: {
    updateStatus: vi.fn(),
  },
}));

const mockDAO = vi.mocked(BehavioralQuestionDAO);

const validCommand: EvaluateCommand = {
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
};

describe('BehavioralQuestionService', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.updateStatus.mockResolvedValue({
      id: 'bq-001',
      sessionId: 'session-001',
      objective: validCommand.objective,
      actions: validCommand.actions,
      obstacles: validCommand.obstacles,
      outcome: validCommand.outcome,
      roleClarity: validCommand.roleClarity,
      status: 'VERIFY',
      updatedAt: '2026-02-28T12:00:00.000Z',
    });
  });

  describe('Reachability: evaluateForVerify(validEntity) returns { eligible: true }', () => {
    it('should return eligible: true for valid command with all minimum slots filled', async () => {
      const result = await BehavioralQuestionService.evaluateForVerify(validCommand);
      expect(result.eligible).toBe(true);
    });

    it('should call DAO.updateStatus when eligible', async () => {
      await BehavioralQuestionService.evaluateForVerify(validCommand);
      expect(mockDAO.updateStatus).toHaveBeenCalledTimes(1);
    });

    it('should return the question ID and VERIFY status on success', async () => {
      const result = await BehavioralQuestionService.evaluateForVerify(validCommand);
      expect(result.questionId).toBe('bq-001');
      expect(result.status).toBe('VERIFY');
    });
  });

  describe('TypeInvariant: result matches EvaluateResult shape', () => {
    it('should return an object with eligible, questionId, status, and updatedAt', async () => {
      const result = await BehavioralQuestionService.evaluateForVerify(validCommand);
      expect(typeof result.eligible).toBe('boolean');
      expect(typeof result.questionId).toBe('string');
      expect(result.status).toMatch(/^(DRAFT|VERIFY)$/);
      expect(typeof result.updatedAt).toBe('string');
    });
  });

  describe('ErrorConsistency: invalid entity throws MinimumSlotsNotMetError', () => {
    it('should throw MINIMUM_SLOTS_NOT_MET when actions count is less than 3', async () => {
      const invalidCommand: EvaluateCommand = {
        ...validCommand,
        actions: ['Action 1', 'Action 2'],
      };

      try {
        await BehavioralQuestionService.evaluateForVerify(invalidCommand);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BehavioralQuestionError);
        expect((e as BehavioralQuestionError).code).toBe('MINIMUM_SLOTS_NOT_MET');
        expect((e as BehavioralQuestionError).statusCode).toBe(422);
      }
    });

    it('should NOT call DAO.updateStatus when validation fails', async () => {
      const invalidCommand: EvaluateCommand = {
        ...validCommand,
        objective: '',
      };

      try {
        await BehavioralQuestionService.evaluateForVerify(invalidCommand);
      } catch {
        // expected
      }

      expect(mockDAO.updateStatus).not.toHaveBeenCalled();
    });

    it('should throw PERSISTENCE_FAILED when DAO fails', async () => {
      mockDAO.updateStatus.mockRejectedValue(new Error('DB connection lost'));

      try {
        await BehavioralQuestionService.evaluateForVerify(validCommand);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BehavioralQuestionError);
        expect((e as BehavioralQuestionError).code).toBe('PERSISTENCE_FAILED');
        expect((e as BehavioralQuestionError).retryable).toBe(true);
      }
    });
  });
});
