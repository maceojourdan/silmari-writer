/**
 * BehavioralQuestionEvaluateHandler Tests
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: handle(validBody) returns EvaluateResult
 * - TypeInvariant: command matches EvaluateCommand shape
 * - ErrorConsistency: service error propagates correctly
 */

import { BehavioralQuestionEvaluateHandler } from '../BehavioralQuestionEvaluateHandler';
import { BehavioralQuestionService } from '@/server/services/BehavioralQuestionService';
import { BehavioralQuestionError } from '@/server/error_definitions/BehavioralQuestionErrors';
import type { EvaluateResult } from '@/server/data_structures/BehavioralQuestion';

vi.mock('@/server/services/BehavioralQuestionService', () => ({
  BehavioralQuestionService: {
    evaluateForVerify: vi.fn(),
  },
}));

const mockService = vi.mocked(BehavioralQuestionService);

const validBody = {
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

const successResult: EvaluateResult = {
  eligible: true,
  questionId: 'bq-001',
  status: 'VERIFY',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

describe('BehavioralQuestionEvaluateHandler', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockService.evaluateForVerify.mockResolvedValue(successResult);
  });

  describe('Reachability: handle(validBody) returns EvaluateResult', () => {
    it('should call service.evaluateForVerify and return result', async () => {
      const result = await BehavioralQuestionEvaluateHandler.handle(validBody);

      expect(result).toEqual(successResult);
      expect(mockService.evaluateForVerify).toHaveBeenCalledTimes(1);
    });
  });

  describe('TypeInvariant: command matches EvaluateCommand shape', () => {
    it('should pass an EvaluateCommand with all required fields to service', async () => {
      await BehavioralQuestionEvaluateHandler.handle(validBody);

      const command = mockService.evaluateForVerify.mock.calls[0][0];
      expect(command).toHaveProperty('sessionId');
      expect(command).toHaveProperty('objective');
      expect(command).toHaveProperty('actions');
      expect(command).toHaveProperty('obstacles');
      expect(command).toHaveProperty('outcome');
      expect(command).toHaveProperty('roleClarity');
    });

    it('should correctly map body fields to command', async () => {
      await BehavioralQuestionEvaluateHandler.handle(validBody);

      const command = mockService.evaluateForVerify.mock.calls[0][0];
      expect(command.sessionId).toBe('session-001');
      expect(command.objective).toBe(validBody.objective);
      expect(command.actions).toEqual(validBody.actions);
    });
  });

  describe('ErrorConsistency: service errors propagate correctly', () => {
    it('should propagate BehavioralQuestionError from service', async () => {
      mockService.evaluateForVerify.mockRejectedValue(
        new BehavioralQuestionError('Minimum slots not met', 'MINIMUM_SLOTS_NOT_MET', 422),
      );

      try {
        await BehavioralQuestionEvaluateHandler.handle(validBody);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BehavioralQuestionError);
        expect((e as BehavioralQuestionError).code).toBe('MINIMUM_SLOTS_NOT_MET');
      }
    });

    it('should propagate persistence errors from service', async () => {
      mockService.evaluateForVerify.mockRejectedValue(
        new BehavioralQuestionError('DB down', 'PERSISTENCE_FAILED', 500, true),
      );

      try {
        await BehavioralQuestionEvaluateHandler.handle(validBody);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as BehavioralQuestionError).retryable).toBe(true);
      }
    });
  });
});
