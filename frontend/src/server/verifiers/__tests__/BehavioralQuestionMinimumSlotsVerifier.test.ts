/**
 * BehavioralQuestionMinimumSlotsVerifier Tests
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: verify(validEntity) returns { valid: true }
 * - TypeInvariant: entity matches BehavioralQuestion Zod schema
 * - ErrorConsistency: invalid entity returns MinimumSlotsNotMetError
 */

import { BehavioralQuestionMinimumSlotsVerifier } from '../BehavioralQuestionMinimumSlotsVerifier';
import { BehavioralQuestionSchema } from '@/server/data_structures/BehavioralQuestion';
import { BehavioralQuestionError } from '@/server/error_definitions/BehavioralQuestionErrors';

const validEntity = {
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
  status: 'DRAFT' as const,
};

describe('BehavioralQuestionMinimumSlotsVerifier', () => {
  describe('Reachability: verify(validEntity) returns valid result', () => {
    it('should return { valid: true } when all minimum slots are filled', () => {
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(validEntity);
      expect(result.valid).toBe(true);
    });

    it('should accept entities with more than minimum required slots', () => {
      const entityWithExtra = {
        ...validEntity,
        actions: [
          'Action 1',
          'Action 2',
          'Action 3',
          'Action 4',
          'Action 5',
        ],
        obstacles: ['Obstacle 1', 'Obstacle 2', 'Obstacle 3'],
      };
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(entityWithExtra);
      expect(result.valid).toBe(true);
    });
  });

  describe('TypeInvariant: entity matches BehavioralQuestion Zod schema', () => {
    it('should validate a valid entity against BehavioralQuestionSchema', () => {
      const parsed = BehavioralQuestionSchema.safeParse(validEntity);
      expect(parsed.success).toBe(true);
    });

    it('should return a result with valid boolean and optional errors record', () => {
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(validEntity);
      expect(typeof result.valid).toBe('boolean');
      expect(result.errors).toBeDefined();
      expect(typeof result.errors).toBe('object');
    });
  });

  describe('ErrorConsistency: invalid entity throws MinimumSlotsNotMetError', () => {
    it('should return invalid with errors when actions count is less than 3', () => {
      const invalidEntity = {
        ...validEntity,
        actions: ['Action 1', 'Action 2'],
      };
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(invalidEntity);
      expect(result.valid).toBe(false);
      expect(result.errors.actions).toBeDefined();
    });

    it('should return invalid when obstacles is empty', () => {
      const invalidEntity = {
        ...validEntity,
        obstacles: [],
      };
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(invalidEntity);
      expect(result.valid).toBe(false);
      expect(result.errors.obstacles).toBeDefined();
    });

    it('should return invalid when objective is empty', () => {
      const invalidEntity = {
        ...validEntity,
        objective: '',
      };
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(invalidEntity);
      expect(result.valid).toBe(false);
      expect(result.errors.objective).toBeDefined();
    });

    it('should return invalid when outcome is empty', () => {
      const invalidEntity = {
        ...validEntity,
        outcome: '',
      };
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(invalidEntity);
      expect(result.valid).toBe(false);
      expect(result.errors.outcome).toBeDefined();
    });

    it('should return invalid when roleClarity is empty', () => {
      const invalidEntity = {
        ...validEntity,
        roleClarity: '',
      };
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(invalidEntity);
      expect(result.valid).toBe(false);
      expect(result.errors.roleClarity).toBeDefined();
    });

    it('should return multiple errors when multiple slots are missing', () => {
      const invalidEntity = {
        ...validEntity,
        objective: '',
        actions: ['Only one'],
        outcome: '',
      };
      const result = BehavioralQuestionMinimumSlotsVerifier.verify(invalidEntity);
      expect(result.valid).toBe(false);
      expect(result.errors.objective).toBeDefined();
      expect(result.errors.actions).toBeDefined();
      expect(result.errors.outcome).toBeDefined();
    });
  });
});
