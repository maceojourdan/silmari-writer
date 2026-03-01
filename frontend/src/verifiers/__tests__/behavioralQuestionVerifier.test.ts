/**
 * behavioralQuestionVerifier Tests
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: validateMinimumSlots(validDraft) returns isValid=true
 * - TypeInvariant: return type { isValid: boolean; errors: Record<string,string> }
 * - ErrorConsistency: call with 2 actions → isValid=false, errors.actions defined
 */

import {
  validateMinimumSlots,
  validateField,
} from '../behavioralQuestionVerifier';
import type { BehavioralQuestionDraft } from '@/server/data_structures/BehavioralQuestion';

const validDraft: BehavioralQuestionDraft = {
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

describe('behavioralQuestionVerifier', () => {
  describe('Reachability: validateMinimumSlots(validDraft) returns isValid=true', () => {
    it('should return isValid=true when all minimum slots are filled', () => {
      const result = validateMinimumSlots(validDraft);
      expect(result.isValid).toBe(true);
    });

    it('should return empty errors record on valid input', () => {
      const result = validateMinimumSlots(validDraft);
      expect(Object.keys(result.errors)).toHaveLength(0);
    });

    it('should accept drafts with more than minimum slots', () => {
      const extraDraft: BehavioralQuestionDraft = {
        ...validDraft,
        actions: ['a', 'b', 'c', 'd', 'e'],
        obstacles: ['x', 'y', 'z'],
      };
      const result = validateMinimumSlots(extraDraft);
      expect(result.isValid).toBe(true);
    });
  });

  describe('TypeInvariant: return type { isValid: boolean; errors: Record<string,string> }', () => {
    it('should return an object with isValid boolean and errors record', () => {
      const result = validateMinimumSlots(validDraft);
      expect(typeof result.isValid).toBe('boolean');
      expect(typeof result.errors).toBe('object');
    });

    it('should return string values for error messages', () => {
      const invalidDraft: BehavioralQuestionDraft = {
        ...validDraft,
        objective: '',
      };
      const result = validateMinimumSlots(invalidDraft);
      if (!result.isValid) {
        for (const value of Object.values(result.errors)) {
          expect(typeof value).toBe('string');
        }
      }
    });
  });

  describe('ErrorConsistency: invalid drafts return appropriate errors', () => {
    it('should return isValid=false with errors.actions when actions < 3', () => {
      const invalidDraft: BehavioralQuestionDraft = {
        ...validDraft,
        actions: ['Action 1', 'Action 2'],
      };
      const result = validateMinimumSlots(invalidDraft);
      expect(result.isValid).toBe(false);
      expect(result.errors.actions).toBeDefined();
    });

    it('should return isValid=false when objective is empty', () => {
      const result = validateMinimumSlots({ ...validDraft, objective: '' });
      expect(result.isValid).toBe(false);
      expect(result.errors.objective).toBeDefined();
    });

    it('should return isValid=false when obstacles is empty', () => {
      const result = validateMinimumSlots({ ...validDraft, obstacles: [] });
      expect(result.isValid).toBe(false);
      expect(result.errors.obstacles).toBeDefined();
    });

    it('should return isValid=false when outcome is empty', () => {
      const result = validateMinimumSlots({ ...validDraft, outcome: '' });
      expect(result.isValid).toBe(false);
      expect(result.errors.outcome).toBeDefined();
    });

    it('should return isValid=false when roleClarity is empty', () => {
      const result = validateMinimumSlots({ ...validDraft, roleClarity: '' });
      expect(result.isValid).toBe(false);
      expect(result.errors.roleClarity).toBeDefined();
    });

    it('should return multiple errors when multiple fields are invalid', () => {
      const invalidDraft: BehavioralQuestionDraft = {
        objective: '',
        actions: ['only one'],
        obstacles: [],
        outcome: '',
        roleClarity: '',
      };
      const result = validateMinimumSlots(invalidDraft);
      expect(result.isValid).toBe(false);
      expect(Object.keys(result.errors).length).toBeGreaterThanOrEqual(4);
    });
  });

  describe('validateField: per-field validation', () => {
    it('should return null for a valid objective field', () => {
      const error = validateField('objective', 'A valid objective');
      expect(error).toBeNull();
    });

    it('should return error string for empty objective', () => {
      const error = validateField('objective', '');
      expect(error).not.toBeNull();
      expect(typeof error).toBe('string');
    });

    it('should return null for valid actions array', () => {
      const error = validateField('actions', ['a', 'b', 'c']);
      expect(error).toBeNull();
    });

    it('should return error for insufficient actions', () => {
      const error = validateField('actions', ['a', 'b']);
      expect(error).not.toBeNull();
    });
  });
});
