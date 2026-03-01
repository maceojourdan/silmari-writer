/**
 * SlotValidationService.test.ts - Step 2: Validate Required Slot Fulfillment
 *
 * TLA+ Properties:
 * - Reachability: call service with payload → returns { missingSlots, newlySatisfied: [] }
 * - TypeInvariant: result matches SlotValidationResult interface
 * - ErrorConsistency:
 *   - Corrupt schema in RequiredSlotSchema → expect REQUIRED_SLOT_SCHEMA_ERROR
 *   - Assert backend logger called
 *
 * Resource: db-h2s4 (service)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SlotError } from '@/server/error_definitions/SlotErrors';

// Mock the slot re-prompt logger
vi.mock('@/server/logging/slotRepromptLogger', () => ({
  slotRepromptLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SlotValidationService } from '../SlotValidationService';
import type { SlotValidationResult } from '../SlotValidationService';
import { slotRepromptLogger } from '@/server/logging/slotRepromptLogger';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createSubmissionPayload(
  slotValues: Record<string, string> = {},
  overrides: Partial<{
    sessionId: string;
    questionType: string;
    attemptCount: number;
  }> = {},
) {
  return {
    sessionId: overrides.sessionId ?? validSessionId,
    questionType: overrides.questionType ?? 'behavioral_question',
    slotValues,
    attemptCount: overrides.attemptCount ?? 1,
  };
}

function createCurrentMissing(): string[] {
  return ['objective', 'actions', 'obstacles', 'outcome', 'roleClarity'];
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SlotValidationService — Step 2: Validate Required Slot Fulfillment', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return missingSlots and empty newlySatisfied when no slots are filled', () => {
      const payload = createSubmissionPayload({});
      const currentMissing = createCurrentMissing();

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result.missingSlots).toEqual(currentMissing);
      expect(result.newlySatisfied).toEqual([]);
    });

    it('should return missingSlots and empty newlySatisfied when submitted values do not match any missing slots', () => {
      const payload = createSubmissionPayload({
        irrelevantField: 'some value',
      });
      const currentMissing = createCurrentMissing();

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result.missingSlots).toEqual(currentMissing);
      expect(result.newlySatisfied).toEqual([]);
    });

    it('should return empty missingSlots and populated newlySatisfied when a slot is filled', () => {
      const payload = createSubmissionPayload({
        objective: 'Increase revenue by 20%',
      });
      const currentMissing = ['objective'];

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result.missingSlots).toEqual([]);
      expect(result.newlySatisfied).toEqual(['objective']);
    });

    it('should detect partial fulfillment — some slots filled, others still missing', () => {
      const payload = createSubmissionPayload({
        objective: 'Increase revenue',
        outcome: 'Revenue grew by 25%',
      });
      const currentMissing = createCurrentMissing();

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result.newlySatisfied).toContain('objective');
      expect(result.newlySatisfied).toContain('outcome');
      expect(result.missingSlots).toContain('actions');
      expect(result.missingSlots).toContain('obstacles');
      expect(result.missingSlots).toContain('roleClarity');
    });

    it('should ignore empty string values as not satisfying a slot', () => {
      const payload = createSubmissionPayload({
        objective: '',
      });
      const currentMissing = ['objective'];

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result.missingSlots).toEqual(['objective']);
      expect(result.newlySatisfied).toEqual([]);
    });

    it('should ignore whitespace-only values as not satisfying a slot', () => {
      const payload = createSubmissionPayload({
        objective: '   ',
      });
      const currentMissing = ['objective'];

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result.missingSlots).toEqual(['objective']);
      expect(result.newlySatisfied).toEqual([]);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching SlotValidationResult interface', () => {
      const payload = createSubmissionPayload({});
      const currentMissing = createCurrentMissing();

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result).toHaveProperty('missingSlots');
      expect(result).toHaveProperty('newlySatisfied');
      expect(Array.isArray(result.missingSlots)).toBe(true);
      expect(Array.isArray(result.newlySatisfied)).toBe(true);
    });

    it('should return string arrays for both missingSlots and newlySatisfied', () => {
      const payload = createSubmissionPayload({
        objective: 'Some objective',
      });
      const currentMissing = ['objective', 'outcome'];

      const result = SlotValidationService.validate(payload, currentMissing);

      for (const slot of result.missingSlots) {
        expect(typeof slot).toBe('string');
      }
      for (const slot of result.newlySatisfied) {
        expect(typeof slot).toBe('string');
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw REQUIRED_SLOT_SCHEMA_ERROR when question_type has no schema', () => {
      const payload = createSubmissionPayload({}, { questionType: 'unknown_type' });
      const currentMissing = ['objective'];

      expect(() => {
        SlotValidationService.validate(payload, currentMissing);
      }).toThrow(SlotError);

      try {
        SlotValidationService.validate(payload, currentMissing);
      } catch (e) {
        expect((e as SlotError).code).toBe('REQUIRED_SLOT_SCHEMA_ERROR');
      }
    });

    it('should call backend logger on schema error', () => {
      const payload = createSubmissionPayload({}, { questionType: 'unknown_type' });
      const currentMissing = ['objective'];

      try {
        SlotValidationService.validate(payload, currentMissing);
      } catch {
        // expected
      }

      expect(slotRepromptLogger.error).toHaveBeenCalled();
    });

    it('should log validation attempt on successful validation', () => {
      const payload = createSubmissionPayload({});
      const currentMissing = createCurrentMissing();

      SlotValidationService.validate(payload, currentMissing);

      expect(slotRepromptLogger.info).toHaveBeenCalled();
    });
  });
});
