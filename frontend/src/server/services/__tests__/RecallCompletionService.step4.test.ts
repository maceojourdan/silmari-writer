/**
 * RecallCompletionService.step4.test.ts - Step 4: Validate Required Slot Completion
 *
 * TLA+ Properties:
 * - Reachability: Fully populated slots → { complete: true }
 * - TypeInvariant: Return type is ValidationResult with boolean `complete`
 * - ErrorConsistency: Slot value violates rule (e.g., actions < 3) → SlotValidationError
 *
 * Resource: db-h2s4 (service)
 * Path: 319-complete-required-slots-and-end-recall-loop
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { RecallError } from '@/server/error_definitions/RecallErrors';
import {
  ValidationResultSchema,
  BEHAVIORAL_QUESTION_TYPE_RECALL,
} from '@/server/data_structures/RecallSession';
import type { RecallSession } from '@/server/data_structures/RecallSession';

// Mock the recall completion logger
vi.mock('@/server/logging/recallCompletionLogger', () => ({
  recallCompletionLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { RecallCompletionService } from '../RecallCompletionService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createFullyPopulatedSession(): RecallSession {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE_RECALL,
    slotState: {
      slots: [
        { name: 'objective', value: 'Increase revenue by 20%', confirmed: false },
        { name: 'actions', value: ['cold calling', 'email campaigns', 'social media outreach'], confirmed: false },
        { name: 'obstacles', value: ['budget constraints'], confirmed: false },
        { name: 'outcome', value: 'Revenue grew by 25%', confirmed: false },
        { name: 'roleClarity', value: 'I was the sales team lead', confirmed: false },
      ],
    },
    active: true,
    retryCount: 0,
    maxRetries: 3,
  };
}

function createPartiallyPopulatedSession(): RecallSession {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE_RECALL,
    slotState: {
      slots: [
        { name: 'objective', value: 'Increase revenue', confirmed: false },
        { name: 'actions', value: ['cold calling', 'email campaigns', 'social media outreach'], confirmed: false },
      ],
    },
    active: true,
    retryCount: 0,
    maxRetries: 3,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallCompletionService.validateRequiredSlots — Step 4', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return complete: true when all required slots are populated', () => {
      const session = createFullyPopulatedSession();

      const result = RecallCompletionService.validateRequiredSlots(session);

      expect(result.complete).toBe(true);
    });

    it('should return complete: false when required slots are missing', () => {
      const session = createPartiallyPopulatedSession();

      const result = RecallCompletionService.validateRequiredSlots(session);

      expect(result.complete).toBe(false);
      expect(result.missingSlots).toBeDefined();
      expect(result.missingSlots!.length).toBeGreaterThan(0);
    });

    it('should identify which slots are missing', () => {
      const session = createPartiallyPopulatedSession();

      const result = RecallCompletionService.validateRequiredSlots(session);

      expect(result.missingSlots).toContain('obstacles');
      expect(result.missingSlots).toContain('outcome');
      expect(result.missingSlots).toContain('roleClarity');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result conforming to ValidationResult schema', () => {
      const session = createFullyPopulatedSession();

      const result = RecallCompletionService.validateRequiredSlots(session);

      const parsed = ValidationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have boolean complete field', () => {
      const session = createFullyPopulatedSession();

      const result = RecallCompletionService.validateRequiredSlots(session);

      expect(typeof result.complete).toBe('boolean');
    });

    it('should return ValidationResult for incomplete slots too', () => {
      const session = createPartiallyPopulatedSession();

      const result = RecallCompletionService.validateRequiredSlots(session);

      const parsed = ValidationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
      expect(typeof result.complete).toBe('boolean');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SlotValidationError when slot value violates constraint (actions < 3)', () => {
      const session: RecallSession = {
        sessionId: validSessionId,
        questionType: BEHAVIORAL_QUESTION_TYPE_RECALL,
        slotState: {
          slots: [
            { name: 'objective', value: 'Some objective', confirmed: false },
            { name: 'actions', value: ['only one action'], confirmed: false },
            { name: 'obstacles', value: ['some obstacle'], confirmed: false },
            { name: 'outcome', value: 'Some outcome', confirmed: false },
            { name: 'roleClarity', value: 'Team lead', confirmed: false },
          ],
        },
        active: true,
        retryCount: 0,
        maxRetries: 3,
      };

      expect(() => {
        RecallCompletionService.validateRequiredSlots(session);
      }).toThrow(RecallError);

      try {
        RecallCompletionService.validateRequiredSlots(session);
      } catch (e) {
        expect((e as RecallError).code).toBe('SLOT_VALIDATION_ERROR');
      }
    });
  });
});
