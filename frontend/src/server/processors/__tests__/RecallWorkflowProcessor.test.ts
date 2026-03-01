/**
 * RecallWorkflowProcessor.test.ts - Step 3: Enforce No Workflow Progression
 *
 * TLA+ Properties:
 * - Reachability: pass validation result with newlySatisfied.length === 0 → state remains RECALL
 * - TypeInvariant: state object matches RecallWorkflowState type
 * - ErrorConsistency: simulate forced progression → expect WORKFLOW_GUARD_VIOLATION error
 *
 * Resource: db-b7r2 (processor)
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

import { RecallWorkflowProcessor } from '../RecallWorkflowProcessor';
import type { RecallWorkflowState } from '../RecallWorkflowProcessor';
import type { SlotValidationResult } from '@/server/services/SlotValidationService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createRecallState(overrides: Partial<RecallWorkflowState> = {}): RecallWorkflowState {
  return {
    sessionId: validSessionId,
    currentStep: 'RECALL',
    missingSlots: ['objective', 'actions', 'obstacles', 'outcome', 'roleClarity'],
    attemptCount: 1,
    ...overrides,
  };
}

function createValidationResult(overrides: Partial<SlotValidationResult> = {}): SlotValidationResult {
  return {
    missingSlots: ['objective', 'actions', 'obstacles', 'outcome', 'roleClarity'],
    newlySatisfied: [],
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallWorkflowProcessor — Step 3: Enforce No Workflow Progression', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should keep state at RECALL when newlySatisfied is empty', () => {
      const state = createRecallState();
      const result = createValidationResult({ newlySatisfied: [] });

      const newState = RecallWorkflowProcessor.handleValidationResult(state, result);

      expect(newState.currentStep).toBe('RECALL');
    });

    it('should preserve the same missing slots when nothing is satisfied', () => {
      const missingSlots = ['objective', 'outcome'];
      const state = createRecallState({ missingSlots });
      const result = createValidationResult({
        missingSlots,
        newlySatisfied: [],
      });

      const newState = RecallWorkflowProcessor.handleValidationResult(state, result);

      expect(newState.missingSlots).toEqual(missingSlots);
    });

    it('should increment attemptCount when no slots are satisfied', () => {
      const state = createRecallState({ attemptCount: 2 });
      const result = createValidationResult({ newlySatisfied: [] });

      const newState = RecallWorkflowProcessor.handleValidationResult(state, result);

      expect(newState.attemptCount).toBe(3);
    });

    it('should update missingSlots when some slots are satisfied', () => {
      const state = createRecallState({
        missingSlots: ['objective', 'outcome', 'roleClarity'],
      });
      const result = createValidationResult({
        missingSlots: ['outcome', 'roleClarity'],
        newlySatisfied: ['objective'],
      });

      const newState = RecallWorkflowProcessor.handleValidationResult(state, result);

      expect(newState.missingSlots).toEqual(['outcome', 'roleClarity']);
      expect(newState.currentStep).toBe('RECALL');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a RecallWorkflowState with all required fields', () => {
      const state = createRecallState();
      const result = createValidationResult({ newlySatisfied: [] });

      const newState = RecallWorkflowProcessor.handleValidationResult(state, result);

      expect(newState).toHaveProperty('sessionId');
      expect(newState).toHaveProperty('currentStep');
      expect(newState).toHaveProperty('missingSlots');
      expect(newState).toHaveProperty('attemptCount');
      expect(typeof newState.sessionId).toBe('string');
      expect(typeof newState.currentStep).toBe('string');
      expect(Array.isArray(newState.missingSlots)).toBe(true);
      expect(typeof newState.attemptCount).toBe('number');
    });

    it('should preserve sessionId in returned state', () => {
      const state = createRecallState({ sessionId: validSessionId });
      const result = createValidationResult({ newlySatisfied: [] });

      const newState = RecallWorkflowProcessor.handleValidationResult(state, result);

      expect(newState.sessionId).toBe(validSessionId);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw WORKFLOW_GUARD_VIOLATION when forced advance is attempted with missing slots', () => {
      const state = createRecallState({
        missingSlots: ['objective', 'outcome'],
      });

      expect(() => {
        RecallWorkflowProcessor.attemptAdvance(state);
      }).toThrow(SlotError);

      try {
        RecallWorkflowProcessor.attemptAdvance(state);
      } catch (e) {
        expect((e as SlotError).code).toBe('WORKFLOW_GUARD_VIOLATION');
      }
    });

    it('should not throw when advance is attempted with zero missing slots', () => {
      const state = createRecallState({ missingSlots: [] });

      expect(() => {
        RecallWorkflowProcessor.attemptAdvance(state);
      }).not.toThrow();
    });
  });
});
