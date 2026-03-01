/**
 * recall-reprompt.integration.test.ts - Terminal Condition Integration Test
 *
 * Exercises full path:
 * 1. Start in RECALL state with missing slots.
 * 2. Submit input filling zero required slots.
 * 3. Assert:
 *    - Validation result shows unchanged missing slots.
 *    - Workflow state remains RECALL.
 *    - API response re-prompts same slots.
 *    - After 5 attempts, guidance hint appears.
 *    - No transition to VERIFY occurs.
 *
 * This proves:
 * - Reachability: trigger → terminal condition executable.
 * - TypeInvariant: contracts enforced across UI/API/service/processor.
 * - ErrorConsistency: malformed input, schema errors, guard violations,
 *   and UI failures produce defined error states.
 *
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SlotError } from '@/server/error_definitions/SlotErrors';
import { SubmitSlotsResponseSchema } from '@/api_contracts/submitSlots';

// Mock the logger at the boundary
vi.mock('@/server/logging/slotRepromptLogger', () => ({
  slotRepromptLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SlotValidationService } from '@/server/services/SlotValidationService';
import { RecallWorkflowProcessor } from '@/server/processors/RecallWorkflowProcessor';
import type { RecallWorkflowState } from '@/server/processors/RecallWorkflowProcessor';
import { RecallProcessChain } from '@/server/process_chains/RecallProcessChain';
import { SubmitSlotsHandler } from '@/server/request_handlers/SubmitSlotsHandler';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const ALL_MISSING_SLOTS = ['objective', 'actions', 'obstacles', 'outcome', 'roleClarity'];

function createPayload(
  slotValues: Record<string, string> = {},
  attemptCount: number = 1,
) {
  return {
    sessionId: validSessionId,
    questionType: 'behavioral_question',
    slotValues,
    attemptCount,
  };
}

function createInitialState(): RecallWorkflowState {
  return {
    sessionId: validSessionId,
    currentStep: 'RECALL',
    missingSlots: [...ALL_MISSING_SLOTS],
    attemptCount: 0,
  };
}

// ---------------------------------------------------------------------------
// Integration Tests
// ---------------------------------------------------------------------------

describe('Recall Re-Prompt Integration — Full Path (320)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Full Path: Zero Slots Filled → Re-Prompt Same Slots
  // -------------------------------------------------------------------------

  describe('Full path: Submit with zero filled slots → re-prompt same slots', () => {
    it('Step 1→2: Validation shows unchanged missing slots when no input provided', () => {
      const payload = createPayload({});
      const currentMissing = [...ALL_MISSING_SLOTS];

      const result = SlotValidationService.validate(payload, currentMissing);

      expect(result.missingSlots).toEqual(ALL_MISSING_SLOTS);
      expect(result.newlySatisfied).toEqual([]);
    });

    it('Step 2→3: Workflow state remains RECALL with zero newly satisfied', () => {
      const state = createInitialState();
      const validationResult = {
        missingSlots: ALL_MISSING_SLOTS,
        newlySatisfied: [] as string[],
      };

      const newState = RecallWorkflowProcessor.handleValidationResult(
        state,
        validationResult,
      );

      expect(newState.currentStep).toBe('RECALL');
      expect(newState.missingSlots).toEqual(ALL_MISSING_SLOTS);
    });

    it('Step 3→4: RecallProcessChain returns re-prompt state', () => {
      const payload = createPayload({});
      const state = createInitialState();

      const processResult = RecallProcessChain.execute(payload, state);

      expect(processResult.state.currentStep).toBe('RECALL');
      expect(processResult.state.missingSlots).toEqual(ALL_MISSING_SLOTS);
      expect(processResult.validationResult.newlySatisfied).toEqual([]);
    });

    it('Step 4→5: Full handler produces response with same slot prompts', async () => {
      const payload = createPayload({}, 1);

      const response = await SubmitSlotsHandler.handle(payload);

      // Response must conform to schema
      const parsed = SubmitSlotsResponseSchema.safeParse(response);
      expect(parsed.success).toBe(true);

      // All 5 missing slots should be in prompts
      const promptNames = response.prompts.map((p) => p.name);
      expect(promptNames).toEqual(ALL_MISSING_SLOTS);

      // AttemptCount incremented
      expect(response.attemptCount).toBe(2);

      // No guidance hint yet
      expect(response.guidanceHint).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // Guard Violation: No Transition to VERIFY
  // -------------------------------------------------------------------------

  describe('Guard: No transition to VERIFY when slots remain unfilled', () => {
    it('should throw WORKFLOW_GUARD_VIOLATION when advance is attempted', () => {
      const state: RecallWorkflowState = {
        sessionId: validSessionId,
        currentStep: 'RECALL',
        missingSlots: ['objective', 'outcome'],
        attemptCount: 3,
      };

      expect(() => {
        RecallWorkflowProcessor.attemptAdvance(state);
      }).toThrow(SlotError);

      try {
        RecallWorkflowProcessor.attemptAdvance(state);
      } catch (e) {
        expect((e as SlotError).code).toBe('WORKFLOW_GUARD_VIOLATION');
        expect((e as SlotError).statusCode).toBe(409);
      }
    });
  });

  // -------------------------------------------------------------------------
  // Feedback Loop: Guidance Hint After 5 Attempts
  // -------------------------------------------------------------------------

  describe('Feedback loop: Guidance hint after 5 failed attempts', () => {
    it('should include guidanceHint: true after 5 consecutive attempts', async () => {
      const payload = createPayload({}, 5);

      const response = await SubmitSlotsHandler.handle(payload);

      expect(response.guidanceHint).toBe(true);
      expect(response.attemptCount).toBe(6);
    });

    it('should not include guidanceHint before 5 attempts', async () => {
      const payload = createPayload({}, 3);

      const response = await SubmitSlotsHandler.handle(payload);

      expect(response.guidanceHint).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: Full Error Path Coverage
  // -------------------------------------------------------------------------

  describe('ErrorConsistency across all layers', () => {
    it('malformed payload → SLOT_SUBMISSION_INVALID from handler', async () => {
      const invalidPayload = {
        sessionId: 'not-a-uuid',
        questionType: '',
        slotValues: {},
        attemptCount: -1,
      };

      try {
        await SubmitSlotsHandler.handle(invalidPayload);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SlotError);
        expect((e as SlotError).code).toBe('SLOT_SUBMISSION_INVALID');
        expect((e as SlotError).statusCode).toBe(400);
      }
    });

    it('unknown question type → REQUIRED_SLOT_SCHEMA_ERROR from service', () => {
      const payload = createPayload({});
      payload.questionType = 'nonexistent';

      expect(() => {
        SlotValidationService.validate(payload, ['some_slot']);
      }).toThrow(SlotError);

      try {
        SlotValidationService.validate(payload, ['some_slot']);
      } catch (e) {
        expect((e as SlotError).code).toBe('REQUIRED_SLOT_SCHEMA_ERROR');
        expect((e as SlotError).statusCode).toBe(500);
      }
    });

    it('guard violation → WORKFLOW_GUARD_VIOLATION from processor', () => {
      const state: RecallWorkflowState = {
        sessionId: validSessionId,
        currentStep: 'RECALL',
        missingSlots: ['objective'],
        attemptCount: 2,
      };

      try {
        RecallWorkflowProcessor.attemptAdvance(state);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SlotError);
        expect((e as SlotError).code).toBe('WORKFLOW_GUARD_VIOLATION');
        expect((e as SlotError).statusCode).toBe(409);
      }
    });
  });

  // -------------------------------------------------------------------------
  // Partial Fulfillment: Some Slots Filled, Others Still Missing
  // -------------------------------------------------------------------------

  describe('Partial fulfillment path', () => {
    it('should return only remaining missing slots in prompts', async () => {
      const payload = createPayload({
        objective: 'Lead the marketing campaign',
        roleClarity: 'I was the marketing director',
      }, 2);

      const response = await SubmitSlotsHandler.handle(payload);

      const promptNames = response.prompts.map((p) => p.name);
      expect(promptNames).not.toContain('objective');
      expect(promptNames).not.toContain('roleClarity');
      expect(promptNames).toContain('actions');
      expect(promptNames).toContain('obstacles');
      expect(promptNames).toContain('outcome');
      expect(response.attemptCount).toBe(3);
    });
  });
});
