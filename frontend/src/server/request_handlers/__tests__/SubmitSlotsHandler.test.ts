/**
 * SubmitSlotsHandler.test.ts - Step 4: Generate Targeted Re-Prompt
 *
 * TLA+ Properties:
 * - Reachability: full handler call → returns { prompts: missingSlots, attemptCount }
 * - TypeInvariant: response matches SubmitSlotsResponse contract
 * - ErrorConsistency: mock missing slot retrieval failure → returns
 *   RECOVERABLE_SLOT_RETRIEVAL_ERROR and generic prompt
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SlotError } from '@/server/error_definitions/SlotErrors';
import { SubmitSlotsResponseSchema } from '@/api_contracts/submitSlots';

// Mock the logger
vi.mock('@/server/logging/slotRepromptLogger', () => ({
  slotRepromptLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock the backend logger
vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SubmitSlotsHandler } from '../SubmitSlotsHandler';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createValidPayload(overrides: Record<string, unknown> = {}) {
  return {
    sessionId: validSessionId,
    questionType: 'behavioral_question',
    slotValues: {},
    attemptCount: 1,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SubmitSlotsHandler — Step 4: Generate Targeted Re-Prompt', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return prompts for missing slots and incremented attemptCount', async () => {
      const payload = createValidPayload();

      const result = await SubmitSlotsHandler.handle(payload);

      expect(result.prompts).toBeDefined();
      expect(result.prompts.length).toBeGreaterThan(0);
      expect(result.attemptCount).toBe(2); // incremented from 1
    });

    it('should return prompts matching the missing required slots', async () => {
      const payload = createValidPayload({
        slotValues: {
          objective: 'Increase revenue',
          outcome: 'Revenue grew by 25%',
        },
      });

      const result = await SubmitSlotsHandler.handle(payload);

      // Should NOT include satisfied slots in prompts
      const promptNames = result.prompts.map((p) => p.name);
      expect(promptNames).not.toContain('objective');
      expect(promptNames).not.toContain('outcome');
      // Should include still-missing slots
      expect(promptNames).toContain('actions');
      expect(promptNames).toContain('obstacles');
      expect(promptNames).toContain('roleClarity');
    });

    it('should include guidanceHint: true after 5 attempts', async () => {
      const payload = createValidPayload({ attemptCount: 5 });

      const result = await SubmitSlotsHandler.handle(payload);

      expect(result.guidanceHint).toBe(true);
    });

    it('should include guidanceHint: false before 5 attempts', async () => {
      const payload = createValidPayload({ attemptCount: 3 });

      const result = await SubmitSlotsHandler.handle(payload);

      expect(result.guidanceHint).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return response conforming to SubmitSlotsResponse schema', async () => {
      const payload = createValidPayload();

      const result = await SubmitSlotsHandler.handle(payload);

      const parsed = SubmitSlotsResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have typed prompt objects with name and promptLabel', async () => {
      const payload = createValidPayload();

      const result = await SubmitSlotsHandler.handle(payload);

      for (const prompt of result.prompts) {
        expect(typeof prompt.name).toBe('string');
        expect(typeof prompt.promptLabel).toBe('string');
        expect(prompt.name.length).toBeGreaterThan(0);
        expect(prompt.promptLabel.length).toBeGreaterThan(0);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SLOT_SUBMISSION_INVALID for invalid payload', async () => {
      const invalidPayload = {
        sessionId: 'not-a-uuid',
        questionType: '',
        slotValues: {},
        attemptCount: -1,
      };

      await expect(SubmitSlotsHandler.handle(invalidPayload)).rejects.toThrow(SlotError);

      try {
        await SubmitSlotsHandler.handle(invalidPayload);
      } catch (e) {
        expect((e as SlotError).code).toBe('SLOT_SUBMISSION_INVALID');
      }
    });

    it('should throw REQUIRED_SLOT_SCHEMA_ERROR for unknown question type', async () => {
      const payload = createValidPayload({ questionType: 'unknown_type' });

      await expect(SubmitSlotsHandler.handle(payload)).rejects.toThrow(SlotError);

      try {
        await SubmitSlotsHandler.handle(payload);
      } catch (e) {
        expect((e as SlotError).code).toBe('REQUIRED_SLOT_SCHEMA_ERROR');
      }
    });
  });
});
