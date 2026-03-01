/**
 * generateFollowUpPrompt.test.ts - Step 4: Generate follow-up prompt
 *
 * TLA+ Properties:
 * - Reachability: Missing slot = 'outcome' → prompt includes slot-specific template
 * - TypeInvariant: Returned value is string
 * - ErrorConsistency: Missing template → generic fallback prompt used
 *
 * Resource: db-h2s4 (service)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { BEHAVIORAL_QUESTION_TYPE } from '@/server/data_structures/VoiceInteractionContext';
import type { VoiceInteractionContext } from '@/server/data_structures/VoiceInteractionContext';
import { SLOT_PROMPT_TEMPLATES, GENERIC_CLARIFICATION_PROMPT } from '@/server/constants/VoicePromptTemplates';

// Mock the recall voice logger
vi.mock('@/server/logging/recallVoiceLogger', () => ({
  recallVoiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { VoiceRecallService } from '../VoiceRecallService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createContext(overrides: Partial<VoiceInteractionContext> = {}): VoiceInteractionContext {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE,
    slotState: { slots: [] },
    retryCount: 0,
    maxRetries: 2,
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VoiceRecallService.generateFollowUpPrompt — Step 4: Generate follow-up prompt', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return slot-specific template for "outcome"', () => {
      const context = createContext();
      const missingSlots = ['outcome'];

      const result = VoiceRecallService.generateFollowUpPrompt(context, missingSlots);

      expect(result).toBe(SLOT_PROMPT_TEMPLATES['outcome']);
    });

    it('should return prompt for multiple missing slots', () => {
      const context = createContext();
      const missingSlots = ['outcome', 'roleClarity'];

      const result = VoiceRecallService.generateFollowUpPrompt(context, missingSlots);

      expect(result.length).toBeGreaterThan(0);
      // Multi-slot prompt should reference both missing slots
      expect(result).toContain('outcome');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a string', () => {
      const context = createContext();
      const missingSlots = ['objective'];

      const result = VoiceRecallService.generateFollowUpPrompt(context, missingSlots);

      expect(typeof result).toBe('string');
    });

    it('should return non-empty string for non-empty missing slots', () => {
      const context = createContext();
      const missingSlots = ['actions'];

      const result = VoiceRecallService.generateFollowUpPrompt(context, missingSlots);

      expect(result.length).toBeGreaterThan(0);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should use generic fallback for unknown slot name', () => {
      const context = createContext();
      const missingSlots = ['unknownSlotXyz'];

      const result = VoiceRecallService.generateFollowUpPrompt(context, missingSlots);

      // Should use the generic template with the slot name substituted
      expect(result).toBe(GENERIC_CLARIFICATION_PROMPT.replace('{slotName}', 'unknownSlotXyz'));
    });

    it('should return empty string when no slots are missing', () => {
      const context = createContext();
      const missingSlots: string[] = [];

      const result = VoiceRecallService.generateFollowUpPrompt(context, missingSlots);

      expect(result).toBe('');
    });
  });
});
