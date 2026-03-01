/**
 * SlotExtractor.test.ts - Step 2: Extract slot values from response
 *
 * TLA+ Properties:
 * - Reachability: Input transcript → returns structured slot-value object
 * - TypeInvariant: Result validates against Zod SlotSchema (PartialSlotData)
 * - ErrorConsistency: Malformed/null input → VoiceErrors.TRANSFORMATION_FAILED
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import { describe, it, expect } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import {
  PartialSlotDataSchema,
  BEHAVIORAL_QUESTION_TYPE,
} from '@/server/data_structures/VoiceInteractionContext';
import type { QuestionTypeDefinition } from '@/server/data_structures/VoiceInteractionContext';
import { SlotExtractor } from '../SlotExtractor';

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SlotExtractor.extract — Step 2: Extract slot values from response', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should extract structured slot-value object from a complete transcript', () => {
      const transcript =
        'My objective was to increase team velocity. ' +
        'I took these actions: reorganized sprints, hired two engineers, and improved CI/CD pipeline. ' +
        'The obstacle was budget constraints. ' +
        'The outcome was a 40% increase in delivery speed. ' +
        'My role was engineering manager responsible for the platform team.';

      const result = SlotExtractor.extract(transcript, BEHAVIORAL_QUESTION_TYPE);

      expect(result).toBeDefined();
      expect(result.slots).toBeDefined();
      expect(result.slots.length).toBeGreaterThan(0);

      const slotNames = result.slots.map((s) => s.name);
      expect(slotNames).toContain('objective');
    });

    it('should extract multiple slot types from a rich transcript', () => {
      const transcript =
        'My objective was to deliver the product launch on time. ' +
        'Actions: coordinated design reviews, set up automated testing, and managed stakeholders. ' +
        'Challenges included tight deadlines and resource constraints. ' +
        'The result was successful on-time delivery with 99.9% uptime. ' +
        'I was responsible for leading the entire engineering initiative.';

      const result = SlotExtractor.extract(transcript, BEHAVIORAL_QUESTION_TYPE);

      expect(result.slots.length).toBeGreaterThanOrEqual(1);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate result against PartialSlotData Zod schema', () => {
      const transcript =
        'My objective was to reduce customer churn by improving onboarding.';

      const result = SlotExtractor.extract(transcript, BEHAVIORAL_QUESTION_TYPE);

      const parsed = PartialSlotDataSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return slot values matching the question_type slot definitions', () => {
      const transcript =
        'My objective was to build a new authentication system. ' +
        'I took these steps: designed the architecture, implemented OAuth, and wrote tests.';

      const result = SlotExtractor.extract(transcript, BEHAVIORAL_QUESTION_TYPE);

      const validSlotNames = BEHAVIORAL_QUESTION_TYPE.slots.map((s) => s.name);
      for (const slot of result.slots) {
        expect(validSlotNames).toContain(slot.name);
      }
    });

    it('should return actions as string_array type', () => {
      const transcript =
        'I took these actions: created documentation, trained the team, and deployed to production.';

      const result = SlotExtractor.extract(transcript, BEHAVIORAL_QUESTION_TYPE);

      const actionsSlot = result.slots.find((s) => s.name === 'actions');
      if (actionsSlot) {
        expect(Array.isArray(actionsSlot.value)).toBe(true);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw TRANSFORMATION_FAILED when transcript is null', () => {
      try {
        SlotExtractor.extract(null as unknown as string, BEHAVIORAL_QUESTION_TYPE);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSFORMATION_FAILED');
      }
    });

    it('should throw TRANSFORMATION_FAILED when transcript is undefined', () => {
      try {
        SlotExtractor.extract(undefined as unknown as string, BEHAVIORAL_QUESTION_TYPE);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSFORMATION_FAILED');
      }
    });

    it('should throw TRANSFORMATION_FAILED when questionType is null', () => {
      try {
        SlotExtractor.extract('Some transcript', null as unknown as QuestionTypeDefinition);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSFORMATION_FAILED');
      }
    });

    it('should throw TRANSFORMATION_FAILED when transcript is empty string', () => {
      try {
        SlotExtractor.extract('', BEHAVIORAL_QUESTION_TYPE);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSFORMATION_FAILED');
      }
    });
  });
});
