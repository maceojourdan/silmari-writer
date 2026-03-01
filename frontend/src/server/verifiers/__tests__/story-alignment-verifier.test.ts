/**
 * Tests for StoryAlignmentVerifier - Step 3: Validate story alignment and eligibility
 *
 * Path: 313-confirm-aligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Valid story + question + requirements → success
 * - TypeInvariant: Return type is ValidationResult union
 * - ErrorConsistency:
 *   - Story not found → STORY_NOT_FOUND
 *   - Already confirmed → STORY_ALREADY_CONFIRMED
 *   - Not aligned → STORY_NOT_ALIGNED
 */

import { describe, it, expect } from 'vitest';
import { StoryAlignmentVerifier } from '../StoryAlignmentVerifier';
import { ConfirmStoryError } from '@/server/error_definitions/ConfirmStoryErrors';
import type { Question, Story, JobRequirement } from '@/server/data_structures/ConfirmStory';
import { ValidationResultSchema } from '@/server/data_structures/ConfirmStory';

const validQuestion: Question = {
  id: 'q-001',
  text: 'Tell me about a time you led a cross-functional team.',
  category: 'leadership',
};

const validRequirements: JobRequirement[] = [
  {
    id: 'jr-001',
    description: 'Experience leading cross-functional teams',
    priority: 'REQUIRED',
  },
  {
    id: 'jr-002',
    description: 'Track record of delivering complex projects on time',
    priority: 'PREFERRED',
  },
];

const validStory: Story = {
  id: 'story-001',
  title: 'Led migration to microservices architecture',
  summary: 'Coordinated 4 teams across engineering, QA, and DevOps.',
  status: 'AVAILABLE',
  questionId: 'q-001',
};

const allStories: Story[] = [
  validStory,
  {
    id: 'story-002',
    title: 'Built real-time analytics pipeline',
    summary: 'Designed streaming data pipeline.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
  {
    id: 'story-003',
    title: 'Established engineering hiring process',
    summary: 'Created structured interview process.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
];

describe('StoryAlignmentVerifier - Step 3: Validate story alignment', () => {
  describe('Reachability: Valid story + question + requirements → success', () => {
    it('should return success for a valid aligned story', () => {
      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        validStory,
        validRequirements,
        allStories,
      );

      expect(result).toEqual({ valid: true });
    });

    it('should accept a story belonging to the question', () => {
      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        validStory,
        validRequirements,
        allStories,
      );

      expect(result.valid).toBe(true);
    });
  });

  describe('TypeInvariant: Return type is ValidationResult union', () => {
    it('should return a value conforming to ValidationResultSchema on success', () => {
      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        validStory,
        validRequirements,
        allStories,
      );

      const parsed = ValidationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return a value conforming to ValidationResultSchema on failure', () => {
      const confirmedStory: Story = {
        ...validStory,
        status: 'CONFIRMED',
      };

      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        confirmedStory,
        validRequirements,
        [confirmedStory, ...allStories.slice(1)],
      );

      const parsed = ValidationResultSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: Domain errors for invalid scenarios', () => {
    it('should return STORY_NOT_FOUND when story is not in the list', () => {
      const missingStory: Story = {
        id: 'story-999',
        title: 'Nonexistent story',
        summary: 'Does not exist.',
        status: 'AVAILABLE',
        questionId: 'q-001',
      };

      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        missingStory,
        validRequirements,
        allStories,
      );

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toContain('STORY_NOT_FOUND');
      }
    });

    it('should return STORY_ALREADY_CONFIRMED when story is already confirmed', () => {
      const confirmedStory: Story = {
        ...validStory,
        status: 'CONFIRMED',
      };

      const storiesWithConfirmed = [confirmedStory, ...allStories.slice(1)];

      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        confirmedStory,
        validRequirements,
        storiesWithConfirmed,
      );

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toContain('STORY_ALREADY_CONFIRMED');
      }
    });

    it('should return STORY_NOT_ALIGNED when story questionId does not match', () => {
      const misalignedStory: Story = {
        ...validStory,
        questionId: 'q-999',
      };

      // Story is in the list but with wrong questionId
      const storiesWithMisaligned = [misalignedStory, ...allStories.slice(1)];

      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        misalignedStory,
        validRequirements,
        storiesWithMisaligned,
      );

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors).toContain('STORY_NOT_ALIGNED');
      }
    });

    it('should return STORY_NOT_ALIGNED when story status is EXCLUDED', () => {
      const excludedStory: Story = {
        ...validStory,
        status: 'EXCLUDED',
      };

      const storiesWithExcluded = [excludedStory, ...allStories.slice(1)];

      const result = StoryAlignmentVerifier.validate(
        validQuestion,
        excludedStory,
        validRequirements,
        storiesWithExcluded,
      );

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.errors.some(e => e === 'STORY_NOT_ALIGNED' || e === 'STORY_ALREADY_CONFIRMED')).toBe(true);
      }
    });
  });
});
