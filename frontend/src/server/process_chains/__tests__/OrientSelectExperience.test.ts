/**
 * Tests for OrientProcessChain.selectExperience
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 295-orient-state-creates-single-story-record
 *
 * TLA+ properties tested:
 * - Reachability: Provide execution context → returned payload has story_title and initial_context
 * - TypeInvariant: Payload matches StoryCreationPayload type
 * - ErrorConsistency: Empty/invalid experiences → NO_VALID_EXPERIENCE_SELECTED
 */

import { describe, it, expect } from 'vitest';
import { OrientProcessChain } from '../OrientProcessChain';
import { OrientError } from '../../error_definitions/OrientErrors';
import {
  StoryCreationPayloadSchema,
  type OrientExecutionContext,
  type Experience,
} from '../../data_structures/OrientStoryRecord';

const validExperiences: Experience[] = [
  { id: 'exp-1', title: 'Led migration to microservices', summary: 'Broke monolith into 12 services' },
  { id: 'exp-2', title: 'Built real-time analytics', summary: 'Streaming pipeline processing 1M events/s' },
];

describe('OrientProcessChain.selectExperience', () => {
  describe('Reachability: execution context → payload with story_title and initial_context', () => {
    it('should return payload with story_title and initial_context from first valid experience', () => {
      const context: OrientExecutionContext = { experiences: validExperiences };
      const payload = OrientProcessChain.selectExperience(context);

      expect(payload.story_title).toBe('Led migration to microservices');
      expect(payload.initial_context).toEqual({
        experienceId: 'exp-1',
        summary: 'Broke monolith into 12 services',
      });
    });

    it('should select exactly one experience even when multiple are valid', () => {
      const context: OrientExecutionContext = { experiences: validExperiences };
      const payload = OrientProcessChain.selectExperience(context);

      // Should always derive from a single experience
      expect(typeof payload.story_title).toBe('string');
      expect(payload.initial_context.experienceId).toBeDefined();
    });
  });

  describe('TypeInvariant: payload matches StoryCreationPayload', () => {
    it('should return an object that satisfies StoryCreationPayloadSchema', () => {
      const context: OrientExecutionContext = { experiences: validExperiences };
      const payload = OrientProcessChain.selectExperience(context);

      const parsed = StoryCreationPayloadSchema.safeParse(payload);
      expect(parsed.success).toBe(true);
    });

    it('should have story_title as string and initial_context as object', () => {
      const context: OrientExecutionContext = { experiences: validExperiences };
      const payload = OrientProcessChain.selectExperience(context);

      expect(typeof payload.story_title).toBe('string');
      expect(typeof payload.initial_context).toBe('object');
      expect(typeof payload.initial_context.experienceId).toBe('string');
      expect(typeof payload.initial_context.summary).toBe('string');
    });
  });

  describe('ErrorConsistency: empty/invalid experiences → NO_VALID_EXPERIENCE_SELECTED', () => {
    it('should throw OrientError when experiences array is empty', () => {
      const context: OrientExecutionContext = { experiences: [] };

      expect(() => OrientProcessChain.selectExperience(context)).toThrow(OrientError);
    });

    it('should throw with code NO_VALID_EXPERIENCE_SELECTED for empty experiences', () => {
      const context: OrientExecutionContext = { experiences: [] };

      try {
        OrientProcessChain.selectExperience(context);
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(OrientError);
        expect((e as OrientError).code).toBe('NO_VALID_EXPERIENCE_SELECTED');
      }
    });

    it('should throw when all experiences have empty titles', () => {
      const context: OrientExecutionContext = {
        experiences: [
          { id: 'exp-1', title: '', summary: 'Some summary' },
          { id: 'exp-2', title: '', summary: 'Another summary' },
        ],
      };

      expect(() => OrientProcessChain.selectExperience(context)).toThrow(OrientError);
    });

    it('should throw when all experiences have empty ids', () => {
      const context: OrientExecutionContext = {
        experiences: [
          { id: '', title: 'A title', summary: 'Some summary' },
        ],
      };

      expect(() => OrientProcessChain.selectExperience(context)).toThrow(OrientError);
    });
  });
});
