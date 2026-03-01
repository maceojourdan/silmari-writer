/**
 * OrientProcessChain - Activates the ORIENT state logic and provides
 * experience selection for story record creation.
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 295-orient-state-creates-single-story-record
 */

import type {
  OrientEvent,
  OrientExecutionContext,
  StoryCreationPayload,
} from '@/server/data_structures/OrientStoryRecord';
import { OrientErrors } from '@/server/error_definitions/OrientErrors';

// ---------------------------------------------------------------------------
// Internal process chain registry
// ---------------------------------------------------------------------------

const ORIENT_CHAIN_KEY = 'ORIENT';

const defaultRegistry = new Map<string, boolean>([
  [ORIENT_CHAIN_KEY, true],
]);

// ---------------------------------------------------------------------------
// Options for testability
// ---------------------------------------------------------------------------

export interface OrientProcessChainOptions {
  /** Override the internal registry (useful for testing unregistered chain) */
  registryOverride?: Map<string, boolean>;
}

// ---------------------------------------------------------------------------
// Process chain functions
// ---------------------------------------------------------------------------

export const OrientProcessChain = {
  /**
   * Step 1: Trigger ORIENT process chain.
   *
   * Validates that the ORIENT chain is registered, then returns
   * the execution context containing candidate experiences.
   */
  startOrientProcess(
    event: OrientEvent,
    options?: OrientProcessChainOptions,
  ): OrientExecutionContext {
    const registry = options?.registryOverride ?? defaultRegistry;

    if (!registry.has(ORIENT_CHAIN_KEY)) {
      throw OrientErrors.SystemProcessChainNotFound(
        `Process chain '${ORIENT_CHAIN_KEY}' is not registered`,
      );
    }

    return {
      experiences: event.experiences,
    };
  },

  /**
   * Step 2: Select single experience and derive story data.
   *
   * Evaluates available experiences, selects exactly one, and derives
   * a story_title + initial_context from the selected experience.
   */
  selectExperience(context: OrientExecutionContext): StoryCreationPayload {
    const validExperiences = context.experiences.filter(
      (exp) => exp.id && exp.title && exp.summary,
    );

    if (validExperiences.length === 0) {
      throw OrientErrors.NoValidExperienceSelected(
        'No valid experience found in execution context',
      );
    }

    // Business rule (minimal for path): select first valid experience
    const selected = validExperiences[0];

    return {
      story_title: selected.title,
      initial_context: {
        experienceId: selected.id,
        summary: selected.summary,
      },
    };
  },
} as const;
