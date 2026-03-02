/**
 * AnswerService - Handles answer content updates with lock-state validation.
 *
 * Resource: db-h2s4 (service)
 * Path: 337-prevent-edit-of-locked-answer
 *
 * 1. Load answer via DAO
 * 2. If not found → throw ANSWER_NOT_FOUND
 * 3. If locked → throw LOCKED_ANSWER_MODIFICATION_FORBIDDEN
 * 4. Update content via DAO
 * 5. Return { id, content }
 *
 * DAO errors are wrapped in PERSISTENCE_ERROR.
 */

import { z } from 'zod';
import { AnswerDAO } from '@/server/data_access_objects/AnswerDAO';
import { AnswerError, AnswerErrors } from '@/server/error_definitions/AnswerErrors';

// ---------------------------------------------------------------------------
// Result Schema
// ---------------------------------------------------------------------------

export const UpdateAnswerResultSchema = z.object({
  id: z.string().uuid(),
  content: z.string(),
});

export type UpdateAnswerResult = z.infer<typeof UpdateAnswerResultSchema>;

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const AnswerService = {
  /**
   * Update the content of an answer, rejecting if the answer is locked.
   *
   * Steps:
   *   1. Load answer via DAO.findById
   *   2. If null → throw AnswerErrors.AnswerNotFound
   *   3. If locked === true → throw AnswerErrors.LockedAnswerModificationForbidden
   *   4. Update content via DAO.updateContent
   *   5. Return { id, content } from the updated answer
   *
   * On DAO error: wrap in AnswerErrors.PersistenceError
   */
  async updateAnswer(id: string, content: string): Promise<UpdateAnswerResult> {
    // Step 1: Load answer
    let answer;
    try {
      answer = await AnswerDAO.findById(id);
    } catch (error) {
      if (error instanceof AnswerError) throw error;
      throw AnswerErrors.PersistenceError(
        `Failed to load answer '${id}': ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }

    // Step 2: Not found check
    if (!answer) {
      throw AnswerErrors.AnswerNotFound(`Answer '${id}' not found`);
    }

    // Step 3: Lock check
    if (answer.locked) {
      throw AnswerErrors.LockedAnswerModificationForbidden();
    }

    // Step 4: Update content
    let updated;
    try {
      updated = await AnswerDAO.updateContent(id, content);
    } catch (error) {
      if (error instanceof AnswerError) throw error;
      throw AnswerErrors.PersistenceError(
        `Failed to update answer '${id}': ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }

    // Step 5: Return result
    return {
      id: updated.id,
      content: updated.content,
    };
  },
} as const;
