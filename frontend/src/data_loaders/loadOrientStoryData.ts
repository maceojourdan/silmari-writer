/**
 * loadOrientStoryData - Data loader for the orient story selection screen.
 *
 * Fetches question, job requirements, and available stories from the backend
 * API endpoint for display in the OrientStoryModule.
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 313-confirm-aligned-story-selection
 */

import type { OrientStoryData } from '@/server/data_structures/ConfirmStory';
import { OrientStoryDataSchema } from '@/server/data_structures/ConfirmStory';
import { ConfirmStoryError, ConfirmStoryErrors } from '@/server/error_definitions/ConfirmStoryErrors';

/**
 * Fetch orient story context from the backend API.
 *
 * Calls GET /api/story/orient-context?questionId={questionId}
 * Validates response against OrientStoryDataSchema.
 *
 * @throws ConfirmStoryError on retrieval or validation failure
 */
export async function loadOrientStoryData(questionId: string): Promise<OrientStoryData> {
  try {
    const response = await fetch(`/api/story/orient-context?questionId=${encodeURIComponent(questionId)}`);

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new ConfirmStoryError(
        errorBody.message || `Failed to load orient story data (status ${response.status})`,
        errorBody.code || 'DATA_NOT_FOUND',
        response.status,
        response.status >= 500,
      );
    }

    const data = await response.json();
    const parsed = OrientStoryDataSchema.safeParse(data);

    if (!parsed.success) {
      const details = parsed.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      throw ConfirmStoryErrors.DataNotFound(
        `Invalid orient story data from server: ${details}`,
      );
    }

    return parsed.data;
  } catch (error) {
    if (error instanceof ConfirmStoryError) {
      throw error;
    }

    throw ConfirmStoryErrors.DataNotFound(
      `Failed to load orient story data: ${error instanceof Error ? error.message : 'unknown error'}`,
    );
  }
}
