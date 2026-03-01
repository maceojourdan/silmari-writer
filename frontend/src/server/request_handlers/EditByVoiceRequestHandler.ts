/**
 * EditByVoiceRequestHandler - Orchestrates voice edit flow:
 * service (validate instruction + fetch content + transform + persist) → response.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 330-edit-content-by-voice-from-review-screen
 *
 * Known errors (EditByVoiceError) are rethrown as-is.
 * Unknown errors are logged and wrapped in GenericErrors.InternalError.
 */

import { EditByVoiceService } from '@/server/services/EditByVoiceService';
import { EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';
import type { ContentEntity } from '@/server/data_structures/ContentEntity';

export interface EditByVoiceHandlerResult {
  updatedContent: ContentEntity;
}

export const EditByVoiceRequestHandler = {
  /**
   * Handle the full edit-by-voice flow:
   * 1. Delegate to service (validate instruction + fetch + transform + persist)
   * 2. Return updated content entity
   */
  async handle(
    contentId: string,
    instructionText: string,
  ): Promise<EditByVoiceHandlerResult> {
    try {
      const updatedContent = await EditByVoiceService.processInstruction(
        contentId,
        instructionText,
      );

      return { updatedContent };
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof EditByVoiceError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error during edit-by-voice processing',
        error,
        { path: '330-edit-content-by-voice-from-review-screen', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error during edit-by-voice: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
