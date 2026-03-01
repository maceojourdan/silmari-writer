/**
 * ProcessVoiceResponseHandler - Validates voice response payload and session state,
 * then delegates to SessionProgressionService for processing.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 307-process-voice-input-and-progress-session
 *
 * Flow:
 * 1. Validate payload (sessionId + transcript)
 * 2. Fetch session via SessionDAO
 * 3. Validate session state (must be INIT)
 * 4. Forward to SessionProgressionService
 *
 * Error handling:
 * - Invalid payload → SessionErrors.INVALID_PAYLOAD
 * - Session not found or not INIT → SessionErrors.INVALID_STATE
 * - Known SessionError → rethrown as-is
 * - Unknown errors → logged and wrapped in GenericErrors.InternalError
 */

import type { SessionWithStoryRecord } from '@/server/data_structures/AnswerSession';
import { SubmitVoiceResponseRequestSchema } from '@/api_contracts/submitVoiceResponse';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { SessionProgressionService } from '@/server/services/SessionProgressionService';
import { SessionErrors, SessionError } from '@/server/error_definitions/SessionErrors';
import { GenericErrors } from '@/server/error_definitions/GenericErrors';
import { logger } from '@/server/logging/logger';

export interface ProcessVoiceResponseInput {
  sessionId: string;
  transcript: string;
}

export const ProcessVoiceResponseHandler = {
  /**
   * Handle the voice response processing flow:
   * 1. Validate payload via Zod schema
   * 2. Fetch and validate session state
   * 3. Delegate to SessionProgressionService
   *
   * @param payload - Raw input with sessionId and transcript
   * @returns SessionWithStoryRecord with updated entities
   */
  async handle(payload: ProcessVoiceResponseInput): Promise<SessionWithStoryRecord> {
    try {
      // Step 1: Validate payload
      const validation = SubmitVoiceResponseRequestSchema.safeParse(payload);
      if (!validation.success) {
        const details = validation.error.issues
          .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
          .join('; ');
        throw SessionErrors.InvalidPayload(`Invalid voice response payload: ${details}`);
      }

      const { sessionId, transcript } = validation.data;

      // Step 2: Fetch session
      const session = await SessionDAO.findAnswerSessionById(sessionId);
      if (!session) {
        throw SessionErrors.InvalidState(`Session ${sessionId} not found`);
      }

      // Step 3: Validate session state (must be INIT)
      if (session.state !== 'INIT') {
        throw SessionErrors.InvalidState(
          `Session ${sessionId} is in ${session.state} state, expected INIT`,
        );
      }

      // Step 4: Delegate to service
      const result = await SessionProgressionService.progressSession(session, transcript);

      return result;
    } catch (error) {
      // Known session errors → rethrow
      if (error instanceof SessionError) {
        throw error;
      }

      // Unknown errors → log and wrap
      logger.error(
        'Unexpected error processing voice response',
        error,
        { path: '307-process-voice-input-and-progress-session', resource: 'api-n8k2' },
      );

      throw GenericErrors.InternalError(
        `Unexpected error processing voice response: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
