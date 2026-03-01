/**
 * ApproveStoryRequestHandler - Maps request DTO to ApproveStoryCommand
 * and delegates to ApproveStoryProcessor.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

import type { ApproveDraftPayload } from '@/verifiers/ApproveDraftVerifier';
import type { AuthContext } from '@/server/filters/AuthAndValidationFilter';
import type { ApproveStoryCommand, PersistenceResult } from '@/server/data_structures/StoryRecord';
import { ApproveStoryProcessor } from '@/server/processors/ApproveStoryProcessor';

export const ApproveStoryRequestHandler = {
  /**
   * Map validated request body + auth context → ApproveStoryCommand.
   */
  toCommand(body: ApproveDraftPayload, auth: AuthContext): ApproveStoryCommand {
    return {
      draftId: body.draftId,
      resumeId: body.resumeId,
      jobId: body.jobId,
      questionId: body.questionId,
      voiceSessionId: body.voiceSessionId,
      userId: auth.userId,
    };
  },

  /**
   * Handle the full request flow: transform → process.
   */
  async handle(
    body: ApproveDraftPayload,
    auth: AuthContext,
  ): Promise<PersistenceResult> {
    const command = this.toCommand(body, auth);
    return ApproveStoryProcessor.process(command);
  },
} as const;
