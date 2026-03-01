/**
 * VoiceResponseProcessor - Processes voice response content and determines
 * the next session state.
 *
 * Resource: db-b7r2 (processor)
 * Path: 307-process-voice-input-and-progress-session
 *
 * Given a transcript and current session, determines:
 * - The next session state based on transition rules
 * - The updated story record content
 */

import type { AnswerSession, AnswerSessionState } from '@/server/data_structures/AnswerSession';
import { AnswerSessionState as States } from '@/server/data_structures/AnswerSession';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface VoiceResponseProcessorResult {
  nextState: AnswerSessionState;
  updatedContent: string;
}

// ---------------------------------------------------------------------------
// Processor
// ---------------------------------------------------------------------------

export const VoiceResponseProcessor = {
  /**
   * Process a voice transcript and determine the next session state.
   *
   * For INIT sessions, transitions to IN_PROGRESS.
   * The transcript becomes the story record content.
   *
   * @param transcript - The user's voice transcript
   * @param session - The current AnswerSession
   * @returns VoiceResponseProcessorResult with next state and updated content
   */
  process(transcript: string, session: AnswerSession): VoiceResponseProcessorResult {
    // Determine next state based on current state
    switch (session.state) {
      case States.INIT:
        return {
          nextState: States.IN_PROGRESS,
          updatedContent: transcript,
        };
      default:
        // For any other state, return current state (no transition)
        return {
          nextState: session.state,
          updatedContent: transcript,
        };
    }
  },
} as const;
