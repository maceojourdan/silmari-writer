/**
 * SessionWorkflowService - Orchestrates the complete voice answer workflow:
 * capturing spoken answers, persisting completed slots, and coordinating
 * workflow advancement.
 *
 * Resource: db-h2s4 (service)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import type {
  VoiceInteractionContext,
  SlotState,
} from '@/server/data_structures/VoiceInteractionContext';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';
import { WorkflowErrors } from '@/server/error_definitions/WorkflowErrors';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { workflowVoiceLogger } from '@/server/logging/workflowVoiceLogger';
import type { TranscriptionClient } from './VoiceRecallService';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface CaptureSpokenAnswerResult {
  transcript: string;
  questionTypeId: string;
}

export interface PersistCompletedSlotsResult {
  sessionId: string;
  questionTypeId: string;
  status: 'COMPLETE';
  slotCount: number;
}

// ---------------------------------------------------------------------------
// Default transcription client (stub — not yet wired to ElevenLabs)
// ---------------------------------------------------------------------------

const defaultTranscriptionClient: TranscriptionClient = {
  async transcribe(_audioBlob: Blob): Promise<{ transcript: string }> {
    throw new Error('TranscriptionClient.transcribe not yet wired to ElevenLabs SDK');
  },
};

// ---------------------------------------------------------------------------
// Service
// ---------------------------------------------------------------------------

export const SessionWorkflowService = {
  // -------------------------------------------------------------------------
  // Step 1: Capture spoken answer
  // -------------------------------------------------------------------------

  /**
   * Converts spoken audio into structured textual input and associates it
   * with the active question_type session context.
   *
   * @param context - Active voice interaction context
   * @param audioBlob - Raw audio data from user
   * @param client - Transcription client (mockable)
   * @returns { transcript, questionTypeId }
   * @throws VoiceError(TRANSCRIPTION_FAILED) on empty/failed transcription
   */
  async captureSpokenAnswer(
    context: VoiceInteractionContext,
    audioBlob: Blob,
    client: TranscriptionClient = defaultTranscriptionClient,
  ): Promise<CaptureSpokenAnswerResult> {
    let transcript: string;

    try {
      const result = await client.transcribe(audioBlob);
      transcript = result.transcript;
    } catch (error) {
      workflowVoiceLogger.error('Transcription client failed', error, {
        sessionId: context.sessionId,
        retryCount: context.retryCount,
      });

      if (context.retryCount >= context.maxRetries) {
        const err = VoiceErrors.TRANSCRIPTION_FAILED(
          'Transcription failed after maximum retries — escalating',
        );
        err.retryable = false;
        throw err;
      }

      throw VoiceErrors.TRANSCRIPTION_FAILED('Transcription failed');
    }

    // Empty transcript → recoverable error with retry tracking
    if (!transcript || transcript.trim() === '') {
      workflowVoiceLogger.warn('Empty transcript received', {
        sessionId: context.sessionId,
        retryCount: context.retryCount,
      });

      if (context.retryCount >= context.maxRetries) {
        const err = VoiceErrors.TRANSCRIPTION_FAILED(
          'Transcription returned empty output after maximum retries — escalating',
        );
        err.retryable = false;
        throw err;
      }

      throw VoiceErrors.TRANSCRIPTION_FAILED(
        'Transcription returned empty output',
      );
    }

    workflowVoiceLogger.info('Captured spoken answer successfully', {
      sessionId: context.sessionId,
      questionTypeId: context.questionType.name,
      transcriptLength: transcript.length,
    });

    return {
      transcript: transcript.trim(),
      questionTypeId: context.questionType.name,
    };
  },

  // -------------------------------------------------------------------------
  // Step 4: Persist completed slot set
  // -------------------------------------------------------------------------

  /**
   * Stores the completed slot values and marks the question_type as complete.
   *
   * @param sessionId - Session to update
   * @param questionTypeId - Question type being completed
   * @param slotState - Validated slot state to persist
   * @returns Persistence result with status COMPLETE
   * @throws WorkflowError(PERSISTENCE_FAILED) on DAO failure
   */
  async persistCompletedSlots(
    sessionId: string,
    questionTypeId: string,
    slotState: SlotState,
  ): Promise<PersistCompletedSlotsResult> {
    try {
      await SessionDAO.saveSlots(sessionId, questionTypeId, slotState);

      workflowVoiceLogger.info('Completed slots persisted successfully', {
        sessionId,
        questionTypeId,
        slotCount: slotState.slots.length,
      });

      return {
        sessionId,
        questionTypeId,
        status: 'COMPLETE',
        slotCount: slotState.slots.length,
      };
    } catch (error) {
      workflowVoiceLogger.error('Failed to persist completed slots', error, {
        sessionId,
        questionTypeId,
      });

      throw WorkflowErrors.PERSISTENCE_FAILED(
        `Failed to persist completed slots for session ${sessionId}`,
      );
    }
  },
} as const;
