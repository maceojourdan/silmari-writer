/**
 * AdvanceWorkflowChain - Determines and executes the next step in the
 * workflow once all required slots are complete.
 *
 * Inspects the session state machine, transitions to the next defined
 * state, and disables the recall loop flag.
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import type { AnswerSession, AnswerSessionState } from '@/server/data_structures/AnswerSession';
import { VALID_STATE_TRANSITIONS } from '@/server/data_structures/AnswerSession';
import { WorkflowErrors } from '@/server/error_definitions/WorkflowErrors';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { workflowVoiceLogger } from '@/server/logging/workflowVoiceLogger';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface AdvanceWorkflowResult {
  sessionId: string;
  nextState: AnswerSessionState;
  recallLoopDisabled: boolean;
}

// ---------------------------------------------------------------------------
// AdvanceWorkflowChain
// ---------------------------------------------------------------------------

export const AdvanceWorkflowChain = {
  /**
   * Determine and activate the next step in the workflow.
   *
   * Inspects the session state machine to find the valid next state,
   * transitions to it, and disables the recall loop flag.
   *
   * @param session - AnswerSession with completed question_type
   * @returns AdvanceWorkflowResult with next state and recall loop status
   * @throws WorkflowError(TRANSITION_FAILED) on resolution failure or no valid transition
   */
  async execute(session: AnswerSession): Promise<AdvanceWorkflowResult> {
    const currentState = session.state as AnswerSessionState;
    const validNextStates = VALID_STATE_TRANSITIONS[currentState];

    if (!validNextStates || validNextStates.length === 0) {
      workflowVoiceLogger.error('No valid state transition available', undefined, {
        sessionId: session.id,
        currentState,
      });

      throw WorkflowErrors.TRANSITION_FAILED(
        `No valid transition from state "${currentState}" for session ${session.id}`,
      );
    }

    // Take the first valid next state
    const nextState = validNextStates[0];

    try {
      await SessionDAO.updateAnswerSessionState(session.id, nextState);

      workflowVoiceLogger.info('Workflow advanced successfully', {
        sessionId: session.id,
        previousState: currentState,
        nextState,
      });

      return {
        sessionId: session.id,
        nextState,
        recallLoopDisabled: true,
      };
    } catch (error) {
      workflowVoiceLogger.error('Failed to advance workflow', error, {
        sessionId: session.id,
        currentState,
        targetState: nextState,
      });

      throw WorkflowErrors.TRANSITION_FAILED(
        `Failed to transition session ${session.id} from "${currentState}" to "${nextState}"`,
      );
    }
  },
} as const;
