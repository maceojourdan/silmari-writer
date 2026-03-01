/**
 * AdvanceWorkflowChain.test.ts - Step 5: Advance workflow to next step
 *
 * TLA+ Properties:
 * - Reachability: Input session with completed question_type → expect next state (VERIFY)
 * - TypeInvariant: Returned state matches enum SessionState (AnswerSessionState)
 * - ErrorConsistency: Mock resolution failure → expect WorkflowErrors.TRANSITION_FAILED
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { WorkflowError } from '@/server/error_definitions/WorkflowErrors';
import { AnswerSessionState } from '@/server/data_structures/AnswerSession';
import type { AnswerSession } from '@/server/data_structures/AnswerSession';

// Mock DAO
vi.mock('@/server/data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    saveSlots: vi.fn(),
    findById: vi.fn(),
    updateState: vi.fn(),
    createSession: vi.fn(),
    createStoryRecord: vi.fn(),
    deleteSession: vi.fn(),
    findAnswerSessionById: vi.fn(),
    findStoryRecordBySessionId: vi.fn(),
    updateSessionAndStoryRecord: vi.fn(),
    updateAnswerSessionState: vi.fn(),
  },
}));

// Mock logger
vi.mock('@/server/logging/workflowVoiceLogger', () => ({
  workflowVoiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { AdvanceWorkflowChain } from '../AdvanceWorkflowChain';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';
const now = new Date().toISOString();

function createSession(state: string): AnswerSession {
  return {
    id: validSessionId,
    userId: 'user-123',
    state: state as AnswerSession['state'],
    createdAt: now,
    updatedAt: now,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('AdvanceWorkflowChain.execute — Step 5: Advance workflow to next step', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should transition from COMPLETE to VERIFY', async () => {
      const session = createSession('COMPLETE');
      const updatedSession = createSession('VERIFY');
      vi.mocked(SessionDAO.updateAnswerSessionState).mockResolvedValue(updatedSession);

      const result = await AdvanceWorkflowChain.execute(session);

      expect(result).toBeDefined();
      expect(result.nextState).toBe('VERIFY');
      expect(result.recallLoopDisabled).toBe(true);
    });

    it('should call DAO to persist the state transition', async () => {
      const session = createSession('COMPLETE');
      const updatedSession = createSession('VERIFY');
      vi.mocked(SessionDAO.updateAnswerSessionState).mockResolvedValue(updatedSession);

      await AdvanceWorkflowChain.execute(session);

      expect(SessionDAO.updateAnswerSessionState).toHaveBeenCalledOnce();
      expect(SessionDAO.updateAnswerSessionState).toHaveBeenCalledWith(
        validSessionId,
        AnswerSessionState.VERIFY,
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result matching AdvanceWorkflowResult type', async () => {
      const session = createSession('COMPLETE');
      const updatedSession = createSession('VERIFY');
      vi.mocked(SessionDAO.updateAnswerSessionState).mockResolvedValue(updatedSession);

      const result = await AdvanceWorkflowChain.execute(session);

      expect(typeof result.nextState).toBe('string');
      expect(typeof result.recallLoopDisabled).toBe('boolean');
      expect(typeof result.sessionId).toBe('string');
    });

    it('should return a valid AnswerSessionState value', async () => {
      const session = createSession('COMPLETE');
      const updatedSession = createSession('VERIFY');
      vi.mocked(SessionDAO.updateAnswerSessionState).mockResolvedValue(updatedSession);

      const result = await AdvanceWorkflowChain.execute(session);

      const validStates = Object.values(AnswerSessionState);
      expect(validStates).toContain(result.nextState);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw TRANSITION_FAILED when DAO fails', async () => {
      const session = createSession('COMPLETE');
      vi.mocked(SessionDAO.updateAnswerSessionState).mockRejectedValue(
        new Error('Database unreachable'),
      );

      try {
        await AdvanceWorkflowChain.execute(session);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(WorkflowError);
        expect((e as WorkflowError).code).toBe('TRANSITION_FAILED');
      }
    });

    it('should throw TRANSITION_FAILED when no valid next state exists', async () => {
      const session = createSession('VERIFY');

      try {
        await AdvanceWorkflowChain.execute(session);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(WorkflowError);
        expect((e as WorkflowError).code).toBe('TRANSITION_FAILED');
      }
    });
  });
});
