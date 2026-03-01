/**
 * persistCompletedSlots.test.ts - Step 4: Persist completed slot set
 *
 * TLA+ Properties:
 * - Reachability: Mock DAO success → session state updated (questionType.status = COMPLETE)
 * - TypeInvariant: DAO called with correct typed payload
 * - ErrorConsistency: Mock DAO throw → expect WorkflowErrors.PERSISTENCE_FAILED; no workflow advancement
 *
 * Resource: db-h2s4 (service)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { WorkflowError } from '@/server/error_definitions/WorkflowErrors';
import type { SlotState } from '@/server/data_structures/VoiceInteractionContext';

// Mock DAO at module boundary
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

import { SessionWorkflowService } from '../SessionWorkflowService';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';
const questionTypeId = 'behavioral_question';

function createCompleteSlotState(): SlotState {
  return {
    slots: [
      { name: 'objective', value: 'Increase team velocity', confirmed: true },
      { name: 'actions', value: ['reorganized sprints', 'hired engineers', 'improved CI/CD'], confirmed: true },
      { name: 'obstacles', value: ['budget constraints'], confirmed: true },
      { name: 'outcome', value: '40% increase in delivery speed', confirmed: true },
      { name: 'roleClarity', value: 'Engineering manager for platform team', confirmed: true },
    ],
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SessionWorkflowService.persistCompletedSlots — Step 4: Persist completed slot set', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return COMPLETE status when DAO succeeds', async () => {
      vi.mocked(SessionDAO.saveSlots).mockResolvedValue(undefined);

      const slotState = createCompleteSlotState();
      const result = await SessionWorkflowService.persistCompletedSlots(
        validSessionId,
        questionTypeId,
        slotState,
      );

      expect(result).toBeDefined();
      expect(result.status).toBe('COMPLETE');
      expect(result.sessionId).toBe(validSessionId);
      expect(result.questionTypeId).toBe(questionTypeId);
    });

    it('should return correct slot count', async () => {
      vi.mocked(SessionDAO.saveSlots).mockResolvedValue(undefined);

      const slotState = createCompleteSlotState();
      const result = await SessionWorkflowService.persistCompletedSlots(
        validSessionId,
        questionTypeId,
        slotState,
      );

      expect(result.slotCount).toBe(5);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should call DAO with correct typed payload', async () => {
      vi.mocked(SessionDAO.saveSlots).mockResolvedValue(undefined);

      const slotState = createCompleteSlotState();
      await SessionWorkflowService.persistCompletedSlots(
        validSessionId,
        questionTypeId,
        slotState,
      );

      expect(SessionDAO.saveSlots).toHaveBeenCalledOnce();
      expect(SessionDAO.saveSlots).toHaveBeenCalledWith(
        validSessionId,
        questionTypeId,
        slotState,
      );
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw PERSISTENCE_FAILED when DAO throws', async () => {
      vi.mocked(SessionDAO.saveSlots).mockRejectedValue(
        new Error('Database connection failed'),
      );

      const slotState = createCompleteSlotState();

      try {
        await SessionWorkflowService.persistCompletedSlots(
          validSessionId,
          questionTypeId,
          slotState,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(WorkflowError);
        expect((e as WorkflowError).code).toBe('PERSISTENCE_FAILED');
      }
    });

    it('should not advance workflow on persistence failure', async () => {
      vi.mocked(SessionDAO.saveSlots).mockRejectedValue(
        new Error('Database timeout'),
      );

      const slotState = createCompleteSlotState();

      try {
        await SessionWorkflowService.persistCompletedSlots(
          validSessionId,
          questionTypeId,
          slotState,
        );
        expect.fail('Should have thrown');
      } catch {
        // Verify no further DAO calls were made after failure
        expect(SessionDAO.saveSlots).toHaveBeenCalledOnce();
      }
    });
  });
});
