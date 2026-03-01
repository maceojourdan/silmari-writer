/**
 * Terminal Condition Integration Test: transition-to-verify-when-minimum-slots-filled
 *
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Proves Reachability from trigger → VERIFY badge:
 * 1. Validate minimum slots (frontend verifier)
 * 2. Submit to backend handler
 * 3. Backend re-validates via verifier
 * 4. Service orchestrates DAO update
 * 5. Status transitions to VERIFY
 *
 * Only mocks at the DAO boundary (Supabase layer).
 */

import { validateMinimumSlots } from '@/verifiers/behavioralQuestionVerifier';
import { BehavioralQuestionEvaluateHandler } from '@/server/request_handlers/BehavioralQuestionEvaluateHandler';
import { BehavioralQuestionDAO } from '@/server/data_access_objects/BehavioralQuestionDAO';
import { BehavioralQuestionError } from '@/server/error_definitions/BehavioralQuestionErrors';
import type { BehavioralQuestion, EvaluateResult } from '@/server/data_structures/BehavioralQuestion';

// Only mock at the DAO boundary
const mockUpdateStatus = vi.fn();

vi.mock('@/server/data_access_objects/BehavioralQuestionDAO', () => ({
  BehavioralQuestionDAO: {
    updateStatus: (...args: unknown[]) => mockUpdateStatus(...args),
  },
}));

// Seed data representing a fully-filled behavioral question
const seedDraft = {
  sessionId: 'session-integration-001',
  objective: 'Led a cross-functional team of 12 engineers to migrate our monolithic payment processing system to microservices architecture',
  actions: [
    'Conducted a comprehensive audit of the existing monolith to identify service boundaries',
    'Designed and documented the target microservices architecture with clear API contracts',
    'Established a phased migration plan with automated rollback procedures for each phase',
  ],
  obstacles: [
    'The legacy system had over 200 undocumented inter-module dependencies that had to be mapped manually',
  ],
  outcome: 'Successfully migrated 100% of payment processing services with zero customer-facing downtime, reducing deployment time from 4 hours to 15 minutes',
  roleClarity: 'I was the technical lead responsible for all architecture decisions and cross-team coordination. I reported directly to the VP of Engineering.',
};

const seedUpdatedEntity: BehavioralQuestion = {
  id: 'bq-integration-001',
  sessionId: seedDraft.sessionId,
  objective: seedDraft.objective,
  actions: seedDraft.actions,
  obstacles: seedDraft.obstacles,
  outcome: seedDraft.outcome,
  roleClarity: seedDraft.roleClarity,
  status: 'VERIFY',
  createdAt: '2026-02-28T10:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

describe('Full Path Integration: transition-to-verify-when-minimum-slots-filled', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockUpdateStatus.mockResolvedValue(seedUpdatedEntity);
  });

  describe('Reachability: Full path from trigger to VERIFY state', () => {
    it('should validate → submit → update status → return VERIFY', async () => {
      // Step 1: Frontend validation (ui-a4y1)
      const validation = validateMinimumSlots({
        objective: seedDraft.objective,
        actions: seedDraft.actions,
        obstacles: seedDraft.obstacles,
        outcome: seedDraft.outcome,
        roleClarity: seedDraft.roleClarity,
      });
      expect(validation.isValid).toBe(true);
      expect(Object.keys(validation.errors)).toHaveLength(0);

      // Steps 2-5: Handler → Service → Verifier → DAO
      const result: EvaluateResult = await BehavioralQuestionEvaluateHandler.handle(seedDraft);

      // Terminal Condition: Status is VERIFY
      expect(result.eligible).toBe(true);
      expect(result.status).toBe('VERIFY');
      expect(result.questionId).toBe('bq-integration-001');
    });

    it('should call DAO.updateStatus exactly once with VERIFY', async () => {
      const validation = validateMinimumSlots({
        objective: seedDraft.objective,
        actions: seedDraft.actions,
        obstacles: seedDraft.obstacles,
        outcome: seedDraft.outcome,
        roleClarity: seedDraft.roleClarity,
      });
      expect(validation.isValid).toBe(true);

      await BehavioralQuestionEvaluateHandler.handle(seedDraft);

      expect(mockUpdateStatus).toHaveBeenCalledTimes(1);
      expect(mockUpdateStatus).toHaveBeenCalledWith(seedDraft.sessionId, 'VERIFY');
    });
  });

  describe('TypeInvariant: Response matches EvaluateResult schema', () => {
    it('should return a properly typed EvaluateResult', async () => {
      const result = await BehavioralQuestionEvaluateHandler.handle(seedDraft);

      expect(typeof result.eligible).toBe('boolean');
      expect(typeof result.questionId).toBe('string');
      expect(result.status).toMatch(/^(DRAFT|VERIFY)$/);
      expect(typeof result.updatedAt).toBe('string');
    });
  });

  describe('ErrorConsistency: Invalid input is rejected without state change', () => {
    it('should fail frontend validation when slots are insufficient', () => {
      const invalidDraft = {
        objective: seedDraft.objective,
        actions: ['Only two actions', 'Not enough'],
        obstacles: seedDraft.obstacles,
        outcome: seedDraft.outcome,
        roleClarity: seedDraft.roleClarity,
      };

      const validation = validateMinimumSlots(invalidDraft);
      expect(validation.isValid).toBe(false);
      expect(validation.errors.actions).toBeDefined();
    });

    it('should fail at backend service level with MINIMUM_SLOTS_NOT_MET', async () => {
      const invalidDraft = {
        ...seedDraft,
        actions: ['Only one action'],
      };

      try {
        await BehavioralQuestionEvaluateHandler.handle(invalidDraft);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BehavioralQuestionError);
        expect((e as BehavioralQuestionError).code).toBe('MINIMUM_SLOTS_NOT_MET');
      }

      // DAO should NOT have been called
      expect(mockUpdateStatus).not.toHaveBeenCalled();
    });

    it('should propagate PERSISTENCE_FAILED when DAO rejects', async () => {
      mockUpdateStatus.mockRejectedValue(new Error('Connection timeout'));

      try {
        await BehavioralQuestionEvaluateHandler.handle(seedDraft);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BehavioralQuestionError);
        expect((e as BehavioralQuestionError).code).toBe('PERSISTENCE_FAILED');
        expect((e as BehavioralQuestionError).retryable).toBe(true);
      }
    });
  });
});
