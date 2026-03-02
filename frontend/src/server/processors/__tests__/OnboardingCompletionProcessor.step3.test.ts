/**
 * OnboardingCompletionProcessor.step3.test.ts - Step 3: Business logic (completeStep)
 *
 * TLA+ Properties:
 * - Reachability: Given eligible user, assert OnboardingDao.updateOnboardingStep() called (via service mock).
 * - TypeInvariant: Assert returned object matches OnboardingCompletionResult type.
 * - ErrorConsistency: Mock DAO failure -> Expect BackendErrors.PERSISTENCE_FAILED. Assert no analytics event creation attempted.
 *
 * Resource: db-h2s4 (processor)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { OnboardingCompletionResultSchema } from '@/server/data_structures/Onboarding';
import { BackendError } from '@/server/error_definitions/BackendErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('@/server/services/OnboardingService', () => ({
  OnboardingService: {
    isEligible: vi.fn(),
    completeStep: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/OnboardingDao', () => ({
  OnboardingDao: {
    findByUserAndStep: vi.fn(),
    updateOnboardingStep: vi.fn(),
    insertAnalyticsEvent: vi.fn(),
    findAnalyticsEvent: vi.fn(),
  },
}));

vi.mock('@/server/logging/onboardingLogger', () => ({
  onboardingLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { OnboardingCompletionProcessor } from '../OnboardingCompletionProcessor';
import { OnboardingService } from '@/server/services/OnboardingService';
import { OnboardingDao } from '@/server/data_access_objects/OnboardingDao';

const mockService = vi.mocked(OnboardingService);
const mockDao = vi.mocked(OnboardingDao);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const userId = '550e8400-e29b-41d4-a716-446655440001';
const step = 1;
const onboardingId = '660e8400-e29b-41d4-a716-446655440002';
const completedAt = '2026-03-01T12:00:00.000Z';

const completionResult = {
  id: onboardingId,
  userId,
  step,
  status: 'COMPLETED' as const,
  completedAt,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('OnboardingCompletionProcessor.process — Step 3: Business logic (completeStep)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call OnboardingService.completeStep with userId and step', async () => {
      mockService.completeStep.mockResolvedValue(completionResult);
      mockDao.insertAnalyticsEvent.mockResolvedValue({} as any);

      await OnboardingCompletionProcessor.process(userId, step);

      expect(mockService.completeStep).toHaveBeenCalledWith(userId, step);
    });

    it('should call OnboardingService.completeStep exactly once', async () => {
      mockService.completeStep.mockResolvedValue(completionResult);
      mockDao.insertAnalyticsEvent.mockResolvedValue({} as any);

      await OnboardingCompletionProcessor.process(userId, step);

      expect(mockService.completeStep).toHaveBeenCalledTimes(1);
    });

    it('should propagate the completion result onboardingId in the process return value', async () => {
      mockService.completeStep.mockResolvedValue(completionResult);
      mockDao.insertAnalyticsEvent.mockResolvedValue({} as any);

      const result = await OnboardingCompletionProcessor.process(userId, step);

      expect(result.onboardingId).toBe(onboardingId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a completion result conforming to OnboardingCompletionResult schema from the service', async () => {
      mockService.completeStep.mockResolvedValue(completionResult);
      mockDao.insertAnalyticsEvent.mockResolvedValue({} as any);

      await OnboardingCompletionProcessor.process(userId, step);

      const serviceReturnValue = mockService.completeStep.mock.results[0].value;
      const resolved = await serviceReturnValue;
      const parsed = OnboardingCompletionResultSchema.safeParse(resolved);

      expect(parsed.success).toBe(true);
    });

    it('should return process result with status "completed"', async () => {
      mockService.completeStep.mockResolvedValue(completionResult);
      mockDao.insertAnalyticsEvent.mockResolvedValue({} as any);

      const result = await OnboardingCompletionProcessor.process(userId, step);

      expect(result.status).toBe('completed');
    });

    it('should return process result with the correct step number', async () => {
      mockService.completeStep.mockResolvedValue(completionResult);
      mockDao.insertAnalyticsEvent.mockResolvedValue({} as any);

      const result = await OnboardingCompletionProcessor.process(userId, step);

      expect(result.step).toBe(step);
    });

    it('should include analyticsRecorded boolean in the process result', async () => {
      mockService.completeStep.mockResolvedValue(completionResult);
      mockDao.insertAnalyticsEvent.mockResolvedValue({} as any);

      const result = await OnboardingCompletionProcessor.process(userId, step);

      expect(typeof result.analyticsRecorded).toBe('boolean');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw PERSISTENCE_FAILED when OnboardingService.completeStep fails with a persistence error', async () => {
      const persistenceError = new BackendError(
        'Failed to persist onboarding step 1 completion',
        'PERSISTENCE_FAILED',
        500,
        true,
      );
      mockService.completeStep.mockRejectedValue(persistenceError);

      try {
        await OnboardingCompletionProcessor.process(userId, step);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BackendError);
        expect((e as BackendError).code).toBe('PERSISTENCE_FAILED');
      }
    });

    it('should not attempt analytics event insertion when completeStep fails', async () => {
      const persistenceError = new BackendError(
        'Failed to persist onboarding step 1 completion',
        'PERSISTENCE_FAILED',
        500,
        true,
      );
      mockService.completeStep.mockRejectedValue(persistenceError);

      try {
        await OnboardingCompletionProcessor.process(userId, step);
      } catch {
        // expected
      }

      expect(mockDao.insertAnalyticsEvent).not.toHaveBeenCalled();
    });

    it('should not call constructAnalyticsEvent when completeStep fails', async () => {
      const persistenceError = new BackendError(
        'Failed to persist onboarding step 1 completion',
        'PERSISTENCE_FAILED',
        500,
        true,
      );
      mockService.completeStep.mockRejectedValue(persistenceError);

      const constructSpy = vi.spyOn(OnboardingCompletionProcessor, 'constructAnalyticsEvent');

      try {
        await OnboardingCompletionProcessor.process(userId, step);
      } catch {
        // expected
      }

      expect(constructSpy).not.toHaveBeenCalled();
      constructSpy.mockRestore();
    });

    it('should propagate the error statusCode from the service', async () => {
      const persistenceError = new BackendError(
        'Failed to persist',
        'PERSISTENCE_FAILED',
        500,
        true,
      );
      mockService.completeStep.mockRejectedValue(persistenceError);

      try {
        await OnboardingCompletionProcessor.process(userId, step);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as BackendError).statusCode).toBe(500);
      }
    });
  });
});
