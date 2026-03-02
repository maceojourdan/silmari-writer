/**
 * OnboardingCompletionProcessor.step4.test.ts - Step 4: Construct analytics event
 *
 * TLA+ Properties:
 * - Reachability: After successful completion, assert event constructed with
 *   kpiId === LeadingKpis.ONBOARDING_STEP_1, userId, timestamp, metadata.step === 1.
 * - TypeInvariant: Assert matches expected analytics event shape.
 * - ErrorConsistency: Test with a step that has no KPI mapping (e.g., step 99) ->
 *   Expect BackendErrors.KPI_IDENTIFIER_MISSING. Assert onboarding completion already persisted.
 *
 * Resource: db-h2s4 (processor)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { BackendError } from '@/server/error_definitions/BackendErrors';
import { LeadingKpis } from '@/shared/constants/LeadingKpis';
import type { OnboardingCompletionResult } from '@/server/data_structures/Onboarding';

// ---------------------------------------------------------------------------
// Mock dependencies (required for module import even though Step 4 tests
// call constructAnalyticsEvent directly)
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
const onboardingId = '660e8400-e29b-41d4-a716-446655440002';
const completedAt = '2026-03-01T12:00:00.000Z';

const step1CompletionResult: OnboardingCompletionResult = {
  id: onboardingId,
  userId,
  step: 1,
  status: 'COMPLETED',
  completedAt,
};

const step99CompletionResult: OnboardingCompletionResult = {
  id: onboardingId,
  userId,
  step: 99,
  status: 'COMPLETED',
  completedAt,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('OnboardingCompletionProcessor.constructAnalyticsEvent — Step 4: Construct analytics event', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should construct event with kpiId matching LeadingKpis.ONBOARDING_STEP_1 for step 1', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(event.kpiId).toBe(LeadingKpis.ONBOARDING_STEP_1);
    });

    it('should construct event with the correct userId from the completion result', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(event.userId).toBe(userId);
    });

    it('should construct event with timestamp from completedAt', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(event.timestamp).toBe(completedAt);
    });

    it('should construct event with metadata.step matching the completion step', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(event.metadata.step).toBe(1);
    });

    it('should merge additional metadata into the event metadata', () => {
      const extraMetadata = { source: 'web', sessionId: 'sess-abc' };

      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(
        step1CompletionResult,
        extraMetadata,
      );

      expect(event.metadata.source).toBe('web');
      expect(event.metadata.sessionId).toBe('sess-abc');
      expect(event.metadata.step).toBe(1);
    });

    it('should construct event without extra metadata when none is provided', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(Object.keys(event.metadata)).toEqual(['step']);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return an object with kpiId as a string', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(typeof event.kpiId).toBe('string');
    });

    it('should return an object with userId as a string', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(typeof event.userId).toBe('string');
    });

    it('should return an object with timestamp as a string', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(typeof event.timestamp).toBe('string');
    });

    it('should return an object with metadata as a plain object', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(typeof event.metadata).toBe('object');
      expect(event.metadata).not.toBeNull();
      expect(Array.isArray(event.metadata)).toBe(false);
    });

    it('should return event matching the expected analytics event shape', () => {
      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step1CompletionResult);

      expect(event).toEqual({
        kpiId: LeadingKpis.ONBOARDING_STEP_1,
        userId,
        timestamp: completedAt,
        metadata: { step: 1 },
      });
    });

    it('should construct event for step 2 with matching KPI', () => {
      const step2Result: OnboardingCompletionResult = {
        ...step1CompletionResult,
        step: 2,
      };

      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step2Result);

      expect(event.kpiId).toBe(LeadingKpis.ONBOARDING_STEP_2);
      expect(event.metadata.step).toBe(2);
    });

    it('should construct event for step 3 with matching KPI', () => {
      const step3Result: OnboardingCompletionResult = {
        ...step1CompletionResult,
        step: 3,
      };

      const event = OnboardingCompletionProcessor.constructAnalyticsEvent(step3Result);

      expect(event.kpiId).toBe(LeadingKpis.ONBOARDING_STEP_3);
      expect(event.metadata.step).toBe(3);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw KPI_IDENTIFIER_MISSING when step has no KPI mapping', () => {
      try {
        OnboardingCompletionProcessor.constructAnalyticsEvent(step99CompletionResult);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BackendError);
        expect((e as BackendError).code).toBe('KPI_IDENTIFIER_MISSING');
      }
    });

    it('should include the step number in the KPI_IDENTIFIER_MISSING error message', () => {
      try {
        OnboardingCompletionProcessor.constructAnalyticsEvent(step99CompletionResult);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as BackendError).message).toContain('99');
      }
    });

    it('should throw KPI_IDENTIFIER_MISSING for step 0', () => {
      const step0Result: OnboardingCompletionResult = {
        ...step1CompletionResult,
        step: 0,
      };

      try {
        OnboardingCompletionProcessor.constructAnalyticsEvent(step0Result);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BackendError);
        expect((e as BackendError).code).toBe('KPI_IDENTIFIER_MISSING');
      }
    });

    it('should throw KPI_IDENTIFIER_MISSING for negative step', () => {
      const negativeStepResult: OnboardingCompletionResult = {
        ...step1CompletionResult,
        step: -1,
      };

      try {
        OnboardingCompletionProcessor.constructAnalyticsEvent(negativeStepResult);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(BackendError);
        expect((e as BackendError).code).toBe('KPI_IDENTIFIER_MISSING');
      }
    });

    it('should confirm onboarding completion was already persisted before analytics event construction fails', async () => {
      // Simulate the full process flow: completeStep succeeds, then constructAnalyticsEvent fails for step 99
      mockService.completeStep.mockResolvedValue(step99CompletionResult);

      try {
        await OnboardingCompletionProcessor.process(userId, 99);
        expect.fail('Should have thrown');
      } catch (e) {
        // completeStep was called and resolved successfully (onboarding persisted)
        expect(mockService.completeStep).toHaveBeenCalledWith(userId, 99);
        expect(mockService.completeStep).toHaveBeenCalledTimes(1);

        // Analytics event insertion was never attempted because constructAnalyticsEvent threw
        expect(mockDao.insertAnalyticsEvent).not.toHaveBeenCalled();

        // The error is KPI_IDENTIFIER_MISSING
        expect(e).toBeInstanceOf(BackendError);
        expect((e as BackendError).code).toBe('KPI_IDENTIFIER_MISSING');
      }
    });
  });
});
