/**
 * AnalyticsEventPersistence.test.ts - Step 5: Analytics Event Persistence
 *
 * TLA+ Properties:
 * - Reachability: Processor calls OnboardingDao.insertAnalyticsEvent, row inserted (mock returns success)
 * - TypeInvariant: Insert data matches AnalyticsEventInsertSchema via safeParse
 * - ErrorConsistency: DB failure -> onboardingLogger.error called, processor returns analyticsRecorded: false
 *
 * Tests through the OnboardingCompletionProcessor to verify end-to-end analytics
 * persistence behavior. Mocks the DAO and logger at module boundaries.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AnalyticsEventInsertSchema } from '@/server/data_structures/AnalyticsEvent';
import type { AnalyticsEvent } from '@/server/data_structures/AnalyticsEvent';

// ---------------------------------------------------------------------------
// Mock OnboardingDao (database boundary)
// ---------------------------------------------------------------------------

vi.mock('../OnboardingDao', () => ({
  OnboardingDao: {
    findByUserAndStep: vi.fn(),
    updateOnboardingStep: vi.fn(),
    createOnboarding: vi.fn(),
    insertAnalyticsEvent: vi.fn(),
    findAnalyticsEvent: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock onboardingLogger (logging boundary)
// ---------------------------------------------------------------------------

vi.mock('../../logging/onboardingLogger', () => ({
  onboardingLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock getKpiForStep (returns a known KPI identifier for step 1)
// ---------------------------------------------------------------------------

vi.mock('@/shared/constants/LeadingKpis', () => ({
  getKpiForStep: vi.fn((step: number) => {
    const mapping: Record<number, string> = {
      1: 'leading_kpi.onboarding_step_1',
      2: 'leading_kpi.onboarding_step_2',
      3: 'leading_kpi.onboarding_step_3',
    };
    return mapping[step];
  }),
}));

import { OnboardingDao } from '../OnboardingDao';
import { onboardingLogger } from '../../logging/onboardingLogger';
import { OnboardingCompletionProcessor } from '@/server/processors/OnboardingCompletionProcessor';

const mockDao = vi.mocked(OnboardingDao);
const mockLogger = vi.mocked(onboardingLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const userId = 'user-persistence-001';
const step = 1;
const metadata = { source: 'welcome-flow' };
const completedAt = '2026-03-01T12:00:00.000Z';

const mockOnboardingRecord = {
  id: '550e8400-e29b-41d4-a716-446655440010',
  userId,
  step,
  status: 'COMPLETED' as const,
  completedAt,
  createdAt: '2026-03-01T11:00:00.000Z',
  updatedAt: completedAt,
};

const mockAnalyticsEventResult: AnalyticsEvent = {
  id: '660e8400-e29b-41d4-a716-446655440020',
  kpiId: 'leading_kpi.onboarding_step_1',
  userId,
  timestamp: completedAt,
  metadata: { step: 1, source: 'welcome-flow' },
  createdAt: '2026-03-01T12:00:01.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('OnboardingDao.insertAnalyticsEvent via Processor - Step 5: Analytics Event Persistence', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default: OnboardingService.completeStep succeeds
    // (findByUserAndStep returns null => eligible, updateOnboardingStep returns completed record)
    mockDao.findByUserAndStep.mockResolvedValue(null);
    mockDao.updateOnboardingStep.mockResolvedValue(mockOnboardingRecord);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call OnboardingDao.insertAnalyticsEvent and return analyticsRecorded: true on success', async () => {
      mockDao.insertAnalyticsEvent.mockResolvedValue(mockAnalyticsEventResult);

      const result = await OnboardingCompletionProcessor.process(userId, step, metadata);

      expect(mockDao.insertAnalyticsEvent).toHaveBeenCalledTimes(1);
      expect(result.analyticsRecorded).toBe(true);
      expect(result.status).toBe('completed');
      expect(result.onboardingId).toBe(mockOnboardingRecord.id);
      expect(result.step).toBe(step);
    });

    it('should pass correct arguments to insertAnalyticsEvent', async () => {
      mockDao.insertAnalyticsEvent.mockResolvedValue(mockAnalyticsEventResult);

      await OnboardingCompletionProcessor.process(userId, step, metadata);

      const insertArg = mockDao.insertAnalyticsEvent.mock.calls[0][0];
      expect(insertArg.kpiId).toBe('leading_kpi.onboarding_step_1');
      expect(insertArg.userId).toBe(userId);
      expect(insertArg.timestamp).toBeDefined();
      expect(insertArg.metadata).toEqual(expect.objectContaining({ step: 1 }));
    });

    it('should log success info after analytics event is recorded', async () => {
      mockDao.insertAnalyticsEvent.mockResolvedValue(mockAnalyticsEventResult);

      await OnboardingCompletionProcessor.process(userId, step, metadata);

      expect(mockLogger.info).toHaveBeenCalledWith(
        'Analytics event recorded successfully',
        expect.objectContaining({
          userId,
          step,
          kpiId: 'leading_kpi.onboarding_step_1',
        }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass insert data that conforms to AnalyticsEventInsertSchema', async () => {
      mockDao.insertAnalyticsEvent.mockResolvedValue(mockAnalyticsEventResult);

      await OnboardingCompletionProcessor.process(userId, step, metadata);

      const insertArg = mockDao.insertAnalyticsEvent.mock.calls[0][0];
      const parsed = AnalyticsEventInsertSchema.safeParse(insertArg);

      expect(parsed.success).toBe(true);
    });

    it('should include merged metadata with step field in insert data', async () => {
      mockDao.insertAnalyticsEvent.mockResolvedValue(mockAnalyticsEventResult);

      const customMetadata = { source: 'onboarding-modal', region: 'us-east' };
      await OnboardingCompletionProcessor.process(userId, step, customMetadata);

      const insertArg = mockDao.insertAnalyticsEvent.mock.calls[0][0];
      const parsed = AnalyticsEventInsertSchema.safeParse(insertArg);

      expect(parsed.success).toBe(true);
      expect(insertArg.metadata).toEqual(
        expect.objectContaining({ step: 1, source: 'onboarding-modal', region: 'us-east' }),
      );
    });

    it('should produce valid insert data even when no metadata is provided', async () => {
      mockDao.insertAnalyticsEvent.mockResolvedValue(mockAnalyticsEventResult);

      await OnboardingCompletionProcessor.process(userId, step);

      const insertArg = mockDao.insertAnalyticsEvent.mock.calls[0][0];
      const parsed = AnalyticsEventInsertSchema.safeParse(insertArg);

      expect(parsed.success).toBe(true);
      expect(insertArg.metadata).toEqual({ step: 1 });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should call onboardingLogger.error when analytics persistence fails', async () => {
      const dbError = new Error('Connection refused');
      mockDao.insertAnalyticsEvent.mockRejectedValue(dbError);

      await OnboardingCompletionProcessor.process(userId, step, metadata);

      expect(mockLogger.error).toHaveBeenCalledWith(
        'Failed to persist analytics event',
        dbError,
        expect.objectContaining({
          userId,
          step,
          kpiId: 'leading_kpi.onboarding_step_1',
        }),
      );
    });

    it('should return analyticsRecorded: false when analytics persistence fails', async () => {
      mockDao.insertAnalyticsEvent.mockRejectedValue(new Error('Timeout'));

      const result = await OnboardingCompletionProcessor.process(userId, step, metadata);

      expect(result.analyticsRecorded).toBe(false);
    });

    it('should still return successful onboarding completion when analytics persistence fails', async () => {
      mockDao.insertAnalyticsEvent.mockRejectedValue(new Error('DB write failed'));

      const result = await OnboardingCompletionProcessor.process(userId, step, metadata);

      expect(result.status).toBe('completed');
      expect(result.onboardingId).toBe(mockOnboardingRecord.id);
      expect(result.step).toBe(step);
    });

    it('should not throw when analytics persistence fails (non-fatal)', async () => {
      mockDao.insertAnalyticsEvent.mockRejectedValue(new Error('Network error'));

      await expect(
        OnboardingCompletionProcessor.process(userId, step, metadata),
      ).resolves.toBeDefined();
    });

    it('should not call logger.info on analytics persistence failure', async () => {
      mockDao.insertAnalyticsEvent.mockRejectedValue(new Error('DB unavailable'));

      await OnboardingCompletionProcessor.process(userId, step, metadata);

      expect(mockLogger.info).not.toHaveBeenCalled();
    });
  });
});
