/**
 * behavioralQuestionModule Tests
 *
 * Resource: ui-v3n6 (module)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: mock successful API → dispatch submit → status shows "VERIFY"
 * - TypeInvariant: module state type includes status: 'DRAFT' | 'VERIFY'
 * - ErrorConsistency: state update exception → frontend_logging.error called and refresh triggered
 */

import { renderHook, act } from '@testing-library/react';
import { useBehavioralQuestionModule } from '../module';
import { evaluateBehavioralQuestion } from '@/api_contracts/evaluateBehavioralQuestion';
import { frontendLogger } from '@/logging/index';
import type { BehavioralQuestionDraft } from '@/server/data_structures/BehavioralQuestion';

vi.mock('@/api_contracts/evaluateBehavioralQuestion', () => ({
  evaluateBehavioralQuestion: vi.fn(),
}));

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

const mockEvaluate = vi.mocked(evaluateBehavioralQuestion);
const mockLogger = vi.mocked(frontendLogger);

const validDraft: BehavioralQuestionDraft = {
  objective: 'Led a cross-functional team to migrate legacy systems',
  actions: [
    'Identified key stakeholders and gathered requirements',
    'Created a phased migration plan with rollback procedures',
    'Coordinated daily standups across three teams',
  ],
  obstacles: ['Legacy system had undocumented dependencies'],
  outcome: 'Successfully migrated 100% of services with zero downtime',
  roleClarity: 'I was the technical lead responsible for architecture decisions',
};

describe('behavioralQuestionModule', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: mock successful API → dispatch submit → status shows VERIFY', () => {
    it('should initialize with DRAFT status', () => {
      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      expect(result.current.status).toBe('DRAFT');
    });

    it('should transition to VERIFY on successful submit', async () => {
      mockEvaluate.mockResolvedValueOnce({
        eligible: true,
        questionId: 'bq-001',
        status: 'VERIFY',
        updatedAt: '2026-02-28T12:00:00.000Z',
      });

      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      // Set draft values
      act(() => {
        result.current.updateDraft(validDraft);
      });

      // Submit
      await act(async () => {
        await result.current.submit();
      });

      expect(result.current.status).toBe('VERIFY');
    });

    it('should call evaluateBehavioralQuestion with correct payload', async () => {
      mockEvaluate.mockResolvedValueOnce({
        eligible: true,
        questionId: 'bq-001',
        status: 'VERIFY',
        updatedAt: '2026-02-28T12:00:00.000Z',
      });

      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      act(() => {
        result.current.updateDraft(validDraft);
      });

      await act(async () => {
        await result.current.submit();
      });

      expect(mockEvaluate).toHaveBeenCalledWith({
        sessionId: 'session-001',
        ...validDraft,
      });
    });
  });

  describe('TypeInvariant: module state type includes status: DRAFT | VERIFY', () => {
    it('should have status property that is either DRAFT or VERIFY', () => {
      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      expect(result.current.status).toMatch(/^(DRAFT|VERIFY)$/);
    });

    it('should have draft, errors, isSubmitting, and status properties', () => {
      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      expect(result.current).toHaveProperty('draft');
      expect(result.current).toHaveProperty('errors');
      expect(result.current).toHaveProperty('isSubmitting');
      expect(result.current).toHaveProperty('status');
      expect(result.current).toHaveProperty('submit');
      expect(result.current).toHaveProperty('updateDraft');
    });
  });

  describe('ErrorConsistency: errors logged and state preserved on failure', () => {
    it('should not submit when validation fails', async () => {
      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      // Don't set valid draft - keep defaults
      await act(async () => {
        await result.current.submit();
      });

      expect(mockEvaluate).not.toHaveBeenCalled();
      expect(result.current.status).toBe('DRAFT');
    });

    it('should set errors when validation fails', async () => {
      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      // Set partial draft (missing slots)
      act(() => {
        result.current.updateDraft({
          ...validDraft,
          actions: ['Only one'],
        });
      });

      await act(async () => {
        await result.current.submit();
      });

      expect(Object.keys(result.current.errors).length).toBeGreaterThan(0);
      expect(mockEvaluate).not.toHaveBeenCalled();
    });

    it('should log error and keep DRAFT status when API call fails', async () => {
      mockEvaluate.mockRejectedValueOnce(new Error('Network error'));

      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      act(() => {
        result.current.updateDraft(validDraft);
      });

      await act(async () => {
        await result.current.submit();
      });

      expect(result.current.status).toBe('DRAFT');
      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should set apiError when API call fails', async () => {
      mockEvaluate.mockRejectedValueOnce(new Error('Server down'));

      const { result } = renderHook(() =>
        useBehavioralQuestionModule('session-001'),
      );

      act(() => {
        result.current.updateDraft(validDraft);
      });

      await act(async () => {
        await result.current.submit();
      });

      expect(result.current.apiError).toBeDefined();
      expect(result.current.apiError).toContain('Server down');
    });
  });
});
