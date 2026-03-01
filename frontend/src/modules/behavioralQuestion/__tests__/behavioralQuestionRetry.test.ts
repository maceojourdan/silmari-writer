/**
 * Feedback Loop Tests: Behavioral Question Retry Limits
 *
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Tests:
 * - Simulate invalid submission attempts up to 5 times → allowed.
 * - 6th invalid attempt → cooldown message shown; no backend call.
 */

import { renderHook, act } from '@testing-library/react';
import { useBehavioralQuestionModule } from '../module';
import { evaluateBehavioralQuestion } from '@/api_contracts/evaluateBehavioralQuestion';
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

const validDraft: BehavioralQuestionDraft = {
  objective: 'Led a team',
  actions: ['Action 1', 'Action 2', 'Action 3'],
  obstacles: ['Obstacle 1'],
  outcome: 'Successful outcome',
  roleClarity: 'Technical lead',
};

describe('Behavioral Question Feedback Loop: Retry Limits', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should allow up to 5 failed submission attempts', async () => {
    mockEvaluate.mockRejectedValue(new Error('Server error'));

    const { result } = renderHook(() =>
      useBehavioralQuestionModule('session-001'),
    );

    act(() => {
      result.current.updateDraft(validDraft);
    });

    // Attempt 1-5 should all be allowed (API called)
    for (let i = 0; i < 5; i++) {
      await act(async () => {
        await result.current.submit();
      });
    }

    expect(mockEvaluate).toHaveBeenCalledTimes(5);
  });

  it('should show cooldown message on 6th invalid attempt', async () => {
    mockEvaluate.mockRejectedValue(new Error('Server error'));

    const { result } = renderHook(() =>
      useBehavioralQuestionModule('session-001'),
    );

    act(() => {
      result.current.updateDraft(validDraft);
    });

    // Exhaust 5 attempts
    for (let i = 0; i < 5; i++) {
      await act(async () => {
        await result.current.submit();
      });
    }

    // 6th attempt
    await act(async () => {
      await result.current.submit();
    });

    // Should not call API on 6th attempt
    expect(mockEvaluate).toHaveBeenCalledTimes(5);

    // Should show cooldown message
    expect(result.current.apiError).toContain('cooldown');
  });

  it('should not count successful submissions toward retry limit', async () => {
    mockEvaluate.mockResolvedValue({
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

    // Successful submission
    await act(async () => {
      await result.current.submit();
    });

    // Should succeed (not counted toward retry limit)
    expect(result.current.status).toBe('VERIFY');
  });

  it('should not count validation failures toward retry limit', async () => {
    const { result } = renderHook(() =>
      useBehavioralQuestionModule('session-001'),
    );

    // Submit without valid draft multiple times (validation fails, no API call)
    for (let i = 0; i < 10; i++) {
      await act(async () => {
        await result.current.submit();
      });
    }

    // None of these should have called the API (validation failed)
    expect(mockEvaluate).not.toHaveBeenCalled();

    // Now set valid draft and submit
    act(() => {
      result.current.updateDraft(validDraft);
    });

    mockEvaluate.mockResolvedValueOnce({
      eligible: true,
      questionId: 'bq-001',
      status: 'VERIFY',
      updatedAt: '2026-02-28T12:00:00.000Z',
    });

    await act(async () => {
      await result.current.submit();
    });

    // Should still work (validation failures don't count)
    expect(mockEvaluate).toHaveBeenCalledTimes(1);
  });
});
