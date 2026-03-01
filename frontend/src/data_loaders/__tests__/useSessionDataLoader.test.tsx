/**
 * Tests for useSessionDataLoader
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 307-process-voice-input-and-progress-session
 *
 * TLA+ properties tested:
 * - Reachability: mock successful API response → expect state updated and component
 *   re-rendered with new state
 * - TypeInvariant: state matches SessionState + StoryRecord types
 * - ErrorConsistency:
 *   - State update throws → logger called and error message rendered
 */

import { renderHook, act, waitFor } from '@testing-library/react';
import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock the API contract
vi.mock('@/api_contracts/submitVoiceResponse', () => ({
  submitVoiceResponse: vi.fn(),
}));

// Mock the frontend logger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { submitVoiceResponse } from '@/api_contracts/submitVoiceResponse';
import { frontendLogger } from '@/logging/index';
import { useSessionDataLoader } from '../useSessionDataLoader';
import type { AnswerSession } from '@/server/data_structures/AnswerSession';

const mockSubmit = vi.mocked(submitVoiceResponse);
const mockLogger = vi.mocked(frontendLogger);

describe('useSessionDataLoader - Step 6: Update UI with progressed session', () => {
  const initSession: AnswerSession = {
    id: '550e8400-e29b-41d4-a716-446655440000',
    userId: 'user-123',
    state: 'INIT',
    createdAt: '2026-02-28T00:00:00Z',
    updatedAt: '2026-02-28T00:00:00Z',
  };

  const successResponse = {
    session: {
      ...initSession,
      state: 'IN_PROGRESS' as const,
      updatedAt: '2026-02-28T00:00:01Z',
    },
    storyRecord: {
      id: '660e8400-e29b-41d4-a716-446655440001',
      sessionId: initSession.id,
      status: 'IN_PROGRESS' as const,
      content: 'I led a cross-functional team.',
      createdAt: '2026-02-28T00:00:00Z',
      updatedAt: '2026-02-28T00:00:01Z',
    },
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return initial session state', () => {
      const { result } = renderHook(() => useSessionDataLoader(initSession));

      expect(result.current.session).toEqual(initSession);
      expect(result.current.storyRecord).toBeNull();
      expect(result.current.isSubmitting).toBe(false);
      expect(result.current.error).toBeNull();
    });

    it('should update session and storyRecord on successful submission', async () => {
      mockSubmit.mockResolvedValue(successResponse);

      const { result } = renderHook(() => useSessionDataLoader(initSession));

      await act(async () => {
        await result.current.submitTranscript('I led a cross-functional team.');
      });

      expect(result.current.session.state).toBe('IN_PROGRESS');
      expect(result.current.storyRecord).not.toBeNull();
      expect(result.current.storyRecord?.content).toBe('I led a cross-functional team.');
    });

    it('should call submitVoiceResponse with correct payload', async () => {
      mockSubmit.mockResolvedValue(successResponse);

      const { result } = renderHook(() => useSessionDataLoader(initSession));

      await act(async () => {
        await result.current.submitTranscript('My response text');
      });

      expect(mockSubmit).toHaveBeenCalledWith({
        sessionId: initSession.id,
        transcript: 'My response text',
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should have session matching AnswerSession type', () => {
      const { result } = renderHook(() => useSessionDataLoader(initSession));

      const session = result.current.session;
      expect(typeof session.id).toBe('string');
      expect(typeof session.userId).toBe('string');
      expect(typeof session.state).toBe('string');
      expect(['INIT', 'IN_PROGRESS']).toContain(session.state);
    });

    it('should have storyRecord matching AnswerStoryRecord type after success', async () => {
      mockSubmit.mockResolvedValue(successResponse);

      const { result } = renderHook(() => useSessionDataLoader(initSession));

      await act(async () => {
        await result.current.submitTranscript('Test transcript');
      });

      const sr = result.current.storyRecord;
      expect(sr).not.toBeNull();
      expect(typeof sr!.id).toBe('string');
      expect(typeof sr!.sessionId).toBe('string');
      expect(['INIT', 'IN_PROGRESS']).toContain(sr!.status);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should set error state when submission fails', async () => {
      mockSubmit.mockRejectedValue(new Error('Network failure'));

      const { result } = renderHook(() => useSessionDataLoader(initSession));

      await act(async () => {
        await result.current.submitTranscript('Test transcript');
      });

      expect(result.current.error).toBe('Network failure');
      expect(result.current.isSubmitting).toBe(false);
    });

    it('should call logger when submission fails', async () => {
      mockSubmit.mockRejectedValue(new Error('Server error'));

      const { result } = renderHook(() => useSessionDataLoader(initSession));

      await act(async () => {
        await result.current.submitTranscript('Test transcript');
      });

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('Failed'),
        expect.any(Error),
        expect.objectContaining({ module: 'useSessionDataLoader' }),
      );
    });

    it('should preserve session state on error', async () => {
      mockSubmit.mockRejectedValue(new Error('Failed'));

      const { result } = renderHook(() => useSessionDataLoader(initSession));

      await act(async () => {
        await result.current.submitTranscript('Test transcript');
      });

      // Session should still be in INIT
      expect(result.current.session.state).toBe('INIT');
      expect(result.current.storyRecord).toBeNull();
    });

    it('should set isSubmitting during API call', async () => {
      let resolvePromise: (value: any) => void;
      mockSubmit.mockReturnValue(
        new Promise((resolve) => {
          resolvePromise = resolve;
        }),
      );

      const { result } = renderHook(() => useSessionDataLoader(initSession));

      act(() => {
        result.current.submitTranscript('Test');
      });

      // Should be submitting
      expect(result.current.isSubmitting).toBe(true);

      // Resolve the promise
      await act(async () => {
        resolvePromise!(successResponse);
      });

      expect(result.current.isSubmitting).toBe(false);
    });
  });
});
