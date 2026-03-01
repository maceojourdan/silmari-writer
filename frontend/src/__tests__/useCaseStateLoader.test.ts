/**
 * useCaseStateLoader.test.ts - Unit test for the case state data loader hook.
 *
 * Step 5 of Path 322: Enforce drafting access restriction in UI.
 *
 * TLA+ properties:
 * - Reachability: Mock API returning blocked status → hook returns blocked state.
 * - TypeInvariant: Returned object matches CaseStateResponse type.
 * - ErrorConsistency: API failure → hook returns error state + logs via frontend logger.
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { renderHook, waitFor, act } from '@testing-library/react';
import { CaseStateResponseSchema } from '@/server/data_structures/Case';

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

vi.mock('@/api_contracts/getCaseState', () => ({
  getCaseState: vi.fn(),
}));

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { useCaseStateLoader } from '@/data_loaders/useCaseStateLoader';
import { getCaseState } from '@/api_contracts/getCaseState';
import { frontendLogger } from '@/logging/index';

const mockGetCaseState = vi.mocked(getCaseState);
const mockLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const blockedResponse = {
  caseId: 'case-001',
  drafting_status: 'blocked_due_to_unverified_claims' as const,
  blocked: true,
  message: 'Drafting is blocked due to disputed claims that are not verified.',
};

const allowedResponse = {
  caseId: 'case-001',
  drafting_status: 'drafting_allowed' as const,
  blocked: false,
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('useCaseStateLoader — Step 5', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // Reachability
  // =========================================================================

  describe('Reachability', () => {
    it('should return blocked state when API returns blocked status', async () => {
      mockGetCaseState.mockResolvedValue(blockedResponse);

      const { result } = renderHook(() => useCaseStateLoader('case-001'));

      // Trigger load
      await act(async () => {
        await result.current.loadCaseState();
      });

      expect(result.current.caseState).toEqual(blockedResponse);
      expect(result.current.caseState?.blocked).toBe(true);
    });

    it('should return allowed state when API returns drafting_allowed', async () => {
      mockGetCaseState.mockResolvedValue(allowedResponse);

      const { result } = renderHook(() => useCaseStateLoader('case-001'));

      await act(async () => {
        await result.current.loadCaseState();
      });

      expect(result.current.caseState?.blocked).toBe(false);
    });
  });

  // =========================================================================
  // TypeInvariant
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should return object matching CaseStateResponse type', async () => {
      mockGetCaseState.mockResolvedValue(blockedResponse);

      const { result } = renderHook(() => useCaseStateLoader('case-001'));

      await act(async () => {
        await result.current.loadCaseState();
      });

      const parsed = CaseStateResponseSchema.safeParse(result.current.caseState);
      expect(parsed.success).toBe(true);
    });
  });

  // =========================================================================
  // ErrorConsistency
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should return error state when API fails', async () => {
      mockGetCaseState.mockRejectedValue(new Error('Network error'));

      const { result } = renderHook(() => useCaseStateLoader('case-001'));

      await act(async () => {
        await result.current.loadCaseState();
      });

      expect(result.current.error).toBe('Network error');
      expect(result.current.caseState).toBeNull();
    });

    it('should log error via frontend logger when API fails', async () => {
      mockGetCaseState.mockRejectedValue(new Error('Network error'));

      const { result } = renderHook(() => useCaseStateLoader('case-001'));

      await act(async () => {
        await result.current.loadCaseState();
      });

      expect(mockLogger.error).toHaveBeenCalledWith(
        'Failed to load case state',
        expect.any(Error),
        expect.objectContaining({
          module: 'useCaseStateLoader',
          action: 'loadCaseState',
        }),
      );
    });

    it('should track loading state during fetch', async () => {
      let resolvePromise: (value: typeof blockedResponse) => void;
      const promise = new Promise<typeof blockedResponse>((resolve) => {
        resolvePromise = resolve;
      });
      mockGetCaseState.mockReturnValue(promise);

      const { result } = renderHook(() => useCaseStateLoader('case-001'));

      expect(result.current.isLoading).toBe(false);

      const loadPromise = act(async () => {
        const loadResult = result.current.loadCaseState();
        // Let microtask queue process
        await Promise.resolve();
        return loadResult;
      });

      // Resolve the promise
      resolvePromise!(blockedResponse);
      await loadPromise;

      expect(result.current.isLoading).toBe(false);
    });
  });
});
