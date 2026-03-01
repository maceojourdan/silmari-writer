/**
 * RecallModule Step 1 Tests - Activate Recall Module
 *
 * Resource: ui-v3n6 (module)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * TLA+ properties tested:
 * - Reachability: Render with initialState="RECALL" → context.state === "RECALL"
 * - TypeInvariant: Returned context satisfies AppStateContext with state union type
 * - ErrorConsistency: Render with initialState={undefined} → fallback state "SAFE_DEFAULT" + logger called
 */

import { renderHook } from '@testing-library/react';
import { useRecallModule } from '../RecallModule';
import { frontendLogger } from '@/logging/index';

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

const mockLogger = vi.mocked(frontendLogger);

describe('RecallModule - Step 1: Activate Recall Module', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should resolve state to RECALL when initialState is RECALL', () => {
      const { result } = renderHook(() => useRecallModule({ initialState: 'RECALL' }));

      expect(result.current.state).toBe('RECALL');
    });

    it('should resolve state to ORIENT when initialState is ORIENT', () => {
      const { result } = renderHook(() => useRecallModule({ initialState: 'ORIENT' }));

      expect(result.current.state).toBe('ORIENT');
    });

    it('should resolve state to INIT when initialState is INIT', () => {
      const { result } = renderHook(() => useRecallModule({ initialState: 'INIT' }));

      expect(result.current.state).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return context with state property matching AppState union', () => {
      const { result } = renderHook(() => useRecallModule({ initialState: 'RECALL' }));

      const validStates = ['INIT', 'ORIENT', 'RECALL', 'SAFE_DEFAULT'];
      expect(validStates).toContain(result.current.state);
    });

    it('should have state property that is a string', () => {
      const { result } = renderHook(() => useRecallModule({ initialState: 'RECALL' }));

      expect(typeof result.current.state).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should fallback to SAFE_DEFAULT when initialState is undefined', () => {
      const { result } = renderHook(() =>
        useRecallModule({ initialState: undefined as unknown as string }),
      );

      expect(result.current.state).toBe('SAFE_DEFAULT');
    });

    it('should log UI_STATE_NOT_FOUND when initialState is undefined', () => {
      renderHook(() =>
        useRecallModule({ initialState: undefined as unknown as string }),
      );

      expect(mockLogger.error).toHaveBeenCalledWith(
        'UI_STATE_NOT_FOUND',
        expect.any(Error),
        expect.objectContaining({ module: 'RecallModule' }),
      );
    });

    it('should fallback to SAFE_DEFAULT when initialState is empty string', () => {
      const { result } = renderHook(() => useRecallModule({ initialState: '' }));

      expect(result.current.state).toBe('SAFE_DEFAULT');
    });

    it('should fallback to SAFE_DEFAULT when initialState is null', () => {
      const { result } = renderHook(() =>
        useRecallModule({ initialState: null as unknown as string }),
      );

      expect(result.current.state).toBe('SAFE_DEFAULT');
    });
  });
});
