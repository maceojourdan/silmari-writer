/**
 * WritingFlowModule.rendering.test.tsx - Step 3: Re-render Recall screen
 *
 * TLA+ Properties:
 * - Reachability: Render WritingFlowModule with initial step 'REVIEW' → trigger navigation to 'RECALL' →
 *                 Recall component present (recall-screen); Review component absent (review-screen null)
 * - TypeInvariant: Rendered component corresponds exactly to activeStep union value;
 *                  discriminated conditional rendering
 * - ErrorConsistency: Mock Recall component to throw during render →
 *                     fallback UI displayed ("Unable to load Recall step");
 *                     logger.error called with "Recall render failure"
 *
 * Resource: ui-v3n6 (module)
 * Path: 331-return-to-recall-from-review
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the frontend logger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock fetch
const mockFetch = vi.fn();

import { frontendLogger } from '@/logging/index';

describe('WritingFlowModule — Step 3: Re-render Recall screen', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    vi.mocked(frontendLogger.error).mockReset();

    // Suppress console.error for error boundary tests
    vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    vi.unstubAllGlobals();
    vi.restoreAllMocks();
    vi.resetModules();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render Recall component when navigated from REVIEW to RECALL', async () => {
      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="REVIEW" />);

      // Initially REVIEW is active
      expect(screen.getByTestId('review-screen')).toBeInTheDocument();
      expect(screen.queryByTestId('recall-screen')).not.toBeInTheDocument();

      // Navigate to RECALL
      await userEvent.click(screen.getByTestId('return-to-recall'));

      // Now RECALL should be present
      await waitFor(() => {
        expect(screen.getByTestId('recall-screen')).toBeInTheDocument();
      });
    });

    it('should remove Review component when RECALL is active', async () => {
      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="REVIEW" />);

      // Navigate to RECALL
      await userEvent.click(screen.getByTestId('return-to-recall'));

      // Review should be removed
      await waitFor(() => {
        expect(screen.queryByTestId('review-screen')).not.toBeInTheDocument();
      });
    });

    it('should render RecallScreen with record button present', async () => {
      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="REVIEW" />);

      // Navigate to RECALL
      await userEvent.click(screen.getByTestId('return-to-recall'));

      // Record button should be present within Recall screen
      await waitFor(() => {
        expect(screen.getByTestId('record-button')).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should render exactly one step component at a time - discriminated rendering', async () => {
      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="REVIEW" />);

      // REVIEW active: exactly 1 review-screen, 0 recall-screens
      expect(screen.queryAllByTestId('review-screen')).toHaveLength(1);
      expect(screen.queryAllByTestId('recall-screen')).toHaveLength(0);

      // Navigate to RECALL
      await userEvent.click(screen.getByTestId('return-to-recall'));

      // RECALL active: exactly 0 review-screens, 1 recall-screen
      await waitFor(() => {
        expect(screen.queryAllByTestId('review-screen')).toHaveLength(0);
        expect(screen.queryAllByTestId('recall-screen')).toHaveLength(1);
      });
    });

    it('should render RECALL when initialStep is RECALL', async () => {
      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="RECALL" />);

      expect(screen.getByTestId('recall-screen')).toBeInTheDocument();
      expect(screen.queryByTestId('review-screen')).not.toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display fallback UI when Recall component throws during render', async () => {
      // Mock RecallScreen to throw
      vi.doMock('@/components/RecallScreen', () => ({
        default: () => {
          throw new Error('Recall component failed to render');
        },
      }));

      // Re-import WritingFlowModule to pick up the mock
      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="RECALL" />);

      // Should show fallback error UI
      await waitFor(() => {
        expect(screen.getByText('Unable to load Recall step')).toBeInTheDocument();
      });
    });

    it('should log error when Recall component fails to render', async () => {
      // Mock RecallScreen to throw
      vi.doMock('@/components/RecallScreen', () => ({
        default: () => {
          throw new Error('Recall component failed to render');
        },
      }));

      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="RECALL" />);

      await waitFor(() => {
        expect(vi.mocked(frontendLogger.error)).toHaveBeenCalledWith(
          'Recall render failure',
          expect.any(Error),
          expect.objectContaining({ module: 'WritingFlowModule' }),
        );
      });
    });

    it('should show fallback with role="alert" for accessibility', async () => {
      vi.doMock('@/components/RecallScreen', () => ({
        default: () => {
          throw new Error('Recall component failed to render');
        },
      }));

      const { WritingFlowModule } = await import('../WritingFlowModule');

      render(<WritingFlowModule initialStep="RECALL" />);

      await waitFor(() => {
        const fallback = screen.getByTestId('recall-fallback-error');
        expect(fallback).toBeInTheDocument();
        expect(fallback).toHaveAttribute('role', 'alert');
      });
    });
  });
});
