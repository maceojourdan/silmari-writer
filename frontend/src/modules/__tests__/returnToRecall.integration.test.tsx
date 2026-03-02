/**
 * returnToRecall.integration.test.tsx - Terminal Condition: End-to-end flow
 *
 * Proves end-to-end reachability from trigger → state update → UI re-render.
 *
 * Integration test:
 * - Render full WritingFlowModule starting in 'REVIEW'.
 * - Simulate user clicking "Return to Recall".
 * - Assert:
 *   - Recall screen visible.
 *   - Review screen not visible.
 *   - Recall input interface active (record button present).
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

import { WritingFlowModule } from '../WritingFlowModule';
import { frontendLogger } from '@/logging/index';

describe('Return to Recall — Terminal Condition (Integration)', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    vi.mocked(frontendLogger.error).mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  it('should navigate from REVIEW to RECALL with complete UI transition', async () => {
    // 1. Render full WritingFlowModule starting in 'REVIEW'
    render(<WritingFlowModule initialStep="REVIEW" />);

    // Verify initial state: Review screen visible
    expect(screen.getByTestId('review-screen')).toBeInTheDocument();
    expect(screen.queryByTestId('recall-screen')).not.toBeInTheDocument();

    // 2. Simulate user clicking "Return to Recall"
    const returnButton = screen.getByTestId('return-to-recall');
    expect(returnButton).toHaveTextContent(/return to recall/i);
    await userEvent.click(returnButton);

    // 3. Assert terminal condition
    await waitFor(() => {
      // Recall screen visible
      expect(screen.getByTestId('recall-screen')).toBeInTheDocument();

      // Review screen not visible
      expect(screen.queryByTestId('review-screen')).not.toBeInTheDocument();

      // Recall input interface active (record button present)
      expect(screen.getByTestId('record-button')).toBeInTheDocument();
    });
  });

  it('should complete full flow without errors logged', async () => {
    render(<WritingFlowModule initialStep="REVIEW" />);

    // Navigate
    await userEvent.click(screen.getByTestId('return-to-recall'));

    // Wait for transition
    await waitFor(() => {
      expect(screen.getByTestId('recall-screen')).toBeInTheDocument();
    });

    // No errors should have been logged during normal flow
    expect(vi.mocked(frontendLogger.error)).not.toHaveBeenCalled();
  });

  it('should render record button as enabled and interactive', async () => {
    render(<WritingFlowModule initialStep="REVIEW" />);

    await userEvent.click(screen.getByTestId('return-to-recall'));

    await waitFor(() => {
      const recordButton = screen.getByTestId('record-button');
      expect(recordButton).toBeInTheDocument();
      expect(recordButton).not.toBeDisabled();
      expect(recordButton).toHaveAttribute('aria-label', 'Record');
    });
  });
});
