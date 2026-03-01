/**
 * Tests for StorySelectionConfirm - Step 3: Block confirmation flow
 *
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Render with [] → click Confirm → confirmStorySelectionLoader.confirm NOT called
 * - TypeInvariant: Validation result object passed through component unchanged
 * - ErrorConsistency: Race condition → in-flight request cancelled via loader.cancel()
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock verifier
vi.mock('@/verifiers/singleStorySelectionVerifier', () => ({
  validateSingleStorySelection: vi.fn(),
}));

// Mock data loader
vi.mock('@/data_loaders/confirmStorySelectionLoader', () => ({
  confirmStorySelectionLoader: {
    confirm: vi.fn(),
    cancel: vi.fn(),
  },
}));

// Mock frontend_logging
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock error definitions
vi.mock('@/server/error_definitions/StorySelectionErrors', () => ({
  StorySelectionErrors: {
    StorySelectionRequired: {
      code: 'StorySelectionRequired',
      message: 'Please select exactly one story before confirming.',
    },
  },
}));

import { StorySelectionConfirm } from '../StorySelectionConfirm';
import { validateSingleStorySelection } from '@/verifiers/singleStorySelectionVerifier';
import { confirmStorySelectionLoader } from '@/data_loaders/confirmStorySelectionLoader';

const mockValidate = vi.mocked(validateSingleStorySelection);
const mockConfirm = vi.mocked(confirmStorySelectionLoader.confirm);
const mockCancel = vi.mocked(confirmStorySelectionLoader.cancel);

describe('StorySelectionConfirm - Step 3: Block confirmation flow', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should NOT call confirmStorySelectionLoader.confirm when validation fails', async () => {
      mockValidate.mockReturnValue({
        valid: false,
        reason: 'StorySelectionRequired',
      });

      render(<StorySelectionConfirm selectedStoryIds={[]} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockValidate).toHaveBeenCalledWith([]);
      });

      // confirm should NOT have been called
      expect(mockConfirm).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass the exact selectedStoryIds array to the verifier unchanged', async () => {
      const ids = ['story-001'];
      mockValidate.mockReturnValue({ valid: true });
      mockConfirm.mockResolvedValue({
        confirmedStoryId: 'story-001',
        status: 'CONFIRMED',
      });

      render(
        <StorySelectionConfirm
          selectedStoryIds={ids}
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockValidate).toHaveBeenCalledWith(ids);
      });

      // When valid, confirm should be called with the first ID
      await waitFor(() => {
        expect(mockConfirm).toHaveBeenCalledWith('story-001');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency (race condition)
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should call loader.cancel() if there is an in-flight request when validation fails', async () => {
      // First call: validation passes (starts in-flight request)
      // We simulate this by rendering with valid data first
      mockValidate.mockReturnValueOnce({ valid: true });

      // Make confirm return a pending promise (simulating in-flight)
      let resolveConfirm: (value: any) => void;
      mockConfirm.mockReturnValueOnce(
        new Promise((resolve) => {
          resolveConfirm = resolve;
        }),
      );

      const { rerender } = render(
        <StorySelectionConfirm selectedStoryIds={['story-001']} />,
      );

      // First click - starts in-flight request
      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockConfirm).toHaveBeenCalledTimes(1);
      });

      // Now rerender with empty selection (simulating race condition)
      mockValidate.mockReturnValue({
        valid: false,
        reason: 'StorySelectionRequired',
      });

      rerender(<StorySelectionConfirm selectedStoryIds={[]} />);

      // Second click with empty selection - should cancel in-flight
      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockCancel).toHaveBeenCalledTimes(1);
      });

      // Resolve the pending promise to clean up
      resolveConfirm!({ confirmedStoryId: 'story-001', status: 'CONFIRMED' });
    });
  });
});
