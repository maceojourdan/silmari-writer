/**
 * Tests for StorySelectionConfirm - Step 1: Capture confirm action
 *
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Render with selectedStoryIds = [] → click Confirm → handler receives [] as selection state
 * - TypeInvariant: Selection state passed to verifier is string[]
 * - ErrorConsistency: Corrupted state (null) → click Confirm → logger.error called, Confirm disabled
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock verifier
vi.mock('@/verifiers/singleStorySelectionVerifier', () => ({
  validateSingleStorySelection: vi.fn().mockReturnValue({
    valid: false,
    reason: 'StorySelectionRequired',
  }),
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
import { frontendLogger } from '@/logging/index';

const mockValidate = vi.mocked(validateSingleStorySelection);
const mockLoggerError = vi.mocked(frontendLogger.error);

describe('StorySelectionConfirm - Step 1: Capture confirm action', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockValidate.mockReturnValue({
      valid: false,
      reason: 'StorySelectionRequired',
    });
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should pass empty array to verifier when Confirm is clicked with selectedStoryIds = []', async () => {
      render(<StorySelectionConfirm selectedStoryIds={[]} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockValidate).toHaveBeenCalledTimes(1);
        expect(mockValidate).toHaveBeenCalledWith([]);
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass selection state as string[] to verifier', async () => {
      const ids = ['story-001', 'story-002'];
      render(<StorySelectionConfirm selectedStoryIds={ids} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockValidate).toHaveBeenCalledTimes(1);
      });

      const [passedArg] = mockValidate.mock.calls[0];
      expect(Array.isArray(passedArg)).toBe(true);
      passedArg.forEach((id: unknown) => {
        expect(typeof id).toBe('string');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log error and disable Confirm button when selectedStoryIds is corrupted (null)', async () => {
      render(<StorySelectionConfirm selectedStoryIds={null as any} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockLoggerError).toHaveBeenCalledWith(
          'Invalid selection state',
          expect.anything(),
          expect.objectContaining({
            component: 'StorySelectionConfirm',
          }),
        );
      });

      // Confirm button should become disabled
      expect(screen.getByTestId('confirm-selection-button')).toBeDisabled();
    });

    it('should not call verifier when state is corrupted', async () => {
      render(<StorySelectionConfirm selectedStoryIds={null as any} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        expect(mockLoggerError).toHaveBeenCalled();
      });

      expect(mockValidate).not.toHaveBeenCalled();
    });
  });
});
