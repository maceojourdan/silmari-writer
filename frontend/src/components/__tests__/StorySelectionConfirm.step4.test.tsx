/**
 * Tests for StorySelectionConfirm - Step 4: Display validation feedback
 *
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Render with [] → click Confirm → message "Please select exactly one story before confirming."
 * - TypeInvariant: Error message type is string
 * - ErrorConsistency: Missing error definition → fallback message rendered, logger.error called
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

import { StorySelectionConfirm } from '../StorySelectionConfirm';
import { validateSingleStorySelection } from '@/verifiers/singleStorySelectionVerifier';
import { frontendLogger } from '@/logging/index';

const mockValidate = vi.mocked(validateSingleStorySelection);
const mockLoggerError = vi.mocked(frontendLogger.error);

describe('StorySelectionConfirm - Step 4: Display validation feedback', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Reset the StorySelectionErrors mock to default
    vi.doMock('@/server/error_definitions/StorySelectionErrors', () => ({
      StorySelectionErrors: {
        StorySelectionRequired: {
          code: 'StorySelectionRequired',
          message: 'Please select exactly one story before confirming.',
        },
      },
    }));
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should display validation message when confirm is clicked with empty selection', async () => {
      mockValidate.mockReturnValue({
        valid: false,
        reason: 'StorySelectionRequired',
      });

      render(<StorySelectionConfirm selectedStoryIds={[]} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        const message = screen.getByTestId('validation-message');
        expect(message).toBeInTheDocument();
        expect(message.textContent).toBe(
          'Please select exactly one story before confirming.',
        );
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should render error message as a string', async () => {
      mockValidate.mockReturnValue({
        valid: false,
        reason: 'StorySelectionRequired',
      });

      render(<StorySelectionConfirm selectedStoryIds={[]} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        const message = screen.getByTestId('validation-message');
        expect(typeof message.textContent).toBe('string');
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display fallback message and log error when error definition is missing', async () => {
      // Return a reason that doesn't exist in StorySelectionErrors
      mockValidate.mockReturnValue({
        valid: false,
        reason: 'NonExistentErrorCode',
      });

      render(<StorySelectionConfirm selectedStoryIds={[]} />);

      await userEvent.click(screen.getByTestId('confirm-selection-button'));

      await waitFor(() => {
        const message = screen.getByTestId('validation-message');
        expect(message).toBeInTheDocument();
        // Should display fallback message
        expect(message.textContent).toBe(
          'Please select a story before confirming.',
        );
      });

      // Should have logged the missing definition
      expect(mockLoggerError).toHaveBeenCalledWith(
        'NonExistentErrorCode',
        expect.anything(),
        expect.objectContaining({
          component: 'StorySelectionConfirm',
          action: 'displayValidationFeedback',
        }),
      );
    });
  });
});
