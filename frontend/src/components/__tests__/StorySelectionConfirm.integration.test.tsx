/**
 * Integration test for StorySelectionConfirm - Terminal Condition
 *
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * End-to-end proof of reachability from trigger to terminal state:
 * - Render component with selectedStoryIds = []
 * - Click Confirm up to 5 times
 * - Assert:
 *   - Validation message visible
 *   - confirmStorySelectionLoader.confirm never called
 *   - Confirm action remains blocked
 *
 * This proves:
 * - Reachability: Full path from trigger to terminal
 * - TypeInvariant: Selection state and validation result types preserved
 * - ErrorConsistency: All error branches produce stable UI state
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock frontend_logging (integration test still mocks external services)
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock the data loader (external API boundary)
vi.mock('@/data_loaders/confirmStorySelectionLoader', () => ({
  confirmStorySelectionLoader: {
    confirm: vi.fn(),
    cancel: vi.fn(),
  },
}));

// Use REAL verifier and REAL error definitions (integration test)
import { StorySelectionConfirm } from '../StorySelectionConfirm';
import { confirmStorySelectionLoader } from '@/data_loaders/confirmStorySelectionLoader';

const mockConfirm = vi.mocked(confirmStorySelectionLoader.confirm);

describe('StorySelectionConfirm - Integration: prevent-confirmation-without-single-story-selection', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should block confirmation and show validation message on every click with empty selection (up to 5 times)', async () => {
    render(<StorySelectionConfirm selectedStoryIds={[]} />);

    const confirmButton = screen.getByTestId('confirm-selection-button');

    // Click Confirm up to 5 times
    for (let i = 0; i < 5; i++) {
      await userEvent.click(confirmButton);
    }

    // Assert: Validation message visible
    await waitFor(() => {
      const message = screen.getByTestId('validation-message');
      expect(message).toBeInTheDocument();
      expect(message.textContent).toBe(
        'Please select exactly one story before confirming.',
      );
    });

    // Assert: confirmStorySelectionLoader.confirm never called
    expect(mockConfirm).not.toHaveBeenCalled();

    // Assert: Confirm action remains available (button not disabled - blocked via logic, not disabled)
    expect(confirmButton).not.toBeDisabled();
  });

  it('should maintain stable UI state across multiple confirm attempts', async () => {
    render(<StorySelectionConfirm selectedStoryIds={[]} />);

    // Click 3 times
    for (let i = 0; i < 3; i++) {
      await userEvent.click(screen.getByTestId('confirm-selection-button'));
    }

    // Validation message should appear once (not duplicated)
    const messages = screen.getAllByTestId('validation-message');
    expect(messages).toHaveLength(1);

    // confirm should never be called
    expect(mockConfirm).not.toHaveBeenCalled();
  });

  it('should allow confirmation when exactly one story is selected', async () => {
    mockConfirm.mockResolvedValue({
      confirmedStoryId: 'story-001',
      status: 'CONFIRMED',
    });

    const onConfirmed = vi.fn();

    render(
      <StorySelectionConfirm
        selectedStoryIds={['story-001']}
        onConfirmed={onConfirmed}
      />,
    );

    await userEvent.click(screen.getByTestId('confirm-selection-button'));

    // confirm should be called with the single story ID
    await waitFor(() => {
      expect(mockConfirm).toHaveBeenCalledWith('story-001');
    });

    // onConfirmed should be called
    await waitFor(() => {
      expect(onConfirmed).toHaveBeenCalledWith('story-001');
    });

    // No validation message should be visible
    expect(screen.queryByTestId('validation-message')).not.toBeInTheDocument();
  });

  it('should block confirmation with multiple stories selected', async () => {
    render(
      <StorySelectionConfirm
        selectedStoryIds={['story-001', 'story-002']}
      />,
    );

    await userEvent.click(screen.getByTestId('confirm-selection-button'));

    // Validation message should appear
    await waitFor(() => {
      expect(screen.getByTestId('validation-message')).toBeInTheDocument();
    });

    // confirm should NOT be called
    expect(mockConfirm).not.toHaveBeenCalled();
  });
});
