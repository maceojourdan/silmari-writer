/**
 * Integration test for StorySelectionList - Terminal Condition
 *
 * Path: 315-switch-selected-story-before-confirmation
 *
 * End-to-end proof of reachability from trigger → terminal UI state:
 * - Given two stories, 'a' initially selected
 * - User clicks 'b' before confirmation
 * - Assert: 'a' visually deselected, 'b' visually selected, exactly one story selected
 */

// @ts-nocheck
import { describe, it, expect, vi } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock frontend_logging
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { StorySelectionList } from '../StorySelectionList';
import type { Story } from '../StorySelectionList';

describe('StorySelectionList - Integration: switch-selected-story-before-confirmation', () => {
  it('should switch selection from story a to story b before confirmation', async () => {
    const stories: Story[] = [
      { id: 'a', title: 'Story A', selected: true },
      { id: 'b', title: 'Story B', selected: false },
    ];
    const onSelectionChange = vi.fn();

    render(
      <StorySelectionList
        stories={stories}
        onSelectionChange={onSelectionChange}
      />,
    );

    // -----------------------------------------------------------------------
    // Initial state: 'a' is visually selected
    // -----------------------------------------------------------------------
    const storyA = screen.getByTestId('story-item-a');
    const storyB = screen.getByTestId('story-item-b');

    expect(storyA).toHaveAttribute('data-selected', 'true');
    expect(storyB).toHaveAttribute('data-selected', 'false');

    // -----------------------------------------------------------------------
    // User clicks 'b' before confirmation
    // -----------------------------------------------------------------------
    await userEvent.click(screen.getByText('Story B'));

    // -----------------------------------------------------------------------
    // Terminal condition:
    // - 'a' visually deselected
    // - 'b' visually selected
    // - Exactly one story selected in rendered state
    // -----------------------------------------------------------------------
    await waitFor(() => {
      expect(storyA).toHaveAttribute('data-selected', 'false');
      expect(storyB).toHaveAttribute('data-selected', 'true');
    });

    // Verify exactly one story is visually selected
    const allStoryItems = screen.getAllByRole('option');
    const selectedItems = allStoryItems.filter(
      (item) => item.getAttribute('data-selected') === 'true',
    );
    expect(selectedItems).toHaveLength(1);
    expect(selectedItems[0]).toHaveAttribute('data-selected', 'true');
    expect(selectedItems[0].textContent).toBe('Story B');

    // Verify callback was fired with correct payload
    expect(onSelectionChange).toHaveBeenCalledWith({
      newId: 'b',
      currentId: 'a',
    });
  });

  it('should handle rapid successive clicks correctly', async () => {
    const stories: Story[] = [
      { id: 'a', title: 'Story A', selected: true },
      { id: 'b', title: 'Story B', selected: false },
      { id: 'c', title: 'Story C', selected: false },
    ];
    const onSelectionChange = vi.fn();

    render(
      <StorySelectionList
        stories={stories}
        onSelectionChange={onSelectionChange}
      />,
    );

    // Click 'b' then 'c' in quick succession
    await userEvent.click(screen.getByText('Story B'));
    await userEvent.click(screen.getByText('Story C'));

    await waitFor(() => {
      expect(screen.getByTestId('story-item-a')).toHaveAttribute(
        'data-selected',
        'false',
      );
      expect(screen.getByTestId('story-item-b')).toHaveAttribute(
        'data-selected',
        'false',
      );
      expect(screen.getByTestId('story-item-c')).toHaveAttribute(
        'data-selected',
        'true',
      );
    });

    // Exactly one selected
    const allStoryItems = screen.getAllByRole('option');
    const selectedItems = allStoryItems.filter(
      (item) => item.getAttribute('data-selected') === 'true',
    );
    expect(selectedItems).toHaveLength(1);
  });
});
