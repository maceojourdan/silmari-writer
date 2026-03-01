/**
 * Tests for StorySelectionList - Step 4: Render updated selection in UI
 *
 * Path: 315-switch-selected-story-before-confirmation
 *
 * TLA+ properties tested:
 * - Reachability: Render with 'a' selected → click 'b' → 'a' NOT data-selected, 'b' HAS data-selected
 * - TypeInvariant: Rendered attributes reflect boolean selected state
 * - ErrorConsistency: Render error → frontend_logging.error with RENDER_FAILURE, previous DOM unchanged
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
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
import { frontendLogger } from '@/logging/index';

const mockLogError = vi.mocked(frontendLogger.error);

const testStories: Story[] = [
  { id: 'a', title: 'Story A', selected: true },
  { id: 'b', title: 'Story B', selected: false },
];

describe('StorySelectionList - Step 4: Render updated selection in UI', () => {
  beforeEach(() => {
    mockLogError.mockReset();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should visually deselect old story and select new story after click', async () => {
      render(
        <StorySelectionList
          stories={testStories}
          onSelectionChange={vi.fn()}
        />,
      );

      // Initial state: 'a' selected, 'b' not selected
      expect(screen.getByTestId('story-item-a')).toHaveAttribute(
        'data-selected',
        'true',
      );
      expect(screen.getByTestId('story-item-b')).toHaveAttribute(
        'data-selected',
        'false',
      );

      // Click on story 'b'
      await userEvent.click(screen.getByText('Story B'));

      // After click: 'a' NOT selected, 'b' IS selected
      await waitFor(() => {
        expect(screen.getByTestId('story-item-a')).toHaveAttribute(
          'data-selected',
          'false',
        );
        expect(screen.getByTestId('story-item-b')).toHaveAttribute(
          'data-selected',
          'true',
        );
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should render data-selected attributes as boolean string values', () => {
      render(
        <StorySelectionList
          stories={testStories}
          onSelectionChange={vi.fn()}
        />,
      );

      const storyA = screen.getByTestId('story-item-a');
      const storyB = screen.getByTestId('story-item-b');

      // data-selected should be 'true' or 'false' (string representation of boolean)
      expect(['true', 'false']).toContain(
        storyA.getAttribute('data-selected'),
      );
      expect(['true', 'false']).toContain(
        storyB.getAttribute('data-selected'),
      );
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log RENDER_FAILURE and keep previous DOM when render error occurs', async () => {
      // Suppress console.error from React for the expected error
      const consoleSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

      render(
        <StorySelectionList
          stories={testStories}
          onSelectionChange={vi.fn()}
          _testForceRenderError={true}
        />,
      );

      // The component should have logged a render failure
      // because _testForceRenderError throws when rendering the selected story
      await waitFor(() => {
        expect(mockLogError).toHaveBeenCalledWith(
          'RENDER_FAILURE',
          expect.anything(),
          expect.objectContaining({
            component: 'StorySelectionList',
            action: 'renderStoryList',
          }),
        );
      });

      // The fallback render should still show story items from lastStableRender
      expect(screen.getByTestId('story-item-a')).toBeInTheDocument();
      expect(screen.getByTestId('story-item-b')).toBeInTheDocument();

      consoleSpy.mockRestore();
    });
  });
});
