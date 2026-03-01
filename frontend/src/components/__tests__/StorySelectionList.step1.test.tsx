/**
 * Tests for StorySelectionList - Step 1: Capture story selection event
 *
 * Path: 315-switch-selected-story-before-confirmation
 *
 * TLA+ properties tested:
 * - Reachability: Click story 'b' with 'a' selected → handler receives { newId: 'b', currentId: 'a' }
 * - TypeInvariant: Both identifiers are string matching StoryId type
 * - ErrorConsistency: Click with invalid id → no state update, frontend_logging.error called with INVALID_STORY_ID
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

describe('StorySelectionList - Step 1: Capture story selection event', () => {
  beforeEach(() => {
    mockLogError.mockReset();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should capture newId and currentId when clicking a different story', async () => {
      const onSelectionChange = vi.fn();

      render(
        <StorySelectionList
          stories={testStories}
          onSelectionChange={onSelectionChange}
        />,
      );

      // Click on story 'b' (currently 'a' is selected)
      await userEvent.click(screen.getByText('Story B'));

      await waitFor(() => {
        expect(onSelectionChange).toHaveBeenCalledWith({
          newId: 'b',
          currentId: 'a',
        });
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should provide string identifiers matching StoryId type', async () => {
      const onSelectionChange = vi.fn();

      render(
        <StorySelectionList
          stories={testStories}
          onSelectionChange={onSelectionChange}
        />,
      );

      await userEvent.click(screen.getByText('Story B'));

      await waitFor(() => {
        expect(onSelectionChange).toHaveBeenCalledTimes(1);
      });

      const args = onSelectionChange.mock.calls[0][0];
      expect(typeof args.newId).toBe('string');
      expect(typeof args.currentId).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log INVALID_STORY_ID and not update state when clicked story id is invalid', async () => {
      const onSelectionChange = vi.fn();

      render(
        <StorySelectionList
          stories={testStories}
          onSelectionChange={onSelectionChange}
          _testInvalidClickId={true}
        />,
      );

      // Click the test-invalid button that simulates an invalid story click
      await userEvent.click(screen.getByTestId('invalid-story-trigger'));

      await waitFor(() => {
        expect(mockLogError).toHaveBeenCalledWith(
          'INVALID_STORY_ID',
          expect.anything(),
          expect.objectContaining({
            component: 'StorySelectionList',
          }),
        );
      });

      expect(onSelectionChange).not.toHaveBeenCalled();
    });
  });
});
