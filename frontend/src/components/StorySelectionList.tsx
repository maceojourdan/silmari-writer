/**
 * StorySelectionList - UI component for switching selected story before confirmation.
 *
 * Displays a list of stories and handles selection changes.
 * Validates click events, evaluates selection changes, updates state,
 * and renders the updated selection with error recovery.
 *
 * Resource: ui-w8p2 (component)
 * Path: 315-switch-selected-story-before-confirmation
 */

'use client';

import { useState, useRef, Component } from 'react';
import type { ReactNode, ErrorInfo } from 'react';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type StoryId = string;

export type Story = {
  id: StoryId;
  title: string;
  selected: boolean;
};

export interface SelectionChangePayload {
  newId: StoryId;
  currentId: StoryId | null;
}

export interface StorySelectionListProps {
  stories: Story[];
  onSelectionChange?: (payload: SelectionChangePayload) => void;
  /** @internal Test-only prop to trigger an invalid story click */
  _testInvalidClickId?: boolean;
  /** @internal Test-only prop to force a render error */
  _testForceRenderError?: boolean;
}

// ---------------------------------------------------------------------------
// Pure functions
// ---------------------------------------------------------------------------

export function evaluateSelectionChange(
  newId: StoryId,
  currentId: StoryId | null,
): { shouldUpdate: boolean } {
  return { shouldUpdate: newId !== currentId };
}

export function updateSelectedStory(
  stories: Story[],
  newId: StoryId,
): Story[] | null {
  const storyExists = stories.some((s) => s.id === newId);
  if (!storyExists) {
    frontendLogger.error('STORY_NOT_FOUND', new Error(`Story ${newId} not found`), {
      component: 'StorySelectionList',
      action: 'updateSelectedStory',
    });
    return null;
  }

  return stories.map((s) => ({ ...s, selected: s.id === newId }));
}

// ---------------------------------------------------------------------------
// StoryItemErrorBoundary - catches render failures in individual items
// ---------------------------------------------------------------------------

interface BoundaryProps {
  children: ReactNode;
}

interface BoundaryState {
  hasError: boolean;
}

class StoryItemErrorBoundary extends Component<BoundaryProps, BoundaryState> {
  constructor(props: BoundaryProps) {
    super(props);
    this.state = { hasError: false };
  }

  static getDerivedStateFromError(): BoundaryState {
    return { hasError: true };
  }

  componentDidCatch(error: Error, _errorInfo: ErrorInfo): void {
    frontendLogger.error('RENDER_FAILURE', error, {
      component: 'StorySelectionList',
      action: 'renderStoryItem',
    });
  }

  render() {
    if (this.state.hasError) {
      return null;
    }
    return this.props.children;
  }
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export function StorySelectionList({
  stories: initialStories,
  onSelectionChange,
  _testInvalidClickId,
  _testForceRenderError,
}: StorySelectionListProps) {
  const [stories, setStories] = useState<Story[]>(initialStories);
  const lastStableRender = useRef<Story[]>(initialStories);

  function handleStoryClick(id?: string): void {
    if (!id || !stories.find((s) => s.id === id)) {
      frontendLogger.error('INVALID_STORY_ID', new Error(`Invalid story id: ${id}`), {
        component: 'StorySelectionList',
        action: 'handleStoryClick',
      });
      return;
    }

    const currentSelected = stories.find((s) => s.selected)?.id ?? null;

    // Step 2: Evaluate if selection should change
    const { shouldUpdate } = evaluateSelectionChange(id, currentSelected);
    if (!shouldUpdate) {
      return;
    }

    // Step 3: Update state
    const updatedStories = updateSelectedStory(stories, id);
    if (updatedStories === null) {
      return;
    }

    setStories(updatedStories);
    lastStableRender.current = updatedStories;

    // Notify parent
    onSelectionChange?.({ newId: id, currentId: currentSelected });
  }

  // Step 4: Render
  let renderedItems: ReactNode;
  try {
    renderedItems = stories.map((story) => {
      if (_testForceRenderError && story.selected) {
        throw new Error('Forced render error for testing');
      }

      return (
        <li
          key={story.id}
          data-testid={`story-item-${story.id}`}
          data-selected={story.selected}
          onClick={() => handleStoryClick(story.id)}
          role="option"
          aria-selected={story.selected}
        >
          {story.title}
        </li>
      );
    });
  } catch (renderError) {
    frontendLogger.error('RENDER_FAILURE', renderError, {
      component: 'StorySelectionList',
      action: 'renderStoryList',
    });

    // Fall back to last stable render
    renderedItems = lastStableRender.current.map((story) => (
      <li
        key={story.id}
        data-testid={`story-item-${story.id}`}
        data-selected={story.selected}
        onClick={() => handleStoryClick(story.id)}
        role="option"
        aria-selected={story.selected}
      >
        {story.title}
      </li>
    ));
  }

  return (
    <div data-testid="story-selection-list">
      <ul role="listbox" aria-label="Story selection">
        {renderedItems}
      </ul>
      {_testInvalidClickId && (
        <button
          data-testid="invalid-story-trigger"
          onClick={() => handleStoryClick(undefined)}
        >
          Invalid click
        </button>
      )}
    </div>
  );
}
