/**
 * OrientStoryModule - Frontend module managing story selection and confirmation.
 *
 * Displays the active question, job requirements, and available stories.
 * Allows user to select one story and confirm it.
 *
 * Resource: ui-v3n6 (module)
 * Paths: 313-confirm-aligned-story-selection, 314-prevent-confirmation-of-misaligned-story-selection
 */

'use client';

import { useState, useEffect, useCallback } from 'react';
import { loadOrientStoryData } from '@/data_loaders/loadOrientStoryData';
import { StorySelection } from '@/components/StorySelection';
import type { OrientStoryData, Story } from '@/server/data_structures/ConfirmStory';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface OrientStoryModuleProps {
  questionId: string;
  jobId?: string;
  onConfirmed?: (confirmedStory: Story, excludedCount: number) => void;
}

type ModuleState =
  | { phase: 'loading' }
  | { phase: 'loaded'; data: OrientStoryData }
  | { phase: 'error'; message: string }
  | { phase: 'confirmed'; story: Story; excludedCount: number };

// ---------------------------------------------------------------------------
// Module Component
// ---------------------------------------------------------------------------

export function OrientStoryModule({ questionId, jobId, onConfirmed }: OrientStoryModuleProps) {
  const [state, setState] = useState<ModuleState>({ phase: 'loading' });

  const fetchData = useCallback(async () => {
    setState({ phase: 'loading' });
    try {
      const data = await loadOrientStoryData(questionId);
      setState({ phase: 'loaded', data });
    } catch (err) {
      const message = err instanceof Error ? err.message : 'An unexpected error occurred';
      setState({ phase: 'error', message });
    }
  }, [questionId]);

  useEffect(() => {
    fetchData();
  }, [fetchData]);

  // Loading state
  if (state.phase === 'loading') {
    return (
      <div data-testid="orient-story-loading">
        <p>Loading story selection...</p>
      </div>
    );
  }

  // Error state
  if (state.phase === 'error') {
    return (
      <div role="alert" data-testid="orient-story-error">
        <p>{state.message}</p>
        <button onClick={fetchData}>Retry</button>
      </div>
    );
  }

  // Confirmed state
  if (state.phase === 'confirmed') {
    return (
      <div data-testid="orient-story-confirmed">
        <h2>Story Confirmed</h2>
        <div data-testid="confirmed-story">
          <h3>{state.story.title}</h3>
          <p>{state.story.summary}</p>
        </div>
      </div>
    );
  }

  // Loaded state - show selection UI
  const { question, jobRequirements, stories } = state.data;

  const handleConfirmed = (confirmedStory: Story, excludedCount: number) => {
    setState({ phase: 'confirmed', story: confirmedStory, excludedCount });
    onConfirmed?.(confirmedStory, excludedCount);
  };

  return (
    <div data-testid="orient-story-module">
      <section data-testid="question-section">
        <h2>{question.text}</h2>
      </section>

      <section data-testid="requirements-section">
        <h3>Job Requirements</h3>
        <ul>
          {jobRequirements.map((req) => (
            <li key={req.id}>{req.description}</li>
          ))}
        </ul>
      </section>

      <section data-testid="stories-section">
        <StorySelection
          stories={stories}
          questionId={questionId}
          jobId={jobId}
          onConfirmed={handleConfirmed}
        />
      </section>
    </div>
  );
}
