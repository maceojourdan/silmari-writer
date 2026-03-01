/**
 * RecallSlotPrompt - Renders missing required slot prompts and captures
 * user input for re-submission.
 *
 * On submit, builds a structured payload and calls the submit-slots
 * endpoint. On 400 with SLOT_SUBMISSION_INVALID, re-renders the same
 * prompts without navigation.
 *
 * Resource: ui-w8p2 (component)
 * Path: 320-re-prompt-unfilled-required-slots
 */

'use client';

import React, { useState, useCallback } from 'react';
import type { SlotPrompt, SubmitSlotsResponse } from '@/api_contracts/submitSlots';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Props
// ---------------------------------------------------------------------------

export interface RecallSlotPromptProps {
  sessionId: string;
  questionType: string;
  prompts: SlotPrompt[];
  attemptCount: number;
  guidanceHint: boolean;
  onUpdate?: (response: SubmitSlotsResponse) => void;
}

// ---------------------------------------------------------------------------
// Component State
// ---------------------------------------------------------------------------

export interface RecallPromptState {
  slotValues: Record<string, string>;
  missingSlots: SlotPrompt[];
  attemptCount: number;
  guidanceHint: boolean;
  error: string | null;
  submitting: boolean;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export function RecallSlotPrompt({
  sessionId,
  questionType,
  prompts,
  attemptCount,
  guidanceHint,
  onUpdate,
}: RecallSlotPromptProps) {
  const [state, setState] = useState<RecallPromptState>(() => {
    const initialValues: Record<string, string> = {};
    for (const prompt of prompts) {
      initialValues[prompt.name] = '';
    }
    return {
      slotValues: initialValues,
      missingSlots: prompts,
      attemptCount,
      guidanceHint,
      error: null,
      submitting: false,
    };
  });

  const handleInputChange = useCallback((slotName: string, value: string) => {
    setState((prev) => ({
      ...prev,
      slotValues: {
        ...prev.slotValues,
        [slotName]: value,
      },
    }));
  }, []);

  const handleSubmit = useCallback(
    async (e: React.FormEvent) => {
      e.preventDefault();

      setState((prev) => ({ ...prev, submitting: true, error: null }));

      try {
        const payload = {
          sessionId,
          questionType,
          slotValues: state.slotValues,
          attemptCount: state.attemptCount,
        };

        const response = await fetch('/api/session/submit-slots', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify(payload),
        });

        if (!response.ok) {
          const errorBody = await response.json().catch(() => ({}));
          const errorMessage =
            errorBody.message || `Submission failed with status ${response.status}`;

          // On 400, re-render same prompts (don't change route/state)
          setState((prev) => ({
            ...prev,
            submitting: false,
            error: errorMessage,
          }));
          return;
        }

        const data: SubmitSlotsResponse = await response.json();

        // Update state with new prompt data
        try {
          const newValues: Record<string, string> = {};
          for (const prompt of data.prompts) {
            newValues[prompt.name] = '';
          }

          setState({
            slotValues: newValues,
            missingSlots: data.prompts,
            attemptCount: data.attemptCount,
            guidanceHint: data.guidanceHint,
            error: null,
            submitting: false,
          });
        } catch (stateError) {
          // Log UI state update failure and preserve last known valid state
          frontendLogger.error(
            'Failed to update RecallSlotPrompt state',
            stateError,
            { component: 'RecallSlotPrompt', action: 'setState' },
          );

          setState((prev) => ({
            ...prev,
            submitting: false,
            error: 'Failed to update display. Please try again.',
          }));
          return;
        }

        // Notify parent if callback provided
        if (onUpdate) {
          onUpdate(data);
        }
      } catch (networkError) {
        frontendLogger.error(
          'Network error submitting slots',
          networkError,
          { component: 'RecallSlotPrompt', action: 'submit' },
        );

        setState((prev) => ({
          ...prev,
          submitting: false,
          error: 'Network error. Please check your connection and try again.',
        }));
      }
    },
    [sessionId, questionType, state.slotValues, state.attemptCount, onUpdate],
  );

  return (
    <form onSubmit={handleSubmit} data-testid="recall-slot-prompt-form">
      <div>
        {state.missingSlots.map((prompt) => (
          <div key={prompt.name}>
            <label htmlFor={`slot-${prompt.name}`}>
              {prompt.promptLabel}
            </label>
            <input
              id={`slot-${prompt.name}`}
              type="text"
              role="textbox"
              value={state.slotValues[prompt.name] || ''}
              onChange={(e) => handleInputChange(prompt.name, e.target.value)}
              disabled={state.submitting}
            />
          </div>
        ))}
      </div>

      {state.guidanceHint && (
        <div data-testid="guidance-hint" role="status">
          <p>
            It looks like you&apos;re having trouble filling in some required information.
            Try to be more specific about each area. You can provide short answers —
            every detail helps!
          </p>
        </div>
      )}

      {state.error && (
        <div role="alert" data-testid="error-message">
          <p>{state.error}</p>
        </div>
      )}

      <button
        type="submit"
        disabled={state.submitting}
      >
        {state.submitting ? 'Submitting...' : 'Submit'}
      </button>
    </form>
  );
}
