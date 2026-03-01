/**
 * StorySelectionConfirm - UI component that handles confirm action
 * and validates single story selection before proceeding.
 *
 * Resource: ui-w8p2 (component)
 * Path: 316-prevent-confirmation-without-single-story-selection
 *
 * Captures the Confirm click, validates via singleStorySelectionVerifier,
 * blocks confirmation flow on failure, and displays validation feedback
 * from StorySelectionErrors.
 */

'use client';

import { useState, useRef, useCallback } from 'react';
import { validateSingleStorySelection } from '@/verifiers/singleStorySelectionVerifier';
import type { ValidationResult } from '@/verifiers/singleStorySelectionVerifier';
import { confirmStorySelectionLoader } from '@/data_loaders/confirmStorySelectionLoader';
import { StorySelectionErrors } from '@/server/error_definitions/StorySelectionErrors';
import type { StorySelectionErrorKey } from '@/server/error_definitions/StorySelectionErrors';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface StorySelectionConfirmProps {
  selectedStoryIds: string[] | null;
  onConfirmed?: (storyId: string) => void;
}

// ---------------------------------------------------------------------------
// Fallback message when error definition is missing
// ---------------------------------------------------------------------------

const FALLBACK_VALIDATION_MESSAGE = 'Please select a story before confirming.';

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export function StorySelectionConfirm({
  selectedStoryIds,
  onConfirmed,
}: StorySelectionConfirmProps) {
  const [isDisabled, setIsDisabled] = useState(false);
  const [validationMessage, setValidationMessage] = useState<string | null>(null);
  const inFlightRef = useRef(false);

  const handleConfirmClick = useCallback(async () => {
    // Step 1: Capture confirm action
    // If state is corrupted (not an array), log error and disable
    if (!Array.isArray(selectedStoryIds)) {
      frontendLogger.error(
        'Invalid selection state',
        new Error('selectedStoryIds is not an array'),
        {
          component: 'StorySelectionConfirm',
          action: 'handleConfirmClick',
        },
      );
      setIsDisabled(true);
      return;
    }

    // Step 2: Validate single selection requirement
    const validation: ValidationResult = validateSingleStorySelection(selectedStoryIds);

    // Step 3: Block confirmation flow on validation failure
    if (!validation.valid) {
      // Cancel any in-flight request (race condition protection)
      if (inFlightRef.current) {
        confirmStorySelectionLoader.cancel();
        inFlightRef.current = false;
      }

      // Step 4: Display validation feedback
      const reason = validation.reason as StorySelectionErrorKey | undefined;
      if (reason && StorySelectionErrors[reason]) {
        setValidationMessage(StorySelectionErrors[reason].message);
      } else {
        // Fallback message when error definition is missing
        setValidationMessage(FALLBACK_VALIDATION_MESSAGE);
        frontendLogger.error(
          reason ?? 'Unknown validation reason',
          new Error('Missing error definition'),
          {
            component: 'StorySelectionConfirm',
            action: 'displayValidationFeedback',
          },
        );
      }

      // Do NOT call confirm
      return;
    }

    // Validation passed - proceed with confirmation
    setValidationMessage(null);
    inFlightRef.current = true;

    try {
      await confirmStorySelectionLoader.confirm(selectedStoryIds[0]);
      onConfirmed?.(selectedStoryIds[0]);
    } catch {
      // Error handled by loader
    } finally {
      inFlightRef.current = false;
    }
  }, [selectedStoryIds, onConfirmed]);

  return (
    <div data-testid="story-selection-confirm">
      {validationMessage && (
        <p role="alert" data-testid="validation-message">
          {validationMessage}
        </p>
      )}

      <button
        onClick={handleConfirmClick}
        disabled={isDisabled}
        data-testid="confirm-selection-button"
      >
        Confirm Selection
      </button>
    </div>
  );
}
