'use client';

/**
 * ApproveDraftButton - Frontend component where user approves a draft
 * and sees confirmation or error feedback.
 *
 * Resource: ui-w8p2 (component)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * On click:
 *   1. Run verifier.
 *   2. If valid → call approveStory().
 *   3. If invalid → set local error state.
 */

import { useState } from 'react';
import { validateApproveDraftPayload } from '@/verifiers/ApproveDraftVerifier';
import { approveStory } from '@/api_contracts/approveStory';

export interface ApproveDraftButtonProps {
  draftId: string;
  resumeId: string;
  jobId: string;
  questionId: string;
  voiceSessionId: string;
  onSuccess?: (storyRecordId: string) => void;
}

export default function ApproveDraftButton({
  draftId,
  resumeId,
  jobId,
  questionId,
  voiceSessionId,
  onSuccess,
}: ApproveDraftButtonProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isApproved, setIsApproved] = useState(false);

  const handleApprove = async () => {
    setError(null);

    // Step 1: Run verifier
    const validation = validateApproveDraftPayload({
      draftId,
      resumeId,
      jobId,
      questionId,
      voiceSessionId,
    });

    if (!validation.success) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 2: Call API
    setIsLoading(true);
    try {
      const result = await approveStory(validation.data);
      setIsApproved(true);
      onSuccess?.(result.storyRecordId);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
    } finally {
      setIsLoading(false);
    }
  };

  if (isApproved) {
    return (
      <div className="flex items-center gap-2 text-green-600" data-testid="approve-success">
        <span>Story approved and saved successfully.</span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        onClick={handleApprove}
        disabled={isLoading}
        aria-label="Approve Draft"
      >
        {isLoading ? 'Approving...' : 'Approve Draft'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
