'use client';

/**
 * DraftGeneratorButton - Frontend component where user triggers
 * generation of a draft from confirmed claims for a story record.
 *
 * Resource: ui-w8p2 (component)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 *
 * On click:
 *   1. Run draftPreconditionsVerifier (validate storyRecordId).
 *   2. If valid → call generateStoryDraft() API contract.
 *   3. On success → call onSuccess callback with response.
 *   4. On error → set local error state and render message (unless onError provided).
 */

import { useState } from 'react';
import { validateDraftPreconditions } from '@/verifiers/draftPreconditionsVerifier';
import { generateStoryDraft } from '@/api_contracts/generateDraft';
import type { GenerateStoryDraftResponse } from '@/server/data_structures/Claim';

export interface DraftGeneratorButtonProps {
  storyRecordId: string;
  onSuccess?: (response: GenerateStoryDraftResponse) => void;
  onError?: (error: Error) => void;
}

export default function DraftGeneratorButton({
  storyRecordId,
  onSuccess,
  onError,
}: DraftGeneratorButtonProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleGenerateDraft = async () => {
    setError(null);

    // Step 1: Run verifier
    const validation = validateDraftPreconditions({ storyRecordId });

    if (!validation.valid) {
      setError(validation.message);
      return;
    }

    // Step 2: Call API
    setIsLoading(true);
    try {
      const result = await generateStoryDraft({ storyRecordId });
      onSuccess?.(result);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      const errorObj = err instanceof Error ? err : new Error(message);
      if (onError) {
        // Parent handles error display
        onError(errorObj);
      } else {
        // Self-managed error display
        setError(message);
      }
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <div className="flex flex-col gap-2">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        onClick={handleGenerateDraft}
        disabled={isLoading}
        aria-label="Generate Draft"
      >
        {isLoading ? 'Generating...' : 'Generate Draft'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
