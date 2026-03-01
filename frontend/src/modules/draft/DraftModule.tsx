'use client';

/**
 * DraftModule - Encapsulates the draft generation UI and state management.
 *
 * Renders the DraftGeneratorButton and handles success/error states:
 *   - On success → shows draft content.
 *   - On error code NO_CONFIRMED_CLAIMS → shows specific error notification.
 *   - On other errors → shows generic error notification.
 *   - Ensures no draft state is set when error occurs.
 *
 * Resource: ui-v3n6 (module)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 */

import { useState } from 'react';
import DraftGeneratorButton from '@/components/DraftGeneratorButton';
import type { GenerateStoryDraftResponse } from '@/server/data_structures/Claim';

export interface DraftModuleProps {
  storyRecordId: string;
}

export function DraftModule({ storyRecordId }: DraftModuleProps) {
  const [draftResponse, setDraftResponse] = useState<GenerateStoryDraftResponse | null>(null);
  const [uiError, setUiError] = useState<{ code?: string; message: string } | null>(null);

  const handleSuccess = (response: GenerateStoryDraftResponse) => {
    setUiError(null);
    setDraftResponse(response);
  };

  const handleError = (error: Error) => {
    setDraftResponse(null);

    const code = (error as any).code;
    if (code === 'NO_CONFIRMED_CLAIMS') {
      setUiError({
        code: 'NO_CONFIRMED_CLAIMS',
        message: error.message || 'No confirmed claims are available.',
      });
    } else {
      setUiError({
        message: error.message || 'An unexpected error occurred',
      });
    }
  };

  return (
    <div data-testid="draft-module" className="flex flex-col gap-4">
      <h2 className="text-xl font-semibold">Draft Generation</h2>

      <DraftGeneratorButton
        storyRecordId={storyRecordId}
        onSuccess={handleSuccess}
        onError={handleError}
      />

      {uiError && (
        <div
          data-testid="error-notification"
          className="rounded-md border border-red-200 bg-red-50 p-4"
          role="alert"
        >
          <p className="text-sm text-red-800">{uiError.message}</p>
        </div>
      )}

      {draftResponse && (
        <div data-testid="draft-content" className="flex flex-col gap-4">
          <h3 className="text-lg font-semibold">Generated Draft</h3>
          <div className="whitespace-pre-wrap border rounded-md p-4">
            {draftResponse.content}
          </div>
          <p className="text-sm text-gray-500">
            Claims used: {draftResponse.claimsUsed.join(', ')}
          </p>
        </div>
      )}
    </div>
  );
}
