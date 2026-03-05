'use client';

/**
 * DraftGenerator - Frontend component where user triggers generation
 * of a structured draft from confirmed claims for a given case.
 *
 * Resource: ui-w8p2 (component)
 * Path: 326-generate-draft-with-only-confirmed-claims
 *
 * On click:
 *   1. Call generateCaseDraft({ caseId }) API contract.
 *   2. On success → render draft content.
 *   3. On error → log via frontend logger, display error message.
 */

import { useState } from 'react';
import { generateCaseDraft } from '@/api_contracts/generateDraft';
import type { GenerateCaseDraftResponse } from '@/api_contracts/generateDraft';
import { frontendLogger } from '@/logging/index';
import { Button } from '@/components/ui/button';

export interface DraftGeneratorProps {
  caseId: string;
  onSuccess?: (response: GenerateCaseDraftResponse) => void;
}

export default function DraftGenerator({
  caseId,
  onSuccess,
}: DraftGeneratorProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [draftResponse, setDraftResponse] = useState<GenerateCaseDraftResponse | null>(null);

  const handleGenerateDraft = async () => {
    setError(null);

    // Call API contract
    setIsLoading(true);
    try {
      const result = await generateCaseDraft({ caseId });
      setDraftResponse(result);
      onSuccess?.(result);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      frontendLogger.error(
        'Draft generation failed',
        err instanceof Error ? err : new Error(String(err)),
        { component: 'DraftGenerator', action: 'generateCaseDraft' },
      );
      setError(message);
    } finally {
      setIsLoading(false);
    }
  };

  // Render draft content on success
  if (draftResponse) {
    return (
      <div className="flex flex-col gap-4" data-testid="draft-content">
        <h3 className="font-serif text-lg font-bold">Generated Draft</h3>
        <div className="whitespace-pre-wrap border rounded-md p-4">
          {draftResponse.content}
        </div>
        <p className="text-sm text-muted-foreground">
          Claims used: {draftResponse.claimsUsed.join(', ')}
        </p>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <Button
        onClick={handleGenerateDraft}
        disabled={isLoading}
        aria-label="Generate Draft"
      >
        {isLoading ? 'Generating...' : 'Generate Draft'}
      </Button>

      {error && (
        <div className="text-sm text-destructive" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
