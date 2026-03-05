'use client';

/**
 * GenerateDraftButton - Frontend component where user triggers
 * generation of a structured draft from confirmed claims.
 *
 * Resource: ui-w8p2 (component)
 * Path: 325-generate-draft-from-confirmed-claims
 *
 * On click:
 *   1. Run verifier (validate claimSetId).
 *   2. If valid → call generateDraft() API contract.
 *   3. On success → render draft preview.
 *   4. On error → display error message.
 */

import { useState } from 'react';
import { validateDraftRequestPayload } from '@/verifiers/draftRequestVerifier';
import { generateDraft } from '@/api_contracts/generateDraft';
import type { GenerateDraftResponse } from '@/api_contracts/generateDraft';
import { Button } from '@/components/ui/button';

export interface GenerateDraftButtonProps {
  claimSetId: string;
  onSuccess?: (response: GenerateDraftResponse) => void;
}

export default function GenerateDraftButton({
  claimSetId,
  onSuccess,
}: GenerateDraftButtonProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [draftResponse, setDraftResponse] = useState<GenerateDraftResponse | null>(null);

  const handleGenerateDraft = async () => {
    setError(null);

    // Step 1: Run verifier
    const validation = validateDraftRequestPayload({ claimSetId });

    if (!validation.success) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 2: Call API
    setIsLoading(true);
    try {
      const result = await generateDraft(validation.data);
      setDraftResponse(result);
      onSuccess?.(result);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
    } finally {
      setIsLoading(false);
    }
  };

  // Render draft preview on success
  if (draftResponse) {
    return (
      <div className="flex flex-col gap-4" data-testid="draft-preview">
        <h3 className="font-serif text-lg font-bold">Generated Draft</h3>
        {draftResponse.draft.sections.map((section) => (
          <div key={section.sectionName} className="border rounded-md p-3">
            <h4 className="font-medium capitalize mb-2">{section.sectionName}</h4>
            <ul className="list-disc list-inside space-y-1">
              {section.claims.map((claim) => (
                <li key={claim.id} className="text-sm">
                  {claim.content}
                </li>
              ))}
            </ul>
          </div>
        ))}
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
