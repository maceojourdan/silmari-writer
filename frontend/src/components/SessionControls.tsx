'use client';

/**
 * SessionControls - Captures user action to modify a session
 * (e.g., add voice input or re-finalize).
 *
 * Resource: ui-w8p2 (component)
 * Path: 309-reject-modifications-to-finalized-session
 *
 * On click:
 *   1. Run SessionModificationVerifier to validate payload
 *   2. If valid → call modifySession API contract
 *   3. If invalid → set local error state with validation message
 *   4. If API returns error → display error message
 */

import { useState } from 'react';
import {
  validateModifySessionPayload,
  ModifySessionPayloadSchema,
} from '@/verifiers/SessionModificationVerifier';
import { modifySession } from '@/api_contracts/modifySession';

export interface SessionControlsProps {
  sessionId: string;
  onModified?: (data: unknown) => void;
}

export default function SessionControls({
  sessionId,
  onModified,
}: SessionControlsProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleModify = async (action: 'ADD_VOICE' | 'FINALIZE') => {
    setError(null);

    // Step 1: Run frontend verifier
    const payload = { sessionId, action };
    const validation = validateModifySessionPayload(payload);

    if (!validation.success) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 2: Validate via Zod schema (additional check)
    const schemaValidation = ModifySessionPayloadSchema.safeParse(payload);
    if (!schemaValidation.success) {
      setError(
        schemaValidation.error.issues
          .map((i) => `${i.path.join('.')}: ${i.message}`)
          .join(', '),
      );
      return;
    }

    // Step 3: Call API contract
    setIsLoading(true);
    try {
      const result = await modifySession(sessionId, action);

      if (!result.ok) {
        setError(result.error.message);
        return;
      }

      onModified?.(result.data);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'An unexpected error occurred');
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <div className="flex flex-col gap-2">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        onClick={() => handleModify('ADD_VOICE')}
        disabled={isLoading}
        aria-label="Add Voice Input"
      >
        {isLoading ? 'Processing...' : 'Add Voice Input'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
