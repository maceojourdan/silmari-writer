'use client';

/**
 * ApproveButton - Captures user Approve action for draft sessions.
 *
 * Resource: ui-w8p2 (component)
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * On click:
 *   1. Run sessionStateVerifier.assertDraft()
 *   2. If valid → build typed payload → call API contract
 *   3. If invalid → set local error state with validation message
 */

import { useState } from 'react';
import { assertDraft } from '@/verifiers/sessionStateVerifier';
import { approveSession, ApproveSessionRequestSchema } from '@/api_contracts/approveSession';
import type { ApproveSessionResponse } from '@/api_contracts/approveSession';
import { StateTransitionError } from '@/server/error_definitions/StateTransitionErrors';

export interface ApproveButtonProps {
  sessionId: string;
  sessionState: string;
  onApproved?: (updatedSession: ApproveSessionResponse) => void;
}

export default function ApproveButton({
  sessionId,
  sessionState,
  onApproved,
}: ApproveButtonProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isApproved, setIsApproved] = useState(false);

  const handleApprove = async () => {
    setError(null);

    // Step 1: Run verifier — block if not DRAFT
    try {
      assertDraft({ id: sessionId, state: sessionState });
    } catch (err) {
      if (err instanceof StateTransitionError) {
        setError(err.message);
      } else {
        setError('An unexpected validation error occurred');
      }
      return;
    }

    // Step 2: Build typed payload and validate via schema
    const payload = { sessionId, action: 'APPROVE' as const };
    const validation = ApproveSessionRequestSchema.safeParse(payload);

    if (!validation.success) {
      setError(
        validation.error.issues.map((i) => `${i.path.join('.')}: ${i.message}`).join(', '),
      );
      return;
    }

    // Step 3: Call API contract
    setIsLoading(true);
    try {
      const result = await approveSession(sessionId);
      setIsApproved(true);
      onApproved?.(result);
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
        <span>Session approved successfully.</span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        onClick={handleApprove}
        disabled={isLoading}
        aria-label="Approve Session"
      >
        {isLoading ? 'Approving...' : 'Approve Session'}
      </button>

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
