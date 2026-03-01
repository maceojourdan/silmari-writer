'use client';

/**
 * DraftSessionView - Module containing the draft session view.
 * Orchestrates component state and approval flow.
 *
 * Resource: ui-v3n6 (module)
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * Displays:
 * - Current session state label
 * - ApproveButton (when in DRAFT state)
 * - Confirmation message after successful approval
 * - Error message on failure
 */

import { useState } from 'react';
import ApproveButton from '@/components/ApproveButton';
import type { ApproveSessionResponse } from '@/api_contracts/approveSession';
import { SessionSchema } from '@/server/data_structures/Session';
import { frontendLogger } from '@/logging/index';

export interface DraftSessionViewProps {
  session: {
    id: string;
    state: string;
    createdAt: string;
    updatedAt: string;
  };
}

export default function DraftSessionView({ session: initialSession }: DraftSessionViewProps) {
  const [session, setSession] = useState(initialSession);
  const [confirmationVisible, setConfirmationVisible] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleApproved = (updatedSession: ApproveSessionResponse) => {
    try {
      // Validate response matches Session schema
      const parsed = SessionSchema.safeParse(updatedSession);

      if (!parsed.success) {
        setError('Received invalid session data. Please refresh the page.');
        frontendLogger.error(
          'Failed to validate updated session response',
          new Error(parsed.error.issues.map((i) => i.message).join(', ')),
          { module: 'DraftSessionView', action: 'handleApproved' },
        );
        return;
      }

      setSession(parsed.data);
      setConfirmationVisible(true);
      setError(null);
    } catch (err) {
      setError('An error occurred while updating the session. Please refresh the page.');
      frontendLogger.error(
        'Failed to update session state in UI',
        err,
        { module: 'DraftSessionView', action: 'handleApproved' },
      );
    }
  };

  return (
    <div className="flex flex-col gap-4 p-4">
      <div className="flex items-center gap-2">
        <span className="text-sm font-medium text-muted-foreground">Status:</span>
        <span
          className="text-sm font-semibold"
          data-testid="session-status"
        >
          {session.state}
        </span>
      </div>

      {session.state === 'DRAFT' && (
        <ApproveButton
          sessionId={session.id}
          sessionState={session.state}
          onApproved={handleApproved}
        />
      )}

      {confirmationVisible && (
        <div
          className="text-sm text-green-600 font-medium"
          data-testid="approval-confirmation"
          role="status"
        >
          Session approved and transitioned to FINALIZE.
        </div>
      )}

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
