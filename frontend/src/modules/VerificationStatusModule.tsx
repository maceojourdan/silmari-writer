/**
 * VerificationStatusModule - Displays verification status and controls
 * drafting button state based on verification outcome.
 *
 * Resource: ui-v3n6 (module)
 * Path: 323-fail-verification-when-no-contact-method
 */

'use client';

// ---------------------------------------------------------------------------
// Props
// ---------------------------------------------------------------------------

export interface VerificationStatusModuleProps {
  verificationStatus: 'FAILED' | 'PENDING';
  reason?: string;
  draftingAllowed: boolean;
}

// ---------------------------------------------------------------------------
// Failure reason messages
// ---------------------------------------------------------------------------

const FAILURE_MESSAGES: Record<string, string> = {
  MISSING_CONTACT_METHOD:
    'Verification failed: no contact method available. Please add a phone number or enable SMS to proceed.',
};

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function VerificationStatusModule({
  verificationStatus,
  reason,
  draftingAllowed,
}: VerificationStatusModuleProps) {
  const isFailed = verificationStatus === 'FAILED';
  const failureMessage = reason
    ? FAILURE_MESSAGES[reason] ?? `Verification failed: ${reason}`
    : undefined;

  return (
    <div data-testid="verification-status-module">
      {/* Status Badge */}
      <div data-testid="verification-status">{verificationStatus}</div>

      {/* Failure Message */}
      {isFailed && failureMessage && (
        <div
          data-testid="verification-failure-message"
          role="alert"
          aria-live="polite"
        >
          {failureMessage}
        </div>
      )}

      {/* Drafting Button */}
      <button
        type="button"
        disabled={!draftingAllowed}
        aria-disabled={!draftingAllowed}
      >
        Start Drafting
      </button>
    </div>
  );
}
