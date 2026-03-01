'use client';

/**
 * ConfirmMetricClaim - Frontend component where user confirms or denies
 * a displayed extracted metric claim.
 *
 * Resource: ui-w8p2 (component)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * On submit:
 *   1. Run verifier (validateDecision).
 *   2. If valid → map Y→confirmed, N→denied → call confirmTruthCheck().
 *   3. On success → display Confirmed/Denied status.
 *   4. On error → display error alert.
 */

import { useState } from 'react';
import { validateDecision } from '@/verifiers/confirmMetricClaimVerifier';
import { confirmTruthCheck } from '@/api_contracts/confirmTruthCheck';
import type { ConfirmTruthCheckRequest } from '@/api_contracts/confirmTruthCheck';
import { frontendLogger } from '@/logging';

export interface ConfirmMetricClaimProps {
  claimId: string;
  source: string;
  onStatusChange?: (status: 'confirmed' | 'denied') => void;
}

export default function ConfirmMetricClaim({
  claimId,
  source,
  onStatusChange,
}: ConfirmMetricClaimProps) {
  const [decision, setDecision] = useState<'Y' | 'N' | null>(null);
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [resultStatus, setResultStatus] = useState<'confirmed' | 'denied' | null>(null);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    setError(null);

    // Step 1: Run verifier
    const validation = validateDecision(decision ?? undefined);

    if (!validation.isValid) {
      setError(validation.error || 'Please make a selection before submitting');
      return;
    }

    // Step 2: Map Y → confirmed, N → denied
    const status = decision === 'Y' ? 'confirmed' : 'denied';

    const payload: ConfirmTruthCheckRequest = {
      claim_id: claimId,
      status,
      source,
    };

    // Step 3: Call API contract
    setIsSubmitting(true);
    try {
      const result = await confirmTruthCheck(payload);
      setResultStatus(result.status);
      onStatusChange?.(result.status);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
      frontendLogger.error('Truth check confirmation failed', err, {
        component: 'ConfirmMetricClaim',
        action: 'submit',
      });
    } finally {
      setIsSubmitting(false);
    }
  };

  // Display result after successful submission
  if (resultStatus) {
    return (
      <div
        className={`flex items-center gap-2 p-4 rounded ${
          resultStatus === 'confirmed'
            ? 'bg-green-50 text-green-800'
            : 'bg-red-50 text-red-800'
        }`}
        data-testid="result-status"
      >
        <span className="font-semibold">
          {resultStatus === 'confirmed' ? 'Confirmed' : 'Denied'}
        </span>
      </div>
    );
  }

  return (
    <form onSubmit={handleSubmit} className="flex flex-col gap-4 p-4">
      {/* Source display */}
      <div className="text-sm text-gray-600">
        Source: <span className="font-medium">{source}</span>
      </div>

      {/* Decision buttons */}
      <div className="flex gap-2">
        <button
          type="button"
          onClick={() => setDecision('Y')}
          className={`px-4 py-2 text-sm font-medium rounded-md transition-colors ${
            decision === 'Y'
              ? 'bg-green-600 text-white'
              : 'bg-gray-100 text-gray-700 hover:bg-gray-200'
          }`}
          aria-label="Confirm"
        >
          Confirm (Y)
        </button>
        <button
          type="button"
          onClick={() => setDecision('N')}
          className={`px-4 py-2 text-sm font-medium rounded-md transition-colors ${
            decision === 'N'
              ? 'bg-red-600 text-white'
              : 'bg-gray-100 text-gray-700 hover:bg-gray-200'
          }`}
          aria-label="Deny"
        >
          Deny (N)
        </button>
      </div>

      {/* Validation error */}
      {error && (
        <div className="text-sm text-red-600 p-2 bg-red-50 rounded" role="alert">
          {error}
        </div>
      )}

      {/* Submit button */}
      <button
        type="submit"
        disabled={isSubmitting}
        className="px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        aria-label="Submit"
      >
        {isSubmitting ? 'Submitting...' : 'Submit Decision'}
      </button>
    </form>
  );
}
