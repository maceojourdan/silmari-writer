/**
 * ClaimStatusPanel - Renders claim verification and drafting status.
 *
 * Resource: ui-w8p2 (component)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * Displays:
 * - Claim status (e.g., "Unverified")
 * - Drafting status (e.g., "On Hold")
 * - Timeout badge when verification has timed out
 * - Error state and fallback "Status Unavailable"
 */

'use client';

import React from 'react';
import type { ClaimStatusResponse } from '@/server/data_structures/DraftingWorkflow';

export interface ClaimStatusPanelProps {
  data: ClaimStatusResponse | null;
  loading: boolean;
  error: Error | null;
}

export function ClaimStatusPanel({ data, loading, error }: ClaimStatusPanelProps) {
  if (loading) {
    return (
      <div data-testid="claim-status-loading" role="status" aria-label="Loading claim status">
        <p>Loading claim status...</p>
      </div>
    );
  }

  if (error) {
    return (
      <div data-testid="claim-status-error" role="alert">
        <p>Error loading claim status</p>
        <p>{error.message}</p>
      </div>
    );
  }

  if (!data || !data.claimStatus || !data.draftingStatus) {
    return (
      <div data-testid="claim-status-unavailable" role="status">
        <p>Status Unavailable</p>
      </div>
    );
  }

  const isTimedOut = data.timedOut === true;

  return (
    <div data-testid="claim-status-panel">
      <div data-testid="claim-status">
        <span>Claim Status: </span>
        <strong>{data.claimStatus === 'UNVERIFIED' ? 'Unverified' : data.claimStatus}</strong>
      </div>

      <div data-testid="drafting-status">
        <span>Drafting Status: </span>
        <strong>{data.draftingStatus}</strong>
      </div>

      {isTimedOut && (
        <div data-testid="timeout-badge" role="status" aria-label="Verification timed out">
          <span>Verification Timed Out</span>
        </div>
      )}
    </div>
  );
}
