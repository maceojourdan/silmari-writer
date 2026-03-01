/**
 * DraftingModule - Contains the drafting workflow UI state and navigation.
 *
 * Resource: ui-v3n6 (module)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * Fetches claim + drafting status and renders the ClaimStatusPanel.
 * Shows error boundary fallback on data load failure.
 */

'use client';

import React from 'react';
import { useClaimStatus } from '@/data_loaders/useClaimStatus';
import { ClaimStatusPanel } from '@/components/ClaimStatusPanel';

export interface DraftingModuleProps {
  claimId: string;
}

export function DraftingModule({ claimId }: DraftingModuleProps) {
  const { data, loading, error } = useClaimStatus(claimId);

  return (
    <div data-testid="drafting-module">
      <h2>Drafting Workflow</h2>
      <ClaimStatusPanel data={data} loading={loading} error={error} />
    </div>
  );
}
