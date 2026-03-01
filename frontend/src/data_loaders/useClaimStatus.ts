/**
 * useClaimStatus - React hook for fetching claim and drafting status.
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * Fetches GET /api/claims/[claimId]/status and returns typed state.
 */

'use client';

import { useState, useEffect } from 'react';
import { frontendLogger } from '@/logging/index';
import type { ClaimStatusResponse } from '@/server/data_structures/DraftingWorkflow';

export interface UseClaimStatusResult {
  data: ClaimStatusResponse | null;
  loading: boolean;
  error: Error | null;
}

export function useClaimStatus(claimId: string): UseClaimStatusResult {
  const [data, setData] = useState<ClaimStatusResponse | null>(null);
  const [loading, setLoading] = useState<boolean>(true);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    if (!claimId) {
      setLoading(false);
      return;
    }

    let cancelled = false;

    async function fetchStatus() {
      try {
        setLoading(true);
        setError(null);

        const response = await fetch(`/api/claims/${claimId}/status`);

        if (!response.ok) {
          const errorBody = await response.json().catch(() => ({}));
          throw new Error(errorBody.message || `HTTP ${response.status}`);
        }

        const json = await response.json();

        if (!cancelled) {
          setData(json);
        }
      } catch (err) {
        if (!cancelled) {
          const loadError = err instanceof Error ? err : new Error(String(err));
          setError(loadError);

          frontendLogger.error(
            'Failed to load claim status',
            loadError,
            {
              component: 'useClaimStatus',
              module: 'drafting',
              action: 'fetch',
              claimId,
            },
          );
        }
      } finally {
        if (!cancelled) {
          setLoading(false);
        }
      }
    }

    fetchStatus();

    return () => {
      cancelled = true;
    };
  }, [claimId]);

  return { data, loading, error };
}
