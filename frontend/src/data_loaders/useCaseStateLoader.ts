/**
 * useCaseStateLoader - React hook that loads case state from the backend
 * and exposes drafting blocked status for UI access control.
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 322-handle-disputed-claims-and-block-drafting
 *
 * On success → updates caseState with blocked/allowed status.
 * On error → logs via frontendLogger and sets recoverable UI error state.
 */

import { useState, useCallback } from 'react';
import type { CaseStateResponse } from '@/server/data_structures/Case';
import { getCaseState } from '@/api_contracts/getCaseState';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Hook Return Type
// ---------------------------------------------------------------------------

export interface UseCaseStateLoaderReturn {
  caseState: CaseStateResponse | null;
  isLoading: boolean;
  error: string | null;
  loadCaseState: () => Promise<void>;
}

// ---------------------------------------------------------------------------
// Hook Implementation
// ---------------------------------------------------------------------------

export function useCaseStateLoader(caseId: string): UseCaseStateLoaderReturn {
  const [caseState, setCaseState] = useState<CaseStateResponse | null>(null);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const loadCaseState = useCallback(async () => {
    setError(null);
    setIsLoading(true);

    try {
      const result = await getCaseState(caseId);
      setCaseState(result);
    } catch (err) {
      const message = err instanceof Error ? err.message : 'An unexpected error occurred';

      frontendLogger.error(
        'Failed to load case state',
        err instanceof Error ? err : new Error(String(err)),
        { module: 'useCaseStateLoader', action: 'loadCaseState' },
      );

      setError(message);
      setCaseState(null);
    } finally {
      setIsLoading(false);
    }
  }, [caseId]);

  return {
    caseState,
    isLoading,
    error,
    loadCaseState,
  };
}
