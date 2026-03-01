/**
 * getCaseState - Typed fetch wrapper for retrieving case state
 * from the backend API.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import type { CaseStateResponse } from '@/server/data_structures/Case';

/**
 * Fetch the current case state for a given case ID.
 *
 * @param caseId - The case ID to query
 * @returns CaseStateResponse with drafting status and blocked flag
 * @throws Error if the fetch fails or response is not OK
 */
export async function getCaseState(caseId: string): Promise<CaseStateResponse> {
  const response = await fetch(`/api/case/${caseId}/state`);

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Failed to fetch case state: ${response.status}`,
    );
  }

  return response.json();
}
