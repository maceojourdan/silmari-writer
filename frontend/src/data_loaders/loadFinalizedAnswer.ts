/**
 * loadFinalizedAnswer - Data loader that bridges frontend UI to the backend
 * export endpoint for retrieving finalized answer content.
 *
 * Resource: ui-y5t3 (data_loader)
 * Path: 334-export-or-copy-finalized-answer
 *
 * Uses the exportFinalizedAnswer API contract to fetch and validate
 * the response from the backend.
 */

import {
  exportFinalizedAnswer,
  type ExportFinalizedAnswerRequest,
  type ExportFinalizedAnswerResponse,
} from '@/api_contracts/exportFinalizedAnswer';

export async function loadFinalizedAnswer(
  request: ExportFinalizedAnswerRequest,
): Promise<ExportFinalizedAnswerResponse> {
  return exportFinalizedAnswer(request);
}
