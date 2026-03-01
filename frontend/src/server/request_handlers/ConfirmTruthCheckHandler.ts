/**
 * ConfirmTruthCheckHandler - Maps request body to ConfirmCommand
 * and delegates to TruthCheckService.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 297-confirm-metric-claim-truth-check
 */

import type { ConfirmCommand, ConfirmResult, TruthCheckStatus } from '@/server/data_structures/TruthCheck';
import { TruthCheckService } from '@/server/services/TruthCheckService';

export interface ConfirmTruthCheckRequestBody {
  claim_id: string;
  status: TruthCheckStatus;
  source: string;
}

export const ConfirmTruthCheckHandler = {
  /**
   * Map validated request body → ConfirmCommand.
   */
  toCommand(body: ConfirmTruthCheckRequestBody): ConfirmCommand {
    return {
      claim_id: body.claim_id,
      status: body.status,
      source: body.source,
    };
  },

  /**
   * Handle the full request flow: transform → confirm.
   */
  async handle(body: ConfirmTruthCheckRequestBody): Promise<ConfirmResult> {
    const command = this.toCommand(body);
    return TruthCheckService.confirm(command);
  },
} as const;
