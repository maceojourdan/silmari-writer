/**
 * BehavioralQuestionEvaluateHandler - Maps request body to EvaluateCommand
 * and delegates to BehavioralQuestionService.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 */

import type { EvaluateCommand, EvaluateResult } from '@/server/data_structures/BehavioralQuestion';
import { BehavioralQuestionService } from '@/server/services/BehavioralQuestionService';

export interface EvaluateRequestBody {
  sessionId: string;
  objective: string;
  actions: string[];
  obstacles: string[];
  outcome: string;
  roleClarity: string;
}

export const BehavioralQuestionEvaluateHandler = {
  /**
   * Map validated request body → EvaluateCommand.
   */
  toCommand(body: EvaluateRequestBody): EvaluateCommand {
    return {
      sessionId: body.sessionId,
      objective: body.objective,
      actions: body.actions,
      obstacles: body.obstacles,
      outcome: body.outcome,
      roleClarity: body.roleClarity,
    };
  },

  /**
   * Handle the full request flow: transform → evaluate.
   */
  async handle(body: EvaluateRequestBody): Promise<EvaluateResult> {
    const command = this.toCommand(body);
    return BehavioralQuestionService.evaluateForVerify(command);
  },
} as const;
