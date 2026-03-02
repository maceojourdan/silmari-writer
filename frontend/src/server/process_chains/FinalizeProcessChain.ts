/**
 * FinalizeProcessChain - Orchestrates the finalize-answer-without-sms-follow-up workflow.
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 336-finalize-answer-without-sms-follow-up
 */

import { FinalizeCompletionContextSchema } from '@/server/data_structures/FinalizeCompletion';
import type { PostFinalizeResult } from '@/server/data_structures/FinalizeCompletion';
import { FinalizeService } from '@/server/services/FinalizeService';
import { finalizeLogger } from '@/server/logging/finalizeLogger';

// ---------------------------------------------------------------------------
// Process Chain
// ---------------------------------------------------------------------------

export const FinalizeProcessChain = {
  /**
   * Step 1: Handle finalize completion event.
   *
   * Validates the event payload using Zod schema. On invalid input, logs
   * the error via finalizeLogger and returns void (early exit).
   * On valid input, calls FinalizeService.evaluatePostFinalize with the
   * parsed context and returns the workflow result.
   */
  async handleFinalizeCompletion(event: unknown): Promise<PostFinalizeResult | undefined> {
    const result = FinalizeCompletionContextSchema.safeParse(event);

    if (!result.success) {
      finalizeLogger.error(
        'Finalize completion event validation failed',
        result.error,
        {
          event: typeof event === 'object' ? JSON.stringify(event) : String(event),
          issues: result.error.issues.map(i => i.message).join(', '),
        },
      );
      return undefined;
    }

    const context = result.data;

    return FinalizeService.evaluatePostFinalize(context);
  },
} as const;
