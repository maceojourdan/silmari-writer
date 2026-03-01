/**
 * FinalizeProcessor - Executes finalization logic: validates draft state,
 * transforms to export artifact, persists FINALIZED status, computes metrics.
 *
 * Resource: db-b7r2 (processor)
 * Path: 300-finalize-approved-draft-and-log-metrics
 */

import type { Draft, ExportArtifact, FinalizeMetrics } from '@/server/data_structures/Draft';
import { DraftDAO } from '@/server/data_access_objects/DraftDAO';
import { FinalizeErrors } from '@/server/error_definitions/FinalizeErrors';
import { logger } from '@/server/logging/logger';
import { frontendLogger } from '@/logging/index';

export const FinalizeProcessor = {
  /**
   * Step 2: Validate that the draft exists and is in APPROVED state.
   * Throws FinalizeErrors.DraftNotFound or InvalidDraftState on failure.
   */
  async validateApprovedDraft(draftId: string): Promise<Draft> {
    const draft = await DraftDAO.getDraftById(draftId);

    if (!draft) {
      throw FinalizeErrors.DraftNotFound(`Draft with id ${draftId} not found`);
    }

    if (draft.status !== 'APPROVED') {
      throw FinalizeErrors.InvalidDraftState(
        `Draft ${draftId} is in ${draft.status} state, expected APPROVED`,
      );
    }

    return draft;
  },

  /**
   * Step 3: Transform approved draft into exportable artifact format.
   * Pure transformation — no side effects.
   */
  transformToArtifact(draft: Draft): ExportArtifact {
    const now = new Date().toISOString();

    return {
      draftId: draft.id,
      content: draft.content,
      title: draft.title,
      exportedAt: now,
      format: 'text',
      metadata: {
        userId: draft.userId,
        originalCreatedAt: draft.createdAt,
        finalizedAt: now,
      },
    };
  },

  /**
   * Step 3: Full finalization — validate, transform, persist.
   * On persistence failure, draft remains APPROVED.
   */
  async finalizeDraft(draftId: string): Promise<{ artifact: ExportArtifact; status: 'FINALIZED' }> {
    // 1. Validate
    const draft = await this.validateApprovedDraft(draftId);

    // 2. Transform
    const artifact = this.transformToArtifact(draft);

    // 3. Persist FINALIZED status
    try {
      await DraftDAO.updateStatus(draftId, 'FINALIZED', {
        finalizedAt: artifact.metadata.finalizedAt,
      });
    } catch (error) {
      // Log and rethrow as PersistenceFailure — draft remains APPROVED
      logger.error(
        'Failed to persist finalized status',
        error,
        { path: '300-finalize-approved-draft-and-log-metrics', resource: 'db-b7r2', draftId },
      );
      throw FinalizeErrors.PersistenceFailure(
        `Failed to persist FINALIZED status for draft ${draftId}`,
      );
    }

    return { artifact, status: 'FINALIZED' };
  },

  /**
   * Step 4: Compute metrics from finalized draft data.
   * Pure function — no side effects.
   */
  computeMetrics(draft: Draft): FinalizeMetrics {
    // Time-to-draft: milliseconds from creation to approval
    const createdAt = new Date(draft.createdAt).getTime();
    const approvedAt = draft.approvedAt
      ? new Date(draft.approvedAt).getTime()
      : new Date(draft.updatedAt).getTime();
    const timeToDraft = approvedAt - createdAt;

    // Confirmation rate: ratio of verified claims to total claims
    const interaction = draft.interactionData;
    const confirmationRate = interaction && interaction.totalClaims > 0
      ? interaction.claimsVerified / interaction.totalClaims
      : 0;

    // Signal density: ratio of signal events to total edits + revisions
    const totalActions = interaction
      ? interaction.editsCount + interaction.revisionsCount
      : 0;
    const signalDensity = totalActions > 0 && interaction
      ? interaction.signalEvents / totalActions
      : 0;

    return { timeToDraft, confirmationRate, signalDensity };
  },

  /**
   * Step 4: Compute and log metrics. Errors are swallowed and logged —
   * FINALIZED state remains valid regardless of metrics success.
   */
  async computeAndLogMetrics(draft: Draft): Promise<boolean> {
    try {
      const metrics = this.computeMetrics(draft);

      frontendLogger.info('Finalize metrics computed', {
        module: 'FinalizeProcessor',
        action: 'computeAndLogMetrics',
        draftId: draft.id,
        ...metrics,
      });

      return true;
    } catch (error) {
      frontendLogger.error(
        'Failed to compute finalize metrics',
        error instanceof Error ? error : new Error(String(error)),
        { module: 'FinalizeProcessor', action: 'computeAndLogMetrics', draftId: draft.id },
      );

      // Swallow error — FINALIZED state remains valid
      return false;
    }
  },
} as const;
