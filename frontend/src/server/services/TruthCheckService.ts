/**
 * TruthCheckService - Orchestrates the creation and persistence
 * of truth check entries.
 *
 * Resource: db-h2s4 (service)
 * Path: 297-confirm-metric-claim-truth-check
 *
 * Flow:
 * 1. Receive validated command (claim_id, status, source).
 * 2. Persist via TruthCheckDAO.create().
 * 3. Return persisted record.
 * 4. Map DB exceptions to PersistenceError.
 */

import type { ConfirmCommand, ConfirmResult } from '@/server/data_structures/TruthCheck';
import { TruthCheckDAO } from '@/server/data_access_objects/TruthCheckDAO';
import { TruthCheckErrors } from '@/server/error_definitions/TruthCheckErrors';

export const TruthCheckService = {
  /**
   * Confirm or deny a metric claim by persisting a truth check entry.
   */
  async confirm(command: ConfirmCommand): Promise<ConfirmResult> {
    try {
      const record = await TruthCheckDAO.create({
        claim_id: command.claim_id,
        status: command.status,
        source: command.source,
      });

      return {
        id: record.id,
        claim_id: record.claim_id,
        status: record.status,
        source: record.source,
        created_at: record.created_at,
      };
    } catch (error) {
      // If it's already a TruthCheckError, re-throw
      if (error instanceof Error && error.name === 'TruthCheckError') {
        throw error;
      }

      throw TruthCheckErrors.PERSISTENCE_ERROR(
        `Failed to persist truth check: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },
} as const;
