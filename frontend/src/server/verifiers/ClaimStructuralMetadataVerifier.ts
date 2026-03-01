/**
 * ClaimStructuralMetadataVerifier - Validates required structural metadata
 * completeness for claims during draft generation.
 *
 * Partitions confirmed claims into complete (eligible for drafting) and
 * incomplete (excluded from draft with reason) sets based on the presence
 * of required metadata fields: metric, scope, context.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 328-exclude-incomplete-claim-during-draft-generation
 */

import type { ConfirmedClaim, IncompleteClaimReport, StructuralMetadataField } from '@/server/data_structures/Claim';
import { REQUIRED_STRUCTURAL_METADATA_FIELDS } from '@/server/data_structures/Claim';
import { logger } from '@/server/logging/logger';

export interface CompletenessPartition {
  complete: ConfirmedClaim[];
  incomplete: IncompleteClaimReport[];
}

export const ClaimStructuralMetadataVerifier = {
  /**
   * Partitions claims into complete and incomplete sets based on
   * required structural metadata fields.
   *
   * A claim is "complete" if it has non-empty values for all of:
   *   - metric
   *   - scope
   *   - context
   *
   * If a rule evaluation exception occurs for a specific claim,
   * the claim is treated as incomplete and the error is logged
   * via backend logging (cfg-q9c5).
   */
  partitionByCompleteness(claims: ConfirmedClaim[]): CompletenessPartition {
    const complete: ConfirmedClaim[] = [];
    const incomplete: IncompleteClaimReport[] = [];

    for (const claim of claims) {
      try {
        const missingFields: StructuralMetadataField[] = [];

        for (const field of REQUIRED_STRUCTURAL_METADATA_FIELDS) {
          const value = claim[field];
          if (!value || value.trim().length === 0) {
            missingFields.push(field);
          }
        }

        if (missingFields.length === 0) {
          complete.push(claim);
        } else {
          incomplete.push({
            claimId: claim.id,
            missingFields,
          });
        }
      } catch (error) {
        // On rule evaluation exception, treat as incomplete and log
        logger.error(
          'Rule evaluation failed for claim; treating as incomplete',
          error,
          { path: '328', resource: 'db-j6x9', claimId: claim.id },
        );
        incomplete.push({
          claimId: claim.id,
          missingFields: [...REQUIRED_STRUCTURAL_METADATA_FIELDS],
        });
      }
    }

    return { complete, incomplete };
  },
} as const;
