/**
 * DraftService - Business logic for the DRAFT state path.
 *
 * Encapsulates claim filtering and draft generation.
 *
 * Resource: db-h2s4 (service)
 * Path: 298-draft-state-filters-unconfirmed-hard-claims-and-records-claims-used
 */

import type {
  DraftStoryRecord,
  FilteredClaimSet,
  DraftPayload,
} from '@/server/data_structures/DraftStoryRecord';
import { TruthCheckVerifier } from '@/server/verifiers/TruthCheckVerifier';
import { DraftServiceError } from '@/server/error_definitions/DraftErrors';

export const DraftService = {
  /**
   * Step 3: Filter unconfirmed hard claims.
   *
   * Business rules:
   * - Hard claims: include only if truth_check.status === 'confirmed'
   * - Soft claims: always include (no truth_check requirement)
   * - Missing confirmation metadata on hard claim → exclude (not throw)
   * - Invalid structure → throw DraftValidationError.INVALID_TRUTH_CHECK
   */
  filterConfirmedClaims(record: DraftStoryRecord): FilteredClaimSet {
    // Validate structure of each claim (throws on invalid)
    const validatedClaims = TruthCheckVerifier.validateAll(record.truth_checks);

    return validatedClaims.filter((claim) => {
      if (claim.type === 'soft') {
        return true;
      }

      // Hard claim: must have confirmed truth_check
      if (claim.type === 'hard') {
        return claim.truth_check?.status === 'confirmed';
      }

      return false;
    });
  },

  /**
   * Step 4: Generate draft text and claims_used metadata.
   *
   * Uses deterministic template composition (no LLM in unit test).
   * claims_used = IDs of all filtered claims included in draft.
   */
  generateDraft(filteredClaims: FilteredClaimSet): DraftPayload {
    try {
      const draft_text = filteredClaims
        .map((claim) => claim.text)
        .join('\n\n');

      const claims_used = filteredClaims.map((claim) => claim.id);

      return { draft_text, claims_used };
    } catch (error) {
      throw DraftServiceError.GENERATION_FAILED(
        `Draft generation failed: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },
} as const;
