/**
 * DraftAssemblyProcessor - Executes core draft assembly logic.
 *
 * Takes a set of structurally complete confirmed claims and generates
 * draft text content. Only complete claims are included in the output.
 *
 * Resource: db-b7r2 (processor)
 * Path: 328-exclude-incomplete-claim-during-draft-generation
 */

import type { ConfirmedClaim } from '@/server/data_structures/Claim';

export const DraftAssemblyProcessor = {
  /**
   * Generate draft content from the given complete claims.
   *
   * Joins claim content with double newlines, producing a
   * simple text-based draft.
   *
   * @param completeClaims - Claims that have passed structural metadata validation.
   * @returns The assembled draft content string.
   * @throws Error if no claims are provided (assembly impossible).
   */
  generateDraft(completeClaims: ConfirmedClaim[]): string {
    if (completeClaims.length === 0) {
      return '';
    }

    return completeClaims.map((claim) => claim.content).join('\n\n');
  },
} as const;
