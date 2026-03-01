/**
 * DraftGenerationService - Business logic for generating structured drafts
 * from confirmed claims within a claim set.
 *
 * Orchestrates retrieval of confirmed claims, transformation into
 * structured draft sections, and persistence of the generated draft.
 *
 * Resource: db-h2s4 (service)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { StoryDAO } from '@/server/data_access_objects/StoryDAO';
import type { StoryClaim, StructuredDraft } from '@/server/data_structures/StoryStructures';
import { StructuredDraftSchema } from '@/server/data_structures/StoryStructures';
import {
  DraftDocumentStructure,
  type DraftSection,
} from '@/server/data_structures/DraftDocumentStructure';
import {
  DraftGenerationError,
  DraftDataAccessError,
} from '@/server/error_definitions/DraftErrors';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';

export const DraftGenerationService = {
  /**
   * Step 3: Retrieve confirmed claims from a claim set.
   *
   * Fetches all claims for the given claim set, filters to only
   * those with status 'CONFIRMED', and validates the result.
   *
   * @throws DraftGenerationError.CLAIM_SET_NOT_FOUND if claim set doesn't exist
   * @throws DraftGenerationError.NO_CONFIRMED_CLAIMS if no confirmed claims found
   */
  async retrieveConfirmedClaims(claimSetId: string): Promise<StoryClaim[]> {
    const claims = await StoryDAO.getClaimsBySetId(claimSetId);

    if (claims === null) {
      throw DraftGenerationError.CLAIM_SET_NOT_FOUND(
        `Claim set '${claimSetId}' not found`,
      );
    }

    const confirmedClaims = claims.filter(
      (claim) => claim.status === 'CONFIRMED',
    );

    if (confirmedClaims.length === 0) {
      throw DraftGenerationError.NO_CONFIRMED_CLAIMS(
        `No confirmed claims found in claim set '${claimSetId}'`,
      );
    }

    return confirmedClaims;
  },

  /**
   * Step 4: Transform confirmed claims into a structured draft.
   *
   * Groups claims by section, validates required sections are present,
   * and constructs a Draft DTO conforming to DraftDocumentStructure.
   *
   * @throws SharedErrors.TransformationError if required sections are missing
   */
  transformClaimsToDraft(
    claimSetId: string,
    confirmedClaims: StoryClaim[],
  ): StructuredDraft {
    const requiredSections = DraftDocumentStructure.getRequiredSections();

    // Group claims by section
    const claimsBySection = new Map<DraftSection, StoryClaim[]>();
    for (const section of requiredSections) {
      claimsBySection.set(section, []);
    }

    for (const claim of confirmedClaims) {
      if (!DraftDocumentStructure.isValidSection(claim.section)) {
        throw SharedErrors.TransformationError(
          `Claim '${claim.id}' has invalid section '${claim.section}'`,
        );
      }
      const sectionClaims = claimsBySection.get(claim.section);
      if (sectionClaims) {
        sectionClaims.push(claim);
      }
    }

    // Validate all required sections have at least one claim
    for (const section of requiredSections) {
      const sectionClaims = claimsBySection.get(section);
      if (!sectionClaims || sectionClaims.length === 0) {
        throw SharedErrors.TransformationError(
          `Required section '${section}' has no confirmed claims`,
        );
      }
    }

    // Build sections ordered by DraftDocumentStructure
    const sections = requiredSections.map((sectionName) => ({
      sectionName,
      claims: (claimsBySection.get(sectionName) || []).sort(
        (a, b) => a.order - b.order,
      ),
    }));

    const draft: StructuredDraft = {
      id: crypto.randomUUID(),
      claimSetId,
      sections,
      createdAt: new Date().toISOString(),
    };

    // Validate draft against schema
    const parsed = StructuredDraftSchema.safeParse(draft);
    if (!parsed.success) {
      throw SharedErrors.TransformationError(
        `Draft validation failed: ${parsed.error.message}`,
      );
    }

    return parsed.data;
  },

  /**
   * Step 5: Persist the generated draft.
   *
   * @throws DraftDataAccessError.PERSISTENCE_FAILED on database error
   */
  async persistDraft(draft: StructuredDraft): Promise<StructuredDraft> {
    try {
      return await StoryDAO.saveDraft(draft);
    } catch (error) {
      throw DraftDataAccessError.PERSISTENCE_FAILED(
        `Failed to persist draft: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }
  },

  /**
   * Full orchestration: retrieve → transform → persist.
   *
   * Called by the request handler to execute the complete
   * draft generation flow.
   */
  async generate(claimSetId: string): Promise<StructuredDraft> {
    // Step 3: Retrieve confirmed claims
    const confirmedClaims = await this.retrieveConfirmedClaims(claimSetId);

    // Step 4: Transform into structured draft
    const draft = this.transformClaimsToDraft(claimSetId, confirmedClaims);

    // Step 5: Persist and return
    return await this.persistDraft(draft);
  },
} as const;
