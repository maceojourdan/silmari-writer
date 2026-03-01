/**
 * DraftGenerationService - Business logic for generating structured drafts
 * from confirmed claims within a claim set.
 *
 * Orchestrates retrieval of confirmed claims, transformation into
 * structured draft sections, and persistence of the generated draft.
 *
 * Resource: db-h2s4 (service)
 * Paths:
 *   - 325-generate-draft-from-confirmed-claims
 *   - 327-prevent-draft-generation-without-confirmed-claims
 */

import { StoryDAO } from '@/server/data_access_objects/StoryDAO';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import type { StoryClaim, StructuredDraft } from '@/server/data_structures/StoryStructures';
import { StructuredDraftSchema } from '@/server/data_structures/StoryStructures';
import type { CaseClaim, CaseDraft, StoryRecordClaim } from '@/server/data_structures/Claim';
import { CaseDraftSchema } from '@/server/data_structures/Claim';
import {
  DraftDocumentStructure,
  type DraftSection,
} from '@/server/data_structures/DraftDocumentStructure';
import {
  DraftGenerationError,
  DraftDataAccessError,
  DraftErrors326,
  DraftErrors327,
} from '@/server/error_definitions/DraftErrors';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';
import { logger } from '@/server/logging/logger';

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

  // =========================================================================
  // Path 326: generate-draft-with-only-confirmed-claims
  // =========================================================================

  /**
   * Step 4 (path 326): Retrieve and filter confirmed claims for a case.
   *
   * Fetches all claims for the given caseId via ClaimDAO,
   * then filters to only those with status === 'confirmed'.
   * Empty confirmed set is allowed (returns empty array).
   *
   * @throws DraftErrors326.DataAccessError on DAO failure
   */
  async getConfirmedClaimsForCase(caseId: string): Promise<CaseClaim[]> {
    try {
      const claims = await ClaimDAO.getClaimsByCaseId(caseId);
      return claims.filter((c) => c.status === 'confirmed');
    } catch (error) {
      logger.error(
        'Failed to retrieve claims for case',
        error,
        { path: '326', resource: 'db-h2s4', caseId },
      );
      throw DraftErrors326.DataAccessError(
        `Failed to retrieve claims for case '${caseId}': ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },

  /**
   * Step 5 (path 326): Compose a simple draft from confirmed claims.
   *
   * Joins claim texts with double newlines, collects IDs.
   *
   * @throws DraftErrors326.GenerationError if claims array is empty or contains invalid claims
   */
  composeCaseDraft(caseId: string, confirmedClaims: CaseClaim[]): CaseDraft {
    if (confirmedClaims.length === 0) {
      throw DraftErrors326.GenerationError(
        'Cannot compose draft from empty claims array',
      );
    }

    // Validate each claim has non-empty text
    for (const claim of confirmedClaims) {
      if (!claim.text || claim.text.trim().length === 0) {
        throw DraftErrors326.GenerationError(
          `Claim '${claim.id}' has missing or empty text`,
        );
      }
    }

    const draft: CaseDraft = {
      caseId,
      content: confirmedClaims.map((c) => c.text).join('\n\n'),
      claimsUsed: confirmedClaims.map((c) => c.id),
    };

    // Validate against schema
    const parsed = CaseDraftSchema.safeParse(draft);
    if (!parsed.success) {
      throw DraftErrors326.GenerationError(
        `Draft validation failed: ${parsed.error.message}`,
      );
    }

    return parsed.data;
  },

  /**
   * Full orchestration (path 326): retrieve confirmed → compose draft.
   *
   * Called by the handler to generate a case-based draft.
   *
   * @throws DraftErrors326.DataAccessError on retrieval failure
   * @throws DraftErrors326.GenerationError on composition failure
   */
  async generateCaseDraft(caseId: string): Promise<CaseDraft> {
    // Step 4: Retrieve confirmed claims
    const confirmedClaims = await this.getConfirmedClaimsForCase(caseId);

    // Step 5: Compose draft
    return this.composeCaseDraft(caseId, confirmedClaims);
  },

  // =========================================================================
  // Path 327: prevent-draft-generation-without-confirmed-claims
  // =========================================================================

  /**
   * Step 3 (path 327): Check for confirmed claims for a story record.
   *
   * Fetches all claims for the given storyRecordId via ClaimDAO,
   * then filters to only those with `confirmed === true`.
   * If zero confirmed claims exist, throws NoConfirmedClaimsError.
   *
   * @throws DraftErrors327.DataAccessError on DAO failure
   * @throws DraftErrors327.NoConfirmedClaimsError if no confirmed claims exist
   */
  async checkConfirmedClaimsForStoryRecord(storyRecordId: string): Promise<StoryRecordClaim[]> {
    let claims: StoryRecordClaim[];

    try {
      claims = await ClaimDAO.getClaimsByStoryRecordId(storyRecordId);
    } catch (error) {
      logger.error(
        'Failed to retrieve claims for story record',
        error,
        { path: '327', resource: 'db-h2s4', storyRecordId },
      );
      throw DraftErrors327.DataAccessError(
        `Failed to retrieve claims for story record '${storyRecordId}': ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }

    const confirmedClaims = claims.filter((claim) => claim.confirmed === true);

    if (confirmedClaims.length === 0) {
      throw DraftErrors327.NoConfirmedClaimsError(
        `No confirmed claims found for story record '${storyRecordId}'`,
      );
    }

    return confirmedClaims;
  },
} as const;
