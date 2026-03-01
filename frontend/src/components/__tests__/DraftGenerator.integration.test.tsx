/**
 * DraftGenerator.integration.test.tsx — Terminal Condition (path 326)
 *
 * Integration test covering the full path:
 * UI → API Contract → Handler → Service → DAO (mocked)
 *
 * Scenario: Case contains:
 * - 2 confirmed claims
 * - 1 unconfirmed claim
 * - 1 rejected claim
 *
 * Assertions:
 * - Draft content includes both confirmed claims
 * - Draft excludes unconfirmed/rejected claims
 * - claimsUsed contains only confirmed IDs
 * - UI displays structured draft
 *
 * TLA+ Properties:
 * - Reachability: End-to-end path executes
 * - TypeInvariant: Types preserved across boundaries
 * - ErrorConsistency: All error branches return structured errors
 *
 * Resource: ui-w8p2, api-q7v1, api-n8k2, db-h2s4, db-d3w8
 * Path: 326-generate-draft-with-only-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import type { CaseClaim } from '@/server/data_structures/Claim';
import { CaseDraftSchema } from '@/server/data_structures/Claim';
import { DraftError } from '@/server/error_definitions/DraftErrors';

// ---------------------------------------------------------------------------
// Mock only the DAO (lowest layer) — everything else is real
// ---------------------------------------------------------------------------

vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getClaimsByCaseId: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    getUnverifiedClaimsBySession: vi.fn(),
    updateStatusToVerified: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

// Mock StoryDAO (used by path 325 methods, not exercised here)
vi.mock('@/server/data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    getClaimsBySetId: vi.fn(),
    saveDraft: vi.fn(),
  },
}));

// Mock the frontend logger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock fetch for the API call (since we can't spin up Next.js server)
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

import DraftGenerator from '../DraftGenerator';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { DraftGenerationService } from '@/server/services/DraftGenerationService';
import { generateDraftHandler } from '@/server/request_handlers/generateDraftHandler';

const mockClaimDAO = vi.mocked(ClaimDAO);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validCaseId = 'case-integration-test';

function createCaseClaim(overrides: Partial<CaseClaim> = {}): CaseClaim {
  return {
    id: `claim-${Math.random().toString(36).slice(2, 8)}`,
    caseId: validCaseId,
    text: 'Test claim text',
    status: 'confirmed',
    metadata: undefined,
    ...overrides,
  };
}

const confirmedClaim1 = createCaseClaim({
  id: 'confirmed-1',
  text: 'The applicant has 5 years of relevant experience',
  status: 'confirmed',
});

const confirmedClaim2 = createCaseClaim({
  id: 'confirmed-2',
  text: 'The applicant holds a valid professional certification',
  status: 'confirmed',
});

const unconfirmedClaim = createCaseClaim({
  id: 'unconfirmed-1',
  text: 'The applicant claims to have won an industry award',
  status: 'unconfirmed',
});

const rejectedClaim = createCaseClaim({
  id: 'rejected-1',
  text: 'The applicant claims to have a PhD',
  status: 'rejected',
});

const allClaims = [confirmedClaim1, confirmedClaim2, unconfirmedClaim, rejectedClaim];

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerator Integration — Terminal Condition (path 326)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full end-to-end path
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should execute full path: Service → DAO → filter → compose → return draft', async () => {
      // Set up DAO mock with mixed claims
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce(allClaims);

      // Exercise the service layer directly (bypassing HTTP)
      const draft = await DraftGenerationService.generateCaseDraft(validCaseId);

      // Draft should contain ONLY confirmed claims
      expect(draft.content).toContain('The applicant has 5 years of relevant experience');
      expect(draft.content).toContain('The applicant holds a valid professional certification');
      expect(draft.content).not.toContain('The applicant claims to have won an industry award');
      expect(draft.content).not.toContain('The applicant claims to have a PhD');
    });

    it('should execute handler → service → DAO path', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce(allClaims);

      const result = await generateDraftHandler.handleCaseDraft(validCaseId);

      expect(result.caseId).toBe(validCaseId);
      expect(result.content).toContain('The applicant has 5 years of relevant experience');
      expect(result.claimsUsed).toContain('confirmed-1');
      expect(result.claimsUsed).toContain('confirmed-2');
    });

    it('should render draft in UI after successful API flow', async () => {
      // Mock the fetch call to simulate API response
      const mockDraft = {
        caseId: validCaseId,
        content: 'The applicant has 5 years of relevant experience\n\nThe applicant holds a valid professional certification',
        claimsUsed: ['confirmed-1', 'confirmed-2'],
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDraft,
      });

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByTestId('draft-content')).toBeInTheDocument();
        expect(screen.getByText(/5 years of relevant experience/)).toBeInTheDocument();
        expect(screen.getByText(/valid professional certification/)).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Types preserved across boundaries
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should produce draft conforming to CaseDraft schema through service', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce(allClaims);

      const draft = await DraftGenerationService.generateCaseDraft(validCaseId);

      const parsed = CaseDraftSchema.safeParse(draft);
      expect(parsed.success).toBe(true);
    });

    it('should include only confirmed claim IDs in claimsUsed', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce(allClaims);

      const draft = await DraftGenerationService.generateCaseDraft(validCaseId);

      expect(draft.claimsUsed).toEqual(['confirmed-1', 'confirmed-2']);
      expect(draft.claimsUsed).not.toContain('unconfirmed-1');
      expect(draft.claimsUsed).not.toContain('rejected-1');
    });

    it('should preserve caseId across boundaries', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce(allClaims);

      const draft = await generateDraftHandler.handleCaseDraft(validCaseId);

      expect(draft.caseId).toBe(validCaseId);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: All error branches produce structured errors
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should propagate DAO errors as DraftError through full path', async () => {
      mockClaimDAO.getClaimsByCaseId.mockRejectedValueOnce(
        new Error('Connection timeout'),
      );

      await expect(
        generateDraftHandler.handleCaseDraft(validCaseId),
      ).rejects.toThrow(DraftError);

      try {
        mockClaimDAO.getClaimsByCaseId.mockRejectedValueOnce(
          new Error('Connection timeout'),
        );
        await generateDraftHandler.handleCaseDraft(validCaseId);
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('DATA_ACCESS_ERROR');
      }
    });

    it('should produce GENERATION_FAILED when no confirmed claims exist', async () => {
      mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([
        unconfirmedClaim,
        rejectedClaim,
      ]);

      await expect(
        generateDraftHandler.handleCaseDraft(validCaseId),
      ).rejects.toThrow(DraftError);

      try {
        mockClaimDAO.getClaimsByCaseId.mockResolvedValueOnce([
          unconfirmedClaim,
          rejectedClaim,
        ]);
        await generateDraftHandler.handleCaseDraft(validCaseId);
      } catch (e) {
        expect(e).toBeInstanceOf(DraftError);
        expect((e as DraftError).code).toBe('GENERATION_FAILED');
      }
    });

    it('should show error in UI when API fails', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({ code: 'INTERNAL_ERROR', message: 'Server failure' }),
      });

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });
      expect(screen.queryByTestId('draft-content')).not.toBeInTheDocument();
    });
  });
});
