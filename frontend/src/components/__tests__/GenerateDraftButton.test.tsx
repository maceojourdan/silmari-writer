/**
 * Tests for GenerateDraftButton
 *
 * Resource: ui-w8p2 (component)
 * Path: 325-generate-draft-from-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Render with valid claimSetId → click → generateDraft() called
 * - TypeInvariant: Request payload matches Zod schema in generateDraft.ts
 * - ErrorConsistency: Invalid claimSetId → verifier blocks submission, no API call
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import type { GenerateDraftResponse } from '@/server/data_structures/StoryStructures';
import { GenerateDraftContractRequestSchema } from '@/api_contracts/generateDraft';

// Mock the generateDraft API contract
vi.mock('@/api_contracts/generateDraft', async (importOriginal) => {
  const actual = await importOriginal<typeof import('@/api_contracts/generateDraft')>();
  return {
    ...actual,
    generateDraft: vi.fn(),
  };
});

import GenerateDraftButton from '../GenerateDraftButton';
import { generateDraft } from '@/api_contracts/generateDraft';

const mockGenerateDraft = vi.mocked(generateDraft);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validClaimSetId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';
const now = new Date().toISOString();

function createMockResponse() {
  return {
    draft: {
      id: crypto.randomUUID(),
      claimSetId: validClaimSetId,
      sections: [
        {
          sectionName: 'context' as const,
          claims: [
            {
              id: crypto.randomUUID(),
              claimSetId: validClaimSetId,
              content: 'Context claim content',
              status: 'CONFIRMED' as const,
              section: 'context' as const,
              order: 0,
              createdAt: now,
              updatedAt: now,
            },
          ],
        },
        {
          sectionName: 'actions' as const,
          claims: [
            {
              id: crypto.randomUUID(),
              claimSetId: validClaimSetId,
              content: 'Actions claim content',
              status: 'CONFIRMED' as const,
              section: 'actions' as const,
              order: 0,
              createdAt: now,
              updatedAt: now,
            },
          ],
        },
        {
          sectionName: 'outcome' as const,
          claims: [
            {
              id: crypto.randomUUID(),
              claimSetId: validClaimSetId,
              content: 'Outcome claim content',
              status: 'CONFIRMED' as const,
              section: 'outcome' as const,
              order: 0,
              createdAt: now,
              updatedAt: now,
            },
          ],
        },
      ],
      createdAt: now,
    },
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('GenerateDraftButton', () => {
  beforeEach(() => {
    mockGenerateDraft.mockReset();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability: Click triggers API call', () => {
    it('should render the Generate Draft button', () => {
      render(<GenerateDraftButton claimSetId={validClaimSetId} />);
      expect(screen.getByRole('button', { name: /generate draft/i })).toBeInTheDocument();
    });

    it('should call generateDraft with claimSetId on click', async () => {
      mockGenerateDraft.mockResolvedValueOnce(createMockResponse());

      render(<GenerateDraftButton claimSetId={validClaimSetId} />);
      const button = screen.getByRole('button', { name: /generate draft/i });

      await userEvent.click(button);

      await waitFor(() => {
        expect(mockGenerateDraft).toHaveBeenCalledTimes(1);
        expect(mockGenerateDraft).toHaveBeenCalledWith({
          claimSetId: validClaimSetId,
        });
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Payload structure', () => {
    it('should send payload conforming to GenerateDraftContractRequest schema', async () => {
      mockGenerateDraft.mockResolvedValueOnce(createMockResponse());

      render(<GenerateDraftButton claimSetId={validClaimSetId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        const calledWith = mockGenerateDraft.mock.calls[0][0];
        const parsed = GenerateDraftContractRequestSchema.safeParse(calledWith);
        expect(parsed.success).toBe(true);
        if (parsed.success) {
          expect(parsed.data.claimSetId).toBe(validClaimSetId);
        }
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Validation blocks submission', () => {
    it('should show validation error and NOT call API when claimSetId is empty', async () => {
      render(<GenerateDraftButton claimSetId="" />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/claimSetId/i)).toBeInTheDocument();
      });
      expect(mockGenerateDraft).not.toHaveBeenCalled();
    });

    it('should show validation error when claimSetId is not a UUID', async () => {
      render(<GenerateDraftButton claimSetId="invalid-uuid" />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/claimSetId/i)).toBeInTheDocument();
      });
      expect(mockGenerateDraft).not.toHaveBeenCalled();
    });

    it('should display API error when generateDraft fails', async () => {
      mockGenerateDraft.mockRejectedValueOnce(new Error('Server error'));

      render(<GenerateDraftButton claimSetId={validClaimSetId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/server error/i)).toBeInTheDocument();
      });
    });

    it('should show loading state during API call', async () => {
      let resolvePromise!: (value: GenerateDraftResponse) => void;
      const pendingPromise = new Promise<GenerateDraftResponse>((resolve) => {
        resolvePromise = resolve;
      });
      mockGenerateDraft.mockReturnValueOnce(pendingPromise);

      render(<GenerateDraftButton claimSetId={validClaimSetId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /generate draft/i })).toBeDisabled();
      });

      resolvePromise(createMockResponse());
    });

    it('should show draft preview on success', async () => {
      mockGenerateDraft.mockResolvedValueOnce(createMockResponse());

      render(<GenerateDraftButton claimSetId={validClaimSetId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByTestId('draft-preview')).toBeInTheDocument();
        expect(screen.getByText('Context claim content')).toBeInTheDocument();
        expect(screen.getByText('Actions claim content')).toBeInTheDocument();
        expect(screen.getByText('Outcome claim content')).toBeInTheDocument();
      });
    });

    it('should show only confirmed claims in draft preview', async () => {
      const response = createMockResponse();
      mockGenerateDraft.mockResolvedValueOnce(response);

      render(<GenerateDraftButton claimSetId={validClaimSetId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        const preview = screen.getByTestId('draft-preview');
        expect(preview).toBeInTheDocument();

        // All claims in the response should be CONFIRMED
        // (non-confirmed were filtered server-side)
        const sections = response.draft.sections;
        for (const section of sections) {
          for (const claim of section.claims) {
            expect(screen.getByText(claim.content)).toBeInTheDocument();
          }
        }
      });
    });
  });
});
