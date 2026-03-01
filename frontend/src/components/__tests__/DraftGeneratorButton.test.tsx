/**
 * Tests for DraftGeneratorButton — Step 1: Initiate draft generation request
 *
 * Resource: ui-w8p2 (component)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Render DraftGeneratorButton → click "Generate Draft" → generateStoryDraft() called
 * - TypeInvariant: API contract is invoked with typed GenerateStoryDraftRequest
 * - ErrorConsistency: Mock verifier to return invalid → no API call, validation message rendered
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import type { GenerateStoryDraftResponse } from '@/server/data_structures/Claim';
import { GenerateStoryDraftContractRequestSchema } from '@/api_contracts/generateDraft';

// Mock the generateStoryDraft API contract
vi.mock('@/api_contracts/generateDraft', async (importOriginal) => {
  const actual = await importOriginal<typeof import('@/api_contracts/generateDraft')>();
  return {
    ...actual,
    generateStoryDraft: vi.fn(),
  };
});

// Mock the verifier
vi.mock('@/verifiers/draftPreconditionsVerifier', async (importOriginal) => {
  const actual = await importOriginal<typeof import('@/verifiers/draftPreconditionsVerifier')>();
  return {
    ...actual,
    validateDraftPreconditions: vi.fn(actual.validateDraftPreconditions),
  };
});

// Mock the frontend logger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import DraftGeneratorButton from '../DraftGeneratorButton';
import { generateStoryDraft } from '@/api_contracts/generateDraft';
import { validateDraftPreconditions } from '@/verifiers/draftPreconditionsVerifier';

const mockGenerateStoryDraft = vi.mocked(generateStoryDraft);
const mockValidateDraftPreconditions = vi.mocked(validateDraftPreconditions);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validStoryRecordId = 'story-record-abc-123';

function createMockResponse(): GenerateStoryDraftResponse {
  return {
    storyRecordId: validStoryRecordId,
    content: 'First confirmed claim\n\nSecond confirmed claim',
    claimsUsed: ['c1', 'c2'],
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGeneratorButton — Step 1: Initiate draft generation (path 327)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    // Default: verifier passes
    mockValidateDraftPreconditions.mockReturnValue({ valid: true });
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render the Generate Draft button', () => {
      render(<DraftGeneratorButton storyRecordId={validStoryRecordId} />);
      expect(screen.getByRole('button', { name: /generate draft/i })).toBeInTheDocument();
    });

    it('should call generateStoryDraft on click when verifier passes', async () => {
      mockGenerateStoryDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftGeneratorButton storyRecordId={validStoryRecordId} />);
      const button = screen.getByRole('button', { name: /generate draft/i });

      await userEvent.click(button);

      await waitFor(() => {
        expect(mockGenerateStoryDraft).toHaveBeenCalledTimes(1);
      });
    });

    it('should call verifier before API call', async () => {
      mockGenerateStoryDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftGeneratorButton storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(mockValidateDraftPreconditions).toHaveBeenCalledBefore(
          mockGenerateStoryDraft,
        );
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should invoke API contract with typed GenerateStoryDraftRequest', async () => {
      mockGenerateStoryDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftGeneratorButton storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        const calledWith = mockGenerateStoryDraft.mock.calls[0][0];
        const parsed = GenerateStoryDraftContractRequestSchema.safeParse(calledWith);
        expect(parsed.success).toBe(true);
        if (parsed.success) {
          expect(parsed.data.storyRecordId).toBe(validStoryRecordId);
        }
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should NOT call API when verifier returns invalid', async () => {
      mockValidateDraftPreconditions.mockReturnValue({
        valid: false,
        message: 'storyRecordId: storyRecordId is required',
      });

      render(<DraftGeneratorButton storyRecordId="" />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(mockGenerateStoryDraft).not.toHaveBeenCalled();
      });
    });

    it('should render validation message when verifier returns invalid', async () => {
      mockValidateDraftPreconditions.mockReturnValue({
        valid: false,
        message: 'storyRecordId: storyRecordId is required',
      });

      render(<DraftGeneratorButton storyRecordId="" />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
        expect(screen.getByText(/storyRecordId/i)).toBeInTheDocument();
      });
    });

    it('should render error message when API call fails', async () => {
      mockGenerateStoryDraft.mockRejectedValueOnce(new Error('Server error'));

      render(<DraftGeneratorButton storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/server error/i)).toBeInTheDocument();
      });
    });

    it('should NOT render draft preview when API call fails', async () => {
      mockGenerateStoryDraft.mockRejectedValueOnce(new Error('Server error'));

      render(<DraftGeneratorButton storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/server error/i)).toBeInTheDocument();
      });
      expect(screen.queryByTestId('draft-preview')).not.toBeInTheDocument();
    });

    it('should show loading state during API call', async () => {
      let resolvePromise!: (value: GenerateStoryDraftResponse) => void;
      const pendingPromise = new Promise<GenerateStoryDraftResponse>((resolve) => {
        resolvePromise = resolve;
      });
      mockGenerateStoryDraft.mockReturnValueOnce(pendingPromise);

      render(<DraftGeneratorButton storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /generate draft/i })).toBeDisabled();
      });

      resolvePromise(createMockResponse());
    });
  });
});
