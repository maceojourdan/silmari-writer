/**
 * Tests for DraftGenerator — Step 1: Initiate draft generation request
 *
 * Resource: ui-w8p2 (component)
 * Path: 326-generate-draft-with-only-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Render with valid caseId → click → generateCaseDraft(caseId) called
 * - TypeInvariant: generateCaseDraft is called with { caseId: string }
 * - ErrorConsistency: Contract rejects → frontend/logging.error called, error message rendered, no draft rendered
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import type { GenerateCaseDraftResponse } from '@/server/data_structures/Claim';
import { GenerateCaseDraftContractRequestSchema } from '@/api_contracts/generateDraft';

// Mock the generateCaseDraft API contract
vi.mock('@/api_contracts/generateDraft', async (importOriginal) => {
  const actual = await importOriginal<typeof import('@/api_contracts/generateDraft')>();
  return {
    ...actual,
    generateCaseDraft: vi.fn(),
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

import DraftGenerator from '../DraftGenerator';
import { generateCaseDraft } from '@/api_contracts/generateDraft';
import { frontendLogger } from '@/logging/index';

const mockGenerateCaseDraft = vi.mocked(generateCaseDraft);
const mockLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validCaseId = 'case-abc-123';

function createMockResponse(): GenerateCaseDraftResponse {
  return {
    caseId: validCaseId,
    content: 'First confirmed claim\n\nSecond confirmed claim',
    claimsUsed: ['c1', 'c2'],
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerator — Step 1: Initiate draft generation (path 326)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render the Generate Draft button', () => {
      render(<DraftGenerator caseId={validCaseId} />);
      expect(screen.getByRole('button', { name: /generate draft/i })).toBeInTheDocument();
    });

    it('should call generateCaseDraft with caseId on click', async () => {
      mockGenerateCaseDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftGenerator caseId={validCaseId} />);
      const button = screen.getByRole('button', { name: /generate draft/i });

      await userEvent.click(button);

      await waitFor(() => {
        expect(mockGenerateCaseDraft).toHaveBeenCalledTimes(1);
        expect(mockGenerateCaseDraft).toHaveBeenCalledWith({
          caseId: validCaseId,
        });
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload conforming to GenerateCaseDraftContractRequest schema', async () => {
      mockGenerateCaseDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        const calledWith = mockGenerateCaseDraft.mock.calls[0][0];
        const parsed = GenerateCaseDraftContractRequestSchema.safeParse(calledWith);
        expect(parsed.success).toBe(true);
        if (parsed.success) {
          expect(parsed.data.caseId).toBe(validCaseId);
        }
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should call frontendLogger.error when contract rejects', async () => {
      mockGenerateCaseDraft.mockRejectedValueOnce(new Error('Server error'));

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(mockLogger.error).toHaveBeenCalled();
      });
    });

    it('should render error message when contract rejects', async () => {
      mockGenerateCaseDraft.mockRejectedValueOnce(new Error('Server error'));

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/server error/i)).toBeInTheDocument();
      });
    });

    it('should NOT render draft when contract rejects', async () => {
      mockGenerateCaseDraft.mockRejectedValueOnce(new Error('Server error'));

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/server error/i)).toBeInTheDocument();
      });
      expect(screen.queryByTestId('draft-content')).not.toBeInTheDocument();
    });

    it('should show loading state during API call', async () => {
      let resolvePromise!: (value: GenerateCaseDraftResponse) => void;
      const pendingPromise = new Promise<GenerateCaseDraftResponse>((resolve) => {
        resolvePromise = resolve;
      });
      mockGenerateCaseDraft.mockReturnValueOnce(pendingPromise);

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /generate draft/i })).toBeDisabled();
      });

      resolvePromise(createMockResponse());
    });
  });
});
