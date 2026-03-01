/**
 * Tests for DraftGenerator — Step 6: Return and display structured draft
 *
 * Resource: ui-w8p2 (component)
 * Path: 326-generate-draft-with-only-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Mock API returns draft → draft content rendered
 * - TypeInvariant: Rendered claims match claimsUsed
 * - ErrorConsistency: Force render error → frontendLogger.error called, fallback message shown
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import type { GenerateCaseDraftResponse } from '@/server/data_structures/Claim';

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

function createMockResponse(overrides: Partial<GenerateCaseDraftResponse> = {}): GenerateCaseDraftResponse {
  return {
    caseId: validCaseId,
    content: 'First confirmed claim\n\nSecond confirmed claim',
    claimsUsed: ['c1', 'c2'],
    ...overrides,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftGenerator — Step 6: Return and display draft (path 326)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render draft content after successful API call', async () => {
      mockGenerateCaseDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByTestId('draft-content')).toBeInTheDocument();
        expect(screen.getByText(/First confirmed claim/)).toBeInTheDocument();
        expect(screen.getByText(/Second confirmed claim/)).toBeInTheDocument();
      });
    });

    it('should show Generated Draft heading', async () => {
      mockGenerateCaseDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText('Generated Draft')).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should display claims used from response', async () => {
      const response = createMockResponse({
        claimsUsed: ['claim-1', 'claim-2', 'claim-3'],
      });
      mockGenerateCaseDraft.mockResolvedValueOnce(response);

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/claim-1/)).toBeInTheDocument();
        expect(screen.getByText(/claim-2/)).toBeInTheDocument();
        expect(screen.getByText(/claim-3/)).toBeInTheDocument();
      });
    });

    it('should call onSuccess callback with response', async () => {
      const response = createMockResponse();
      mockGenerateCaseDraft.mockResolvedValueOnce(response);

      const onSuccess = vi.fn();
      render(<DraftGenerator caseId={validCaseId} onSuccess={onSuccess} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(onSuccess).toHaveBeenCalledWith(response);
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log error and show fallback message when API fails', async () => {
      mockGenerateCaseDraft.mockRejectedValueOnce(new Error('Rendering issue'));

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(mockLogger.error).toHaveBeenCalledWith(
          'Draft generation failed',
          expect.any(Error),
          expect.objectContaining({ component: 'DraftGenerator' }),
        );
        expect(screen.getByRole('alert')).toBeInTheDocument();
        expect(screen.getByText(/rendering issue/i)).toBeInTheDocument();
      });
    });

    it('should not show draft content when error occurs', async () => {
      mockGenerateCaseDraft.mockRejectedValueOnce(new Error('API failure'));

      render(<DraftGenerator caseId={validCaseId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });
      expect(screen.queryByTestId('draft-content')).not.toBeInTheDocument();
    });
  });
});
