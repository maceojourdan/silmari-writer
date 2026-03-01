/**
 * Tests for DraftModule — Step 5: Display no confirmed claims message
 *
 * Resource: ui-v3n6 (module)
 * Path: 327-prevent-draft-generation-without-confirmed-claims
 *
 * TLA+ properties tested:
 * - Reachability: Mock API returning NO_CONFIRMED_CLAIMS → message rendered, no draft content
 * - TypeInvariant: Error response matches shared ErrorResponse type
 * - ErrorConsistency: Malformed error → fallback generic notification displayed
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import type { GenerateStoryDraftResponse } from '@/server/data_structures/Claim';

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

import { DraftModule } from '../DraftModule';
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

describe('DraftModule — Step 5: Display no confirmed claims message (path 327)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockValidateDraftPreconditions.mockReturnValue({ valid: true });
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render the module with Generate Draft button', () => {
      render(<DraftModule storyRecordId={validStoryRecordId} />);
      expect(screen.getByTestId('draft-module')).toBeInTheDocument();
      expect(screen.getByRole('button', { name: /generate draft/i })).toBeInTheDocument();
    });

    it('should display NO_CONFIRMED_CLAIMS message when API returns that error', async () => {
      const error = new Error('No confirmed claims are available.');
      (error as any).code = 'NO_CONFIRMED_CLAIMS';
      mockGenerateStoryDraft.mockRejectedValueOnce(error);

      render(<DraftModule storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/no confirmed claims/i)).toBeInTheDocument();
      });
    });

    it('should NOT render any draft content when NO_CONFIRMED_CLAIMS', async () => {
      const error = new Error('No confirmed claims are available.');
      (error as any).code = 'NO_CONFIRMED_CLAIMS';
      mockGenerateStoryDraft.mockRejectedValueOnce(error);

      render(<DraftModule storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByText(/no confirmed claims/i)).toBeInTheDocument();
      });
      expect(screen.queryByTestId('draft-content')).not.toBeInTheDocument();
    });

    it('should render draft content when API succeeds', async () => {
      mockGenerateStoryDraft.mockResolvedValueOnce(createMockResponse());

      render(<DraftModule storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByTestId('draft-content')).toBeInTheDocument();
      });
      expect(screen.getByText(/First confirmed claim/)).toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should display structured error notification for NO_CONFIRMED_CLAIMS', async () => {
      const error = new Error('No confirmed claims are available.');
      (error as any).code = 'NO_CONFIRMED_CLAIMS';
      mockGenerateStoryDraft.mockRejectedValueOnce(error);

      render(<DraftModule storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        const errorNotification = screen.getByTestId('error-notification');
        expect(errorNotification).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display generic error notification for unknown errors', async () => {
      mockGenerateStoryDraft.mockRejectedValueOnce(new Error('Something unexpected'));

      render(<DraftModule storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByTestId('error-notification')).toBeInTheDocument();
      });
    });

    it('should display fallback for non-Error thrown values', async () => {
      mockGenerateStoryDraft.mockRejectedValueOnce('string error');

      render(<DraftModule storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByTestId('error-notification')).toBeInTheDocument();
        expect(screen.getByText(/an unexpected error occurred/i)).toBeInTheDocument();
      });
    });

    it('should clear error state when draft generation succeeds after failure', async () => {
      // First click: failure
      const error = new Error('No confirmed claims are available.');
      (error as any).code = 'NO_CONFIRMED_CLAIMS';
      mockGenerateStoryDraft.mockRejectedValueOnce(error);

      render(<DraftModule storyRecordId={validStoryRecordId} />);
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.getByTestId('error-notification')).toBeInTheDocument();
      });

      // Second click: success
      mockGenerateStoryDraft.mockResolvedValueOnce(createMockResponse());
      await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

      await waitFor(() => {
        expect(screen.queryByTestId('error-notification')).not.toBeInTheDocument();
        expect(screen.getByTestId('draft-content')).toBeInTheDocument();
      });
    });
  });
});
