/**
 * GenerateDraft.integration.test.tsx - Frontend integration test
 *
 * Verifies the full frontend flow:
 * - Mock successful API response
 * - Click button
 * - Await draft render
 * - Assert UI shows only confirmed claims
 *
 * Resource: ui-w8p2 (component)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

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

/**
 * Creates a response with confirmed claims across all sections,
 * simulating what the server would return after filtering.
 */
function createFullResponse() {
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
              content: 'Led a cross-functional team of 8 engineers',
              status: 'CONFIRMED' as const,
              section: 'context' as const,
              order: 0,
              createdAt: now,
              updatedAt: now,
            },
            {
              id: crypto.randomUUID(),
              claimSetId: validClaimSetId,
              content: 'Project was in fintech domain with strict compliance',
              status: 'CONFIRMED' as const,
              section: 'context' as const,
              order: 1,
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
              content: 'Implemented automated testing pipeline reducing bugs by 40%',
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
              content: 'Delivered project 2 weeks ahead of schedule',
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
// Integration Test
// ---------------------------------------------------------------------------

describe('GenerateDraft Integration — Terminal Condition (Frontend)', () => {
  beforeEach(() => {
    mockGenerateDraft.mockReset();
  });

  it('should render structured draft with only confirmed claims after clicking Generate Draft', async () => {
    const response = createFullResponse();
    mockGenerateDraft.mockResolvedValueOnce(response);

    render(<GenerateDraftButton claimSetId={validClaimSetId} />);

    // Click the button
    await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

    // Wait for draft preview to render
    await waitFor(() => {
      expect(screen.getByTestId('draft-preview')).toBeInTheDocument();
    });

    // Assert all sections are rendered
    expect(screen.getByText('context')).toBeInTheDocument();
    expect(screen.getByText('actions')).toBeInTheDocument();
    expect(screen.getByText('outcome')).toBeInTheDocument();

    // Assert all confirmed claim contents are displayed
    expect(screen.getByText('Led a cross-functional team of 8 engineers')).toBeInTheDocument();
    expect(screen.getByText('Project was in fintech domain with strict compliance')).toBeInTheDocument();
    expect(screen.getByText('Implemented automated testing pipeline reducing bugs by 40%')).toBeInTheDocument();
    expect(screen.getByText('Delivered project 2 weeks ahead of schedule')).toBeInTheDocument();
  });

  it('should display sections in the correct order matching DraftDocumentStructure', async () => {
    const response = createFullResponse();
    mockGenerateDraft.mockResolvedValueOnce(response);

    render(<GenerateDraftButton claimSetId={validClaimSetId} />);
    await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

    await waitFor(() => {
      expect(screen.getByTestId('draft-preview')).toBeInTheDocument();
    });

    // Verify section order: context → actions → outcome
    const sectionHeaders = screen.getAllByRole('heading', { level: 4 });
    expect(sectionHeaders[0].textContent).toBe('context');
    expect(sectionHeaders[1].textContent).toBe('actions');
    expect(sectionHeaders[2].textContent).toBe('outcome');
  });

  it('should call API with correct claimSetId and handle the full lifecycle', async () => {
    const response = createFullResponse();
    mockGenerateDraft.mockResolvedValueOnce(response);
    const onSuccess = vi.fn();

    render(<GenerateDraftButton claimSetId={validClaimSetId} onSuccess={onSuccess} />);

    // Initial state: button visible
    const button = screen.getByRole('button', { name: /generate draft/i });
    expect(button).toBeEnabled();

    // Click and wait for response
    await userEvent.click(button);

    // Verify API was called correctly
    expect(mockGenerateDraft).toHaveBeenCalledWith({ claimSetId: validClaimSetId });

    // Verify onSuccess callback
    await waitFor(() => {
      expect(onSuccess).toHaveBeenCalledWith(response);
    });

    // Verify draft preview replaces button
    expect(screen.getByTestId('draft-preview')).toBeInTheDocument();
    expect(screen.queryByRole('button', { name: /generate draft/i })).not.toBeInTheDocument();
  });

  it('should handle error gracefully and remain in button state', async () => {
    mockGenerateDraft.mockRejectedValueOnce(new Error('No confirmed claims found'));

    render(<GenerateDraftButton claimSetId={validClaimSetId} />);
    await userEvent.click(screen.getByRole('button', { name: /generate draft/i }));

    // Error message should appear
    await waitFor(() => {
      expect(screen.getByText(/no confirmed claims found/i)).toBeInTheDocument();
    });

    // Button should still be visible for retry
    expect(screen.getByRole('button', { name: /generate draft/i })).toBeInTheDocument();
    expect(screen.queryByTestId('draft-preview')).not.toBeInTheDocument();
  });
});
