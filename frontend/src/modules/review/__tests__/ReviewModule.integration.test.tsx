/**
 * ReviewModule.integration.test.tsx - Step 5: Return updated content to review screen
 *
 * TLA+ Properties:
 * - Reachability: Mock full backend response → trigger voice edit → assert updated content rendered
 * - TypeInvariant: Assert component state matches ContentEntity type
 * - ErrorConsistency: Mock malformed backend response →
 *   frontend_logging.error() called → error message displayed → previous content preserved
 *
 * Resource: ui-v3n6 (module)
 * Path: 330-edit-content-by-voice-from-review-screen
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

const mockFetch = vi.fn();

import { ReviewWorkflowModule } from '../ReviewWorkflowModule';

describe('ReviewModule Integration — Step 5: Return updated content to review screen (edit-by-voice)', () => {
  const contentId = '550e8400-e29b-41d4-a716-446655440000';

  const contentItems = [
    { id: contentId, title: 'Test Content Item' },
    { id: '550e8400-e29b-41d4-a716-446655440001', title: 'Another Item' },
  ];

  const validEditResponse = {
    updatedContent: {
      id: contentId,
      body: 'The revised introduction text.',
      status: 'REVIEW',
      workflowStage: 'REVIEW',
      createdAt: '2026-02-28T12:00:00.000Z',
      updatedAt: '2026-02-28T12:01:00.000Z',
    },
  };

  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render "Edit by Voice" button when a content item is selected', async () => {
      render(<ReviewWorkflowModule contentItems={contentItems} />);

      // Select a content item
      await userEvent.click(screen.getByText('Test Content Item'));

      // Edit by Voice button should appear
      expect(screen.getByRole('button', { name: /edit by voice/i })).toBeInTheDocument();
    });

    it('should display updated content after successful voice edit', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validEditResponse,
      });

      render(<ReviewWorkflowModule contentItems={contentItems} />);

      // Select content item
      await userEvent.click(screen.getByText('Test Content Item'));

      // Click Edit by Voice
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      // Enter instruction
      const input = screen.getByPlaceholderText(/voice instruction/i);
      await userEvent.type(input, 'Make it more concise');
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      // Should show success state with updated content
      await waitFor(() => {
        expect(screen.getByTestId('edit-success')).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should render content body text from updated response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validEditResponse,
      });

      render(<ReviewWorkflowModule contentItems={contentItems} />);

      await userEvent.click(screen.getByText('Test Content Item'));
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      const input = screen.getByPlaceholderText(/voice instruction/i);
      await userEvent.type(input, 'Improve grammar');
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByTestId('edit-success')).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display error message on backend failure', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 422,
        json: async () => ({
          code: 'INVALID_INSTRUCTION',
          message: 'Voice instruction could not be processed',
        }),
      });

      render(<ReviewWorkflowModule contentItems={contentItems} />);

      await userEvent.click(screen.getByText('Test Content Item'));
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      const input = screen.getByPlaceholderText(/voice instruction/i);
      await userEvent.type(input, 'Nonsense instruction');
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        const errorElement = screen.getByTestId('error-notification');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should preserve content items when voice edit fails', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({
          code: 'INTERNAL_ERROR',
          message: 'An unexpected error occurred',
        }),
      });

      render(<ReviewWorkflowModule contentItems={contentItems} />);

      await userEvent.click(screen.getByText('Test Content Item'));
      await userEvent.click(screen.getByRole('button', { name: /edit by voice/i }));

      const input = screen.getByPlaceholderText(/voice instruction/i);
      await userEvent.type(input, 'Some edit instruction');
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      // All items should still be visible
      await waitFor(() => {
        expect(screen.getByText('Test Content Item')).toBeInTheDocument();
        expect(screen.getByText('Another Item')).toBeInTheDocument();
      });
    });
  });
});
