/**
 * Tests for StorySelection - Step 4: Render validation feedback to user
 *
 * Path: 314-prevent-confirmation-of-misaligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Misaligned state → error banner rendered, user remains on page
 * - TypeInvariant: Banner receives message as string
 * - ErrorConsistency (render failure): Banner render error → logError() called, fallback banner rendered
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock AlignmentVerifier
vi.mock('@/verifiers/AlignmentVerifier', () => ({
  AlignmentVerifier: {
    validate: vi.fn(),
  },
}));

// Mock frontendLogger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock fetch
const mockFetch = vi.fn();

import { StorySelection } from '../StorySelection';
import { AlignmentVerifier } from '@/verifiers/AlignmentVerifier';
import { frontendLogger } from '@/logging/index';
import { AlignmentErrors } from '@/server/error_definitions/AlignmentErrors';
import type { Story } from '@/server/data_structures/ConfirmStory';

const mockValidate = vi.mocked(AlignmentVerifier.validate);
const mockLogError = vi.mocked(frontendLogger.error);

const testStories: Story[] = [
  {
    id: 'story-001',
    title: 'Led migration to microservices architecture',
    summary: 'Coordinated 4 teams to decompose a monolithic application.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
  {
    id: 'story-002',
    title: 'Built real-time analytics pipeline',
    summary: 'Designed streaming data pipeline processing 1M events per second.',
    status: 'AVAILABLE',
    questionId: 'q-001',
  },
];

describe('StorySelection - Step 4: Render validation feedback to user', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
    mockValidate.mockReset();
    mockLogError.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render alignment error banner when misaligned', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'STORY_MISALIGNED',
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        const banner = screen.getByTestId('alignment-error');
        expect(banner).toBeInTheDocument();
        expect(banner).toHaveAttribute('role', 'alert');
      });
    });

    it('should keep user on the selection screen after misalignment', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'STORY_MISALIGNED',
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        // Error banner shown
        expect(screen.getByTestId('alignment-error')).toBeInTheDocument();
      });

      // User remains on selection screen - stories and confirm button still visible
      expect(screen.getByTestId('story-selection')).toBeInTheDocument();
      expect(screen.getByTestId('confirm-button')).toBeInTheDocument();
      expect(screen.getByLabelText('Led migration to microservices architecture')).toBeInTheDocument();
    });

    it('should display ALIGNMENT_RULES_UNAVAILABLE message when rules are null', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'ALIGNMENT_RULES_UNAVAILABLE',
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        expect(screen.getByText(AlignmentErrors.ALIGNMENT_RULES_UNAVAILABLE)).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should render banner with message as a non-empty string', async () => {
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'STORY_MISALIGNED',
      });

      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        const banner = screen.getByTestId('alignment-error');
        expect(typeof banner.textContent).toBe('string');
        expect(banner.textContent!.length).toBeGreaterThan(0);
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency (render failure)
  // -------------------------------------------------------------------------

  describe('ErrorConsistency (render failure)', () => {
    it('should log error and render fallback banner when AlignmentErrorBanner fails to render', async () => {
      // Force the alignment error banner to throw during render by providing
      // a specially crafted message that triggers the error boundary
      mockValidate.mockReturnValue({
        status: 'misaligned',
        messageKey: 'STORY_MISALIGNED',
      });

      // We'll render with renderError=true to trigger the error boundary path
      render(
        <StorySelection
          stories={testStories}
          questionId="q-001"
          jobId="job-001"
          onConfirmed={vi.fn()}
          _testForceRenderError={true}
        />,
      );

      await userEvent.click(screen.getByLabelText('Led migration to microservices architecture'));
      await userEvent.click(screen.getByTestId('confirm-button'));

      await waitFor(() => {
        // Fallback banner should be rendered
        expect(screen.getByTestId('alignment-error-fallback')).toBeInTheDocument();
        expect(
          screen.getByText('An error occurred while displaying validation feedback.'),
        ).toBeInTheDocument();
      });

      // Logger should have been called
      expect(mockLogError).toHaveBeenCalled();
    });
  });
});
