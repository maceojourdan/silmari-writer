/**
 * Tests for OrientStoryModule - Step 1: Render question requirements and stories
 *
 * Path: 313-confirm-aligned-story-selection
 *
 * TLA+ properties tested:
 * - Reachability: Mock loadOrientStoryData → render → assert UI visible
 * - TypeInvariant: Returned data satisfies OrientStoryDataSchema
 * - ErrorConsistency: Loader failure → error UI with retry button
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the data loader
vi.mock('@/data_loaders/loadOrientStoryData', () => ({
  loadOrientStoryData: vi.fn(),
}));

import { OrientStoryModule } from '../OrientStoryModule';
import { loadOrientStoryData } from '@/data_loaders/loadOrientStoryData';
import { OrientStoryDataSchema } from '@/server/data_structures/ConfirmStory';
import { ConfirmStoryError } from '@/server/error_definitions/ConfirmStoryErrors';

const mockLoader = vi.mocked(loadOrientStoryData);

describe('OrientStoryModule - Step 1: Render question requirements and stories', () => {
  const validData = {
    question: {
      id: 'q-001',
      text: 'Tell me about a time you led a cross-functional team to deliver a complex project.',
      category: 'leadership',
    },
    jobRequirements: [
      {
        id: 'jr-001',
        description: 'Experience leading cross-functional teams',
        priority: 'REQUIRED' as const,
      },
      {
        id: 'jr-002',
        description: 'Track record of delivering complex projects on time',
        priority: 'PREFERRED' as const,
      },
    ],
    stories: [
      {
        id: 'story-001',
        title: 'Led migration to microservices architecture',
        summary: 'Coordinated 4 teams across engineering, QA, and DevOps to decompose a monolithic application.',
        status: 'AVAILABLE' as const,
        questionId: 'q-001',
      },
      {
        id: 'story-002',
        title: 'Built real-time analytics pipeline',
        summary: 'Designed and implemented a streaming data pipeline processing 1M events per second.',
        status: 'AVAILABLE' as const,
        questionId: 'q-001',
      },
      {
        id: 'story-003',
        title: 'Established engineering hiring process',
        summary: 'Created structured interview process across 3 departments.',
        status: 'AVAILABLE' as const,
        questionId: 'q-001',
      },
    ],
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: Render question, job requirements, and stories', () => {
    it('should display the question text when data loads successfully', async () => {
      mockLoader.mockResolvedValue(validData);

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByText(/Tell me about a time you led a cross-functional team/i)).toBeInTheDocument();
      });
    });

    it('should display all stories in a selectable list', async () => {
      mockLoader.mockResolvedValue(validData);

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByText('Led migration to microservices architecture')).toBeInTheDocument();
        expect(screen.getByText('Built real-time analytics pipeline')).toBeInTheDocument();
        expect(screen.getByText('Established engineering hiring process')).toBeInTheDocument();
      });
    });

    it('should display job requirements', async () => {
      mockLoader.mockResolvedValue(validData);

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByText(/Experience leading cross-functional teams/i)).toBeInTheDocument();
        expect(screen.getByText(/Track record of delivering complex projects/i)).toBeInTheDocument();
      });
    });

    it('should call loadOrientStoryData with the questionId', async () => {
      mockLoader.mockResolvedValue(validData);

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(mockLoader).toHaveBeenCalledWith('q-001');
      });
    });
  });

  describe('TypeInvariant: Returned data satisfies OrientStoryDataSchema', () => {
    it('should produce data conforming to OrientStoryDataSchema', async () => {
      mockLoader.mockResolvedValue(validData);

      const parsed = OrientStoryDataSchema.safeParse(validData);
      expect(parsed.success).toBe(true);
    });

    it('should reject data missing question text', () => {
      const invalidData = {
        ...validData,
        question: { id: 'q-001', text: '' },
      };

      const parsed = OrientStoryDataSchema.safeParse(invalidData);
      expect(parsed.success).toBe(false);
    });

    it('should reject data with empty stories array', () => {
      const invalidData = {
        ...validData,
        stories: [],
      };

      const parsed = OrientStoryDataSchema.safeParse(invalidData);
      expect(parsed.success).toBe(false);
    });

    it('should reject data with empty job requirements', () => {
      const invalidData = {
        ...validData,
        jobRequirements: [],
      };

      const parsed = OrientStoryDataSchema.safeParse(invalidData);
      expect(parsed.success).toBe(false);
    });
  });

  describe('ErrorConsistency: Loader failure → error UI with retry', () => {
    it('should display error UI when loader throws DATA_NOT_FOUND', async () => {
      mockLoader.mockRejectedValue(
        new ConfirmStoryError('Data not found', 'DATA_NOT_FOUND', 404, true),
      );

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });
    });

    it('should display a retry button on error', async () => {
      mockLoader.mockRejectedValue(
        new ConfirmStoryError('Data not found', 'DATA_NOT_FOUND', 404, true),
      );

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /retry/i })).toBeInTheDocument();
      });
    });

    it('should retry loading when retry button is clicked', async () => {
      mockLoader
        .mockRejectedValueOnce(new ConfirmStoryError('Data not found', 'DATA_NOT_FOUND', 404, true))
        .mockResolvedValueOnce(validData);

      render(<OrientStoryModule questionId="q-001" />);

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /retry/i })).toBeInTheDocument();
      });

      await userEvent.click(screen.getByRole('button', { name: /retry/i }));

      await waitFor(() => {
        expect(screen.getByText(/Tell me about a time you led a cross-functional team/i)).toBeInTheDocument();
      });

      expect(mockLoader).toHaveBeenCalledTimes(2);
    });

    it('should display loading state while fetching data', async () => {
      mockLoader.mockImplementation(() => new Promise(() => {})); // never resolves

      render(<OrientStoryModule questionId="q-001" />);

      expect(screen.getByText(/loading/i)).toBeInTheDocument();
    });
  });
});
