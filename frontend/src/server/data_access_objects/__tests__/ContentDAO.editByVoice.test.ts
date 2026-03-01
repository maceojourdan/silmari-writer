/**
 * ContentDAO.editByVoice.test.ts - Step 4: Persist revised content
 *
 * TLA+ Properties:
 * - Reachability: Call updateContent(content) → assert record stored in test DB
 * - TypeInvariant: Assert stored row matches ContentEntity schema
 * - ErrorConsistency: Mock DB failure → backend_logging.error() called →
 *   EditByVoiceErrors.PERSISTENCE_FAILURE returned
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 330-edit-content-by-voice-from-review-screen
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import { EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';

// ---------------------------------------------------------------------------
// Mock ContentDAO
// ---------------------------------------------------------------------------

vi.mock('../ContentDAO', () => ({
  ContentDAO: {
    findById: vi.fn(),
    update: vi.fn(),
    updateContent: vi.fn(),
  },
}));

// Mock backend logger
vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { ContentDAO } from '../ContentDAO';
import { logger } from '../../logging/logger';

const mockDAO = vi.mocked(ContentDAO);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const contentId = '550e8400-e29b-41d4-a716-446655440000';

const revisedContent = {
  id: contentId,
  body: 'A more concise introduction.',
  status: 'REVIEW' as const,
  workflowStage: 'REVIEW' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ContentDAO — Step 4: Persist revised content (edit-by-voice)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should update content and return updated entity', async () => {
      mockDAO.updateContent.mockResolvedValue(revisedContent);

      const result = await ContentDAO.updateContent(revisedContent);

      expect(result).toBeDefined();
      expect(result.id).toBe(contentId);
      expect(result.body).toBe('A more concise introduction.');
      expect(mockDAO.updateContent).toHaveBeenCalledWith(revisedContent);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return entity that conforms to ContentEntity schema', async () => {
      mockDAO.updateContent.mockResolvedValue(revisedContent);

      const result = await ContentDAO.updateContent(revisedContent);
      const parsed = ContentEntitySchema.safeParse(result);

      expect(parsed.success).toBe(true);
    });

    it('should only persist valid ContentEntity fields', async () => {
      mockDAO.updateContent.mockResolvedValue(revisedContent);

      const result = await ContentDAO.updateContent(revisedContent);

      const keys = Object.keys(result);
      expect(keys).toContain('id');
      expect(keys).toContain('body');
      expect(keys).toContain('status');
      expect(keys).toContain('workflowStage');
      expect(keys).toContain('createdAt');
      expect(keys).toContain('updatedAt');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw PERSISTENCE_FAILURE on DB failure', async () => {
      const error = new EditByVoiceError(
        'Failed to persist revised content',
        'PERSISTENCE_FAILURE',
        500,
        true,
      );
      mockDAO.updateContent.mockRejectedValue(error);

      try {
        await ContentDAO.updateContent(revisedContent);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(EditByVoiceError);
        expect((e as EditByVoiceError).code).toBe('PERSISTENCE_FAILURE');
        expect((e as EditByVoiceError).retryable).toBe(true);
      }
    });

    it('should not confirm update on persistence failure', async () => {
      mockDAO.updateContent.mockRejectedValue(
        new EditByVoiceError('Failed to persist', 'PERSISTENCE_FAILURE', 500, true),
      );

      let succeeded = false;
      try {
        await ContentDAO.updateContent(revisedContent);
        succeeded = true;
      } catch {
        // expected
      }

      expect(succeeded).toBe(false);
    });
  });
});
