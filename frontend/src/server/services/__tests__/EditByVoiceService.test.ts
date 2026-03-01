/**
 * EditByVoiceService.test.ts - Step 3: Process voice instruction and generate revised content
 *
 * TLA+ Properties:
 * - Reachability: Provide existing Content + valid instruction → assert revised Content returned
 * - TypeInvariant: Assert returned object conforms to ContentEntity type
 * - ErrorConsistency: Provide semantically invalid instruction → INVALID_INSTRUCTION;
 *   assert DAO updateContent() not called
 *
 * Resource: db-h2s4 (service)
 * Path: 330-edit-content-by-voice-from-review-screen
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import { EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/ContentDAO', () => ({
  ContentDAO: {
    findById: vi.fn(),
    update: vi.fn(),
    updateContent: vi.fn(),
  },
}));

import { EditByVoiceService } from '../EditByVoiceService';
import { ContentDAO } from '../../data_access_objects/ContentDAO';

const mockDAO = vi.mocked(ContentDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const contentId = '550e8400-e29b-41d4-a716-446655440000';

const existingContent = {
  id: contentId,
  body: 'The original introduction text that needs improvement.',
  status: 'REVIEW' as const,
  workflowStage: 'REVIEW' as const,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

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

describe('EditByVoiceService — Step 3: Process voice instruction and generate revised content', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.findById.mockResolvedValue(existingContent);
    mockDAO.updateContent.mockResolvedValue(revisedContent);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return revised content when given valid content and instruction', async () => {
      const result = await EditByVoiceService.processInstruction(
        contentId,
        'Make the introduction more concise',
      );

      expect(mockDAO.findById).toHaveBeenCalledWith(contentId);
      expect(result).toBeDefined();
      expect(result.id).toBe(contentId);
    });

    it('should call DAO updateContent with the revised content', async () => {
      await EditByVoiceService.processInstruction(
        contentId,
        'Make the introduction more concise',
      );

      expect(mockDAO.updateContent).toHaveBeenCalledTimes(1);
      const updatedEntity = mockDAO.updateContent.mock.calls[0][0];
      expect(updatedEntity.id).toBe(contentId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return entity conforming to ContentEntity schema', async () => {
      const result = await EditByVoiceService.processInstruction(
        contentId,
        'Make the introduction more concise',
      );

      const parsed = ContentEntitySchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should preserve content status and workflowStage (remain REVIEW)', async () => {
      const result = await EditByVoiceService.processInstruction(
        contentId,
        'Make the introduction more concise',
      );

      expect(result.status).toBe('REVIEW');
      expect(result.workflowStage).toBe('REVIEW');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw CONTENT_NOT_FOUND when content does not exist', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await EditByVoiceService.processInstruction(contentId, 'Fix grammar');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(EditByVoiceError);
        expect((e as EditByVoiceError).code).toBe('CONTENT_NOT_FOUND');
        expect((e as EditByVoiceError).statusCode).toBe(404);
      }
    });

    it('should throw INVALID_INSTRUCTION for empty instruction', async () => {
      try {
        await EditByVoiceService.processInstruction(contentId, '');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(EditByVoiceError);
        expect((e as EditByVoiceError).code).toBe('INVALID_INSTRUCTION');
      }
    });

    it('should throw INVALID_INSTRUCTION for whitespace-only instruction', async () => {
      try {
        await EditByVoiceService.processInstruction(contentId, '   ');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(EditByVoiceError);
        expect((e as EditByVoiceError).code).toBe('INVALID_INSTRUCTION');
      }
    });

    it('should NOT call DAO updateContent when content not found', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await EditByVoiceService.processInstruction(contentId, 'Fix grammar');
      } catch {
        // expected
      }

      expect(mockDAO.updateContent).not.toHaveBeenCalled();
    });

    it('should NOT call DAO updateContent when instruction is invalid', async () => {
      try {
        await EditByVoiceService.processInstruction(contentId, '');
      } catch {
        // expected
      }

      expect(mockDAO.updateContent).not.toHaveBeenCalled();
    });
  });
});
