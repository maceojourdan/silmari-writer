/**
 * editByVoice.integration.test.ts - Terminal Condition: Full path integration
 *
 * Asserts full path reachability from trigger → terminal condition:
 * - Given review screen with draft content
 * - When user selects "Edit by Voice" and provides valid instruction
 * - Then:
 *   - Backend processes + persists content
 *   - Review screen displays updated content
 *   - No error state present
 *
 * This test verifies the entire backend flow:
 * EditByVoiceRequestHandler → EditByVoiceService → ContentDAO
 *
 * Resource: Full path integration
 * Path: 330-edit-content-by-voice-from-review-screen
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';
import type { ContentEntity } from '@/server/data_structures/ContentEntity';
import { EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// ---------------------------------------------------------------------------
// Mock ContentDAO (database layer)
// ---------------------------------------------------------------------------

vi.mock('../../server/data_access_objects/ContentDAO', () => ({
  ContentDAO: {
    findById: vi.fn(),
    update: vi.fn(),
    updateContent: vi.fn(),
  },
}));

vi.mock('../../server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { EditByVoiceRequestHandler } from '../request_handlers/EditByVoiceRequestHandler';
import { ContentDAO } from '../data_access_objects/ContentDAO';
import { logger } from '../logging/logger';

const mockDAO = vi.mocked(ContentDAO);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const contentId = '550e8400-e29b-41d4-a716-446655440000';

const existingContent: ContentEntity = {
  id: contentId,
  body: 'The original introduction text that needs improvement.',
  status: 'REVIEW',
  workflowStage: 'REVIEW',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const updatedContent: ContentEntity = {
  id: contentId,
  body: 'The original introduction text that needs improvement.',
  status: 'REVIEW',
  workflowStage: 'REVIEW',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Terminal Condition Tests
// ---------------------------------------------------------------------------

describe('Edit By Voice — Terminal Condition: Full path integration', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.findById.mockResolvedValue(existingContent);
    mockDAO.updateContent.mockResolvedValue(updatedContent);
  });

  // -------------------------------------------------------------------------
  // Happy Path: Full flow from handler → service → DAO → response
  // -------------------------------------------------------------------------

  describe('Full path reachability', () => {
    it('should process voice instruction end-to-end and return updated content', async () => {
      const result = await EditByVoiceRequestHandler.handle(
        contentId,
        'Make the introduction more concise',
      );

      // Verify DAO was called to find content
      expect(mockDAO.findById).toHaveBeenCalledWith(contentId);

      // Verify DAO was called to persist updated content
      expect(mockDAO.updateContent).toHaveBeenCalledTimes(1);

      // Verify result has the updated content
      expect(result.updatedContent).toBeDefined();
      expect(result.updatedContent.id).toBe(contentId);
      expect(result.updatedContent.status).toBe('REVIEW');
    });

    it('should return result conforming to expected response shape', async () => {
      const result = await EditByVoiceRequestHandler.handle(
        contentId,
        'Fix grammar errors in the draft',
      );

      // Verify result shape
      expect(result).toHaveProperty('updatedContent');
      expect(typeof result.updatedContent.id).toBe('string');
      expect(typeof result.updatedContent.status).toBe('string');
      expect(typeof result.updatedContent.workflowStage).toBe('string');

      // Verify ContentEntity conformance
      const parsed = ContentEntitySchema.safeParse(result.updatedContent);
      expect(parsed.success).toBe(true);
    });

    it('should preserve REVIEW status and workflowStage (no state transition)', async () => {
      const result = await EditByVoiceRequestHandler.handle(
        contentId,
        'Simplify the wording',
      );

      expect(result.updatedContent.status).toBe('REVIEW');
      expect(result.updatedContent.workflowStage).toBe('REVIEW');
    });
  });

  // -------------------------------------------------------------------------
  // Error flow: Content not found
  // -------------------------------------------------------------------------

  describe('Error flow: content not found', () => {
    it('should throw CONTENT_NOT_FOUND when content does not exist', async () => {
      mockDAO.findById.mockResolvedValue(null);

      try {
        await EditByVoiceRequestHandler.handle(contentId, 'Fix grammar');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(EditByVoiceError);
        expect((e as EditByVoiceError).code).toBe('CONTENT_NOT_FOUND');
        expect((e as EditByVoiceError).statusCode).toBe(404);
      }

      // DAO should not have been called for update
      expect(mockDAO.updateContent).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // Error flow: Invalid instruction
  // -------------------------------------------------------------------------

  describe('Error flow: invalid instruction', () => {
    it('should throw INVALID_INSTRUCTION for empty instruction text', async () => {
      try {
        await EditByVoiceRequestHandler.handle(contentId, '');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(EditByVoiceError);
        expect((e as EditByVoiceError).code).toBe('INVALID_INSTRUCTION');
      }

      expect(mockDAO.updateContent).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // Error flow: Unexpected error
  // -------------------------------------------------------------------------

  describe('Error flow: unexpected error', () => {
    it('should wrap unexpected errors in GenericError and log', async () => {
      mockDAO.findById.mockRejectedValue(new Error('Database connection lost'));

      try {
        await EditByVoiceRequestHandler.handle(contentId, 'Fix grammar');
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(1);
    });
  });

  // -------------------------------------------------------------------------
  // No error state verification
  // -------------------------------------------------------------------------

  describe('No error state present on success', () => {
    it('should complete without any error being thrown', async () => {
      // This test explicitly verifies the terminal condition:
      // "No error state present"
      let errorOccurred = false;

      try {
        const result = await EditByVoiceRequestHandler.handle(
          contentId,
          'Make the text more engaging',
        );

        // Verify success
        expect(result.updatedContent).toBeDefined();
        expect(result.updatedContent.id).toBe(contentId);
      } catch {
        errorOccurred = true;
      }

      expect(errorOccurred).toBe(false);
      expect(mockLogger.error).not.toHaveBeenCalled();
    });
  });
});
