/**
 * EditByVoiceRequestHandler.test.ts - Request handler for edit-by-voice
 *
 * TLA+ Properties:
 * - Reachability: Valid contentId + instructionText → service processes → returns updated content
 * - TypeInvariant: Result matches expected shape { updatedContent: ContentEntity }
 * - ErrorConsistency: Known errors (EditByVoiceError) rethrown;
 *   unknown errors logged + wrapped in GenericErrors.InternalError
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 330-edit-content-by-voice-from-review-screen
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';
import { GenericError } from '@/server/error_definitions/GenericErrors';

// ---------------------------------------------------------------------------
// Mock dependencies
// ---------------------------------------------------------------------------

vi.mock('../../services/EditByVoiceService', () => ({
  EditByVoiceService: {
    processInstruction: vi.fn(),
  },
}));

vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { EditByVoiceRequestHandler } from '../EditByVoiceRequestHandler';
import { EditByVoiceService } from '../../services/EditByVoiceService';
import { logger } from '../../logging/logger';

const mockService = vi.mocked(EditByVoiceService);
const mockLogger = vi.mocked(logger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const contentId = '550e8400-e29b-41d4-a716-446655440000';
const instructionText = 'Make the introduction more concise';

const updatedContent = {
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

describe('EditByVoiceRequestHandler — Step 5: Request handler', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockService.processInstruction.mockResolvedValue(updatedContent);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should delegate to EditByVoiceService and return updated content', async () => {
      const result = await EditByVoiceRequestHandler.handle(contentId, instructionText);

      expect(mockService.processInstruction).toHaveBeenCalledWith(contentId, instructionText);
      expect(result.updatedContent).toBeDefined();
      expect(result.updatedContent.id).toBe(contentId);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result with updatedContent matching ContentEntity', async () => {
      const result = await EditByVoiceRequestHandler.handle(contentId, instructionText);

      expect(result.updatedContent.id).toBe(contentId);
      expect(result.updatedContent.status).toBe('REVIEW');
      expect(result.updatedContent.workflowStage).toBe('REVIEW');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should rethrow known EditByVoiceError errors', async () => {
      const error = new EditByVoiceError('Content not found', 'CONTENT_NOT_FOUND', 404, false);
      mockService.processInstruction.mockRejectedValue(error);

      try {
        await EditByVoiceRequestHandler.handle(contentId, instructionText);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(EditByVoiceError);
        expect((e as EditByVoiceError).code).toBe('CONTENT_NOT_FOUND');
      }
    });

    it('should log and wrap unknown errors in GenericErrors.InternalError', async () => {
      mockService.processInstruction.mockRejectedValue(new Error('Unexpected DB issue'));

      try {
        await EditByVoiceRequestHandler.handle(contentId, instructionText);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }

      expect(mockLogger.error).toHaveBeenCalledTimes(1);
    });
  });
});
