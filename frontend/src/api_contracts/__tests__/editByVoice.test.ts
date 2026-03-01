/**
 * editByVoice.test.ts - Step 2: Send voice edit request to backend
 *
 * TLA+ Properties:
 * - Reachability: Call editByVoice(payload) with valid payload → assert fetch called with /api/edit-by-voice
 * - TypeInvariant: Validate payload via Zod schema before submission;
 *   assert response type { updatedContent: ContentEntity }
 * - ErrorConsistency: Mock network failure → SharedErrors.NETWORK_ERROR;
 *   assert UI state preserves original content
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 330-edit-content-by-voice-from-review-screen
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { ContentEntitySchema } from '@/server/data_structures/ContentEntity';

const mockFetch = vi.fn();

import {
  editByVoice,
  EditByVoiceRequestSchema,
  EditByVoiceResponseSchema,
} from '../editByVoice';

describe('editByVoice API contract — Step 2: Send voice edit request to backend', () => {
  const contentId = '550e8400-e29b-41d4-a716-446655440000';
  const instructionText = 'Make the introduction more concise';

  const validResponse = {
    updatedContent: {
      id: contentId,
      body: 'The revised introduction text.',
      status: 'REVIEW' as const,
      workflowStage: 'REVIEW' as const,
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
    it('should call fetch with /api/edit-by-voice when given valid payload', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      await editByVoice({ contentId, instructionText });

      expect(mockFetch).toHaveBeenCalledTimes(1);
      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe('/api/edit-by-voice');
      expect(options.method).toBe('POST');
    });

    it('should send contentId and instructionText in request body', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      await editByVoice({ contentId, instructionText });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      expect(body.contentId).toBe(contentId);
      expect(body.instructionText).toBe(instructionText);
    });

    it('should return parsed response with updatedContent', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      const result = await editByVoice({ contentId, instructionText });

      expect(result.updatedContent).toBeDefined();
      expect(result.updatedContent.id).toBe(contentId);
      expect(result.updatedContent.body).toBe('The revised introduction text.');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate request payload via Zod schema', () => {
      const validPayload = { contentId, instructionText };
      const parsed = EditByVoiceRequestSchema.safeParse(validPayload);

      expect(parsed.success).toBe(true);
    });

    it('should reject payload with missing contentId', () => {
      const invalidPayload = { instructionText };
      const parsed = EditByVoiceRequestSchema.safeParse(invalidPayload);

      expect(parsed.success).toBe(false);
    });

    it('should reject payload with empty instructionText', () => {
      const invalidPayload = { contentId, instructionText: '' };
      const parsed = EditByVoiceRequestSchema.safeParse(invalidPayload);

      expect(parsed.success).toBe(false);
    });

    it('should validate response matches EditByVoiceResponse schema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      const result = await editByVoice({ contentId, instructionText });

      const parsed = EditByVoiceResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return updatedContent conforming to ContentEntity schema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      const result = await editByVoice({ contentId, instructionText });

      const parsed = ContentEntitySchema.safeParse(result.updatedContent);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw on network failure', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      await expect(
        editByVoice({ contentId, instructionText }),
      ).rejects.toThrow('Network error');
    });

    it('should throw on non-ok HTTP response with error code', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 422,
        json: async () => ({
          code: 'INVALID_INSTRUCTION',
          message: 'Voice instruction could not be processed',
        }),
      });

      await expect(
        editByVoice({ contentId, instructionText }),
      ).rejects.toThrow('Voice instruction could not be processed');
    });

    it('should throw on malformed response data', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ invalid: 'data' }),
      });

      await expect(
        editByVoice({ contentId, instructionText }),
      ).rejects.toThrow(/invalid response/i);
    });
  });
});
