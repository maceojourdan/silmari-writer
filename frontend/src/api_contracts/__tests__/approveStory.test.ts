/**
 * Tests for approveStory API contract
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * TLA+ properties tested:
 * - Reachability: approveStory sends POST request with payload
 * - TypeInvariant: Response matches ApproveStoryResponse schema
 * - ErrorConsistency: Network/server errors are properly caught
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  approveStory,
  ApproveStoryResponseSchema,
  type ApproveStoryRequest,
  type ApproveStoryResponse,
} from '../approveStory';

// Mock global fetch
const mockFetch = vi.fn();

describe('approveStory API contract', () => {
  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  const validRequest: ApproveStoryRequest = {
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
  };

  const validResponse: ApproveStoryResponse = {
    storyRecordId: 'story-record-001',
    status: 'FINALIZED',
    persistedAt: '2026-02-28T12:00:00.000Z',
  };

  describe('Reachability: Sends POST request', () => {
    it('should POST to /api/approve-story with the payload', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      await approveStory(validRequest);

      expect(mockFetch).toHaveBeenCalledTimes(1);
      expect(mockFetch).toHaveBeenCalledWith('/api/approve-story', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(validRequest),
      });
    });
  });

  describe('TypeInvariant: Response schema', () => {
    it('should return a valid ApproveStoryResponse on success', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      const result = await approveStory(validRequest);

      const parsed = ApproveStoryResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
      expect(result.storyRecordId).toBe('story-record-001');
      expect(result.status).toBe('FINALIZED');
      expect(result.persistedAt).toBeDefined();
    });
  });

  describe('ErrorConsistency: Error handling', () => {
    it('should throw on non-OK HTTP response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 400,
        json: async () => ({ code: 'VALIDATION_ERROR', message: 'Invalid request' }),
      });

      await expect(approveStory(validRequest)).rejects.toThrow('Invalid request');
    });

    it('should throw on network failure', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      await expect(approveStory(validRequest)).rejects.toThrow('Network error');
    });

    it('should throw on malformed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      await expect(approveStory(validRequest)).rejects.toThrow();
    });
  });
});
