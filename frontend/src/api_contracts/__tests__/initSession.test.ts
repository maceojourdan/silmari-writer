/**
 * Tests for initSession API contract
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: initSession(validPayload) → calls fetch with correct endpoint
 * - TypeInvariant: response validates against InitSessionResponseSchema
 * - ErrorConsistency: non-ok response → throws with error message
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { InitSessionResponseSchema, initSession } from '../initSession';
import type { InitSessionRequest } from '../initSession';

// Mock global fetch
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('initSession API contract', () => {
  const validPayload: InitSessionRequest = {
    resume: 'My resume content...',
    jobText: 'Senior Developer position at Acme Corp',
    questionText: 'Tell me about a challenge you overcame.',
  };

  const validResponse = {
    sessionId: '550e8400-e29b-41d4-a716-446655440000',
    resumeId: '550e8400-e29b-41d4-a716-446655440001',
    jobId: '550e8400-e29b-41d4-a716-446655440002',
    questionId: '550e8400-e29b-41d4-a716-446655440003',
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: valid payload → fetch called correctly', () => {
    it('should POST to /api/session/init with JSON body', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await initSession(validPayload);

      expect(mockFetch).toHaveBeenCalledWith('/api/session/init', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(validPayload),
      });
    });

    it('should return parsed response on success', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      const result = await initSession(validPayload);

      expect(result.sessionId).toBe(validResponse.sessionId);
      expect(result.resumeId).toBe(validResponse.resumeId);
      expect(result.jobId).toBe(validResponse.jobId);
      expect(result.questionId).toBe(validResponse.questionId);
    });
  });

  describe('TypeInvariant: response matches InitSessionResponseSchema', () => {
    it('should validate a correct response', () => {
      const parsed = InitSessionResponseSchema.safeParse(validResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject response with missing sessionId', () => {
      const parsed = InitSessionResponseSchema.safeParse({
        resumeId: 'r-1',
        jobId: 'j-1',
        questionId: 'q-1',
      });
      expect(parsed.success).toBe(false);
    });

    it('should reject response with empty string IDs', () => {
      const parsed = InitSessionResponseSchema.safeParse({
        sessionId: '',
        resumeId: '',
        jobId: '',
        questionId: '',
      });
      expect(parsed.success).toBe(false);
    });
  });

  describe('ErrorConsistency: non-ok response throws', () => {
    it('should throw when response is not ok', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 400,
        json: () => Promise.resolve({ code: 'INVALID_REQUEST', message: 'Missing resume' }),
      });

      await expect(initSession(validPayload)).rejects.toThrow('Missing resume');
    });

    it('should throw with status when error body cannot be parsed', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 500,
        json: () => Promise.reject(new Error('parse error')),
      });

      await expect(initSession(validPayload)).rejects.toThrow('500');
    });

    it('should throw when response body does not match schema', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve({ invalid: 'data' }),
      });

      await expect(initSession(validPayload)).rejects.toThrow('Invalid response');
    });
  });
});
