/**
 * updateAnswer.test.ts - Typed API contract for updating an answer
 *
 * TLA+ Properties:
 * - Reachability: updateAnswer({ id, content }) → PUT /api/answers/:id → { id, content }
 * - TypeInvariant: response validated against UpdateAnswerResponseSchema via safeParse
 * - ErrorConsistency: non-ok with LOCKED code → throws UpdateAnswerApiError with code;
 *   non-ok with ANSWER_NOT_FOUND → throws UpdateAnswerApiError;
 *   ok but invalid response → throws Error about invalid response
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 337-prevent-edit-of-locked-answer
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  updateAnswer,
  UpdateAnswerRequestSchema,
  UpdateAnswerResponseSchema,
  UpdateAnswerApiError,
} from '../updateAnswer';

// ---------------------------------------------------------------------------
// Mock fetch
// ---------------------------------------------------------------------------

const mockFetch = vi.fn();

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const validRequest = { id: 'test-id', content: 'new content' };
const validResponse = { id: 'test-id', content: 'new content' };

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('updateAnswer API contract — PUT /api/answers/:id (Path 337)', () => {
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
    it('should PUT to /api/answers/:id with correct URL', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await updateAnswer(validRequest);

      expect(mockFetch).toHaveBeenCalledWith(
        '/api/answers/test-id',
        expect.objectContaining({
          method: 'PUT',
          headers: { 'Content-Type': 'application/json' },
        }),
      );
    });

    it('should send body with content only (not id)', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      await updateAnswer(validRequest);

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      expect(body).toEqual({ content: 'new content' });
    });

    it('should return parsed response on success', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve(validResponse),
      });

      const result = await updateAnswer(validRequest);

      expect(result).toEqual({ id: 'test-id', content: 'new content' });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should validate valid response against UpdateAnswerResponseSchema', () => {
      const parsed = UpdateAnswerResponseSchema.safeParse(validResponse);
      expect(parsed.success).toBe(true);
    });

    it('should validate valid request against UpdateAnswerRequestSchema', () => {
      const parsed = UpdateAnswerRequestSchema.safeParse(validRequest);
      expect(parsed.success).toBe(true);
    });

    it('should reject response missing content field', () => {
      const parsed = UpdateAnswerResponseSchema.safeParse({ id: 'test-id' });
      expect(parsed.success).toBe(false);
    });

    it('should reject response missing id field', () => {
      const parsed = UpdateAnswerResponseSchema.safeParse({ content: 'hello' });
      expect(parsed.success).toBe(false);
    });

    it('should reject request with empty id', () => {
      const parsed = UpdateAnswerRequestSchema.safeParse({ id: '', content: 'hello' });
      expect(parsed.success).toBe(false);
    });

    it('should reject request with empty content', () => {
      const parsed = UpdateAnswerRequestSchema.safeParse({ id: 'abc', content: '' });
      expect(parsed.success).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw UpdateAnswerApiError with code on LOCKED_ANSWER_MODIFICATION_FORBIDDEN', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 403,
        json: () =>
          Promise.resolve({
            code: 'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
            message: 'Cannot modify a finalized answer',
          }),
      });

      try {
        await updateAnswer(validRequest);
        expect.fail('Expected UpdateAnswerApiError to be thrown');
      } catch (error) {
        expect(error).toBeInstanceOf(UpdateAnswerApiError);
        expect((error as UpdateAnswerApiError).code).toBe(
          'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
        );
        expect((error as UpdateAnswerApiError).message).toBe(
          'Cannot modify a finalized answer',
        );
      }
    });

    it('should throw UpdateAnswerApiError with code on ANSWER_NOT_FOUND', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 404,
        json: () =>
          Promise.resolve({
            code: 'ANSWER_NOT_FOUND',
            message: 'Answer does not exist',
          }),
      });

      try {
        await updateAnswer(validRequest);
        expect.fail('Expected UpdateAnswerApiError to be thrown');
      } catch (error) {
        expect(error).toBeInstanceOf(UpdateAnswerApiError);
        expect((error as UpdateAnswerApiError).code).toBe('ANSWER_NOT_FOUND');
      }
    });

    it('should throw Error about invalid response when schema validation fails', async () => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: () => Promise.resolve({ id: 'test-id' }), // missing content
      });

      await expect(updateAnswer(validRequest)).rejects.toThrow(
        'Invalid response from update answer',
      );
    });

    it('should throw UpdateAnswerApiError with fallback message when error body has no message', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 500,
        json: () => Promise.resolve({ code: 'INTERNAL_ERROR' }),
      });

      try {
        await updateAnswer(validRequest);
        expect.fail('Expected UpdateAnswerApiError to be thrown');
      } catch (error) {
        expect(error).toBeInstanceOf(UpdateAnswerApiError);
        expect((error as UpdateAnswerApiError).code).toBe('INTERNAL_ERROR');
      }
    });

    it('should throw UpdateAnswerApiError with fallback when error body is not JSON', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 500,
        json: () => Promise.reject(new SyntaxError('Unexpected token')),
      });

      try {
        await updateAnswer(validRequest);
        expect.fail('Expected UpdateAnswerApiError to be thrown');
      } catch (error) {
        expect(error).toBeInstanceOf(UpdateAnswerApiError);
        expect((error as UpdateAnswerApiError).code).toBe('UNKNOWN_ERROR');
        expect((error as UpdateAnswerApiError).message).toBe(
          'Update answer failed with status 500',
        );
      }
    });
  });
});
