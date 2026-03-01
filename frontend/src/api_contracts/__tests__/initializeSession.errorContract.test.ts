/**
 * Tests for initializeSession API contract — Error handling
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 311-reject-duplicate-session-initialization
 *
 * TLA+ properties tested:
 * - Reachability: initializeSession() → when 409 → throws SessionAlreadyActiveError
 * - TypeInvariant: Error response validates against SessionInitErrorResponseSchema
 * - ErrorConsistency: HTTP 409 with SESSION_ALREADY_ACTIVE → typed SessionAlreadyActiveError
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  initializeSession,
  SessionInitErrorResponseSchema,
  SessionAlreadyActiveError,
} from '../initializeSession';
import type { InitializeSessionRequest } from '../initializeSession';

// Mock global fetch
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// Mock frontendLogger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

describe('initializeSession API contract — Path 311: Error handling', () => {
  const validRequest: InitializeSessionRequest = {
    resume: {
      content: 'Experienced software engineer.',
      name: 'Test Resume',
      wordCount: 4,
    },
    job: {
      title: 'Senior Engineer',
      description: 'Lead engineering team.',
      sourceType: 'text',
      sourceValue: 'Lead engineering team.',
    },
    question: {
      text: 'Tell me about a complex project.',
    },
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: 409 response triggers SessionAlreadyActiveError', () => {
    it('should throw SessionAlreadyActiveError on HTTP 409 with SESSION_ALREADY_ACTIVE', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 409,
        json: () => Promise.resolve({
          code: 'SESSION_ALREADY_ACTIVE',
          message: 'A session is already active. Please finalize or end the current session before starting a new one.',
        }),
      });

      await expect(initializeSession(validRequest)).rejects.toThrow(
        SessionAlreadyActiveError,
      );
    });
  });

  describe('TypeInvariant: error response matches SessionInitErrorResponseSchema', () => {
    it('should validate SESSION_ALREADY_ACTIVE error response shape', () => {
      const errorResponse = {
        code: 'SESSION_ALREADY_ACTIVE',
        message: 'A session is already active.',
      };

      const parsed = SessionInitErrorResponseSchema.safeParse(errorResponse);
      expect(parsed.success).toBe(true);
    });

    it('should validate generic error response shape', () => {
      const errorResponse = {
        code: 'INTERNAL_ERROR',
        message: 'An unexpected error occurred',
      };

      const parsed = SessionInitErrorResponseSchema.safeParse(errorResponse);
      expect(parsed.success).toBe(true);
    });

    it('should reject malformed error response', () => {
      const malformed = { error: 'something' };
      const parsed = SessionInitErrorResponseSchema.safeParse(malformed);
      expect(parsed.success).toBe(false);
    });
  });

  describe('ErrorConsistency: SessionAlreadyActiveError has correct properties', () => {
    it('should have code SESSION_ALREADY_ACTIVE and statusCode 409', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 409,
        json: () => Promise.resolve({
          code: 'SESSION_ALREADY_ACTIVE',
          message: 'A session is already active.',
        }),
      });

      try {
        await initializeSession(validRequest);
        expect.unreachable('Expected to throw');
      } catch (error) {
        expect(error).toBeInstanceOf(SessionAlreadyActiveError);
        const typed = error as SessionAlreadyActiveError;
        expect(typed.code).toBe('SESSION_ALREADY_ACTIVE');
        expect(typed.statusCode).toBe(409);
        expect(typed.message).toContain('session is already active');
      }
    });

    it('should throw generic Error for non-SESSION_ALREADY_ACTIVE 409', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 409,
        json: () => Promise.resolve({
          code: 'CONFLICT_GENERIC',
          message: 'A conflict occurred.',
        }),
      });

      await expect(initializeSession(validRequest)).rejects.toThrow(Error);
      await expect(initializeSession(validRequest)).rejects.not.toThrow(SessionAlreadyActiveError);
    });

    it('should throw generic Error for non-409 errors', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 500,
        json: () => Promise.resolve({
          code: 'INTERNAL_ERROR',
          message: 'Something broke.',
        }),
      });

      await expect(initializeSession(validRequest)).rejects.toThrow('Something broke.');
      await expect(initializeSession(validRequest)).rejects.not.toThrow(SessionAlreadyActiveError);
    });
  });
});
