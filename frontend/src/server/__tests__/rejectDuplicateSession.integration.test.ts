/**
 * Integration test for Path 311: reject-duplicate-session-initialization
 *
 * Terminal Condition: Exercises the full path end-to-end:
 *   POST /api/sessions/initialize → RequestHandler → Service → DAO (active check) → Verifier → Error Response
 *
 * Proves:
 * - Reachability: full path from trigger (HTTP POST) to rejection (HTTP 409) exercised
 * - TypeInvariant: request → command → verifier → error → HTTP response types consistent
 * - ErrorConsistency: duplicate session always produces SESSION_ALREADY_ACTIVE + HTTP 409
 *
 * The DAO is mocked at the lowest layer. All other layers (endpoint, handler, service, verifier)
 * run their real implementations to verify integration across the full stack.
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { InitializedSession } from '@/server/data_structures/InitializedSession';
import type { ResumeObject, JobObject, QuestionObject } from '@/server/data_structures/SessionObjects';
import { SessionInitErrorResponseSchema } from '@/api_contracts/initializeSession';

// Mock ONLY the DAO (lowest layer) to simulate DB
vi.mock('@/server/data_access_objects/InitializeSessionDAO', () => {
  return {
    InitializeSessionDAO: {
      getActiveSession: vi.fn(),
      persist: vi.fn(),
    },
  };
});

// Mock logger to avoid noisy output
vi.mock('@/server/logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { InitializeSessionDAO } from '@/server/data_access_objects/InitializeSessionDAO';
import { POST } from '@/app/api/sessions/initialize/route';

const mockDAO = vi.mocked(InitializeSessionDAO);

function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/sessions/initialize', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('Path 311 Integration: reject-duplicate-session-initialization', () => {
  const validResume: ResumeObject = {
    content: 'Experienced software engineer with 10 years of expertise in TypeScript and React.',
    name: 'Jane Smith Resume',
    wordCount: 12,
  };

  const validJob: JobObject = {
    title: 'Senior Software Engineer',
    description: 'We are looking for a senior engineer to lead our frontend team building next-gen applications.',
    sourceType: 'text',
    sourceValue: 'We are looking for a senior engineer to lead our frontend team building next-gen applications.',
  };

  const validQuestion: QuestionObject = {
    text: 'Tell me about a time you led a complex technical project and how you handled technical disagreements.',
  };

  const validBody = {
    resume: validResume,
    job: validJob,
    question: validQuestion,
  };

  // Simulate an existing active session in the database
  const existingActiveSession: InitializedSession = {
    id: '110e8400-e29b-41d4-a716-446655440000',
    resume: {
      content: 'Previous engineer resume content.',
      name: 'Previous Resume',
      wordCount: 5,
    },
    job: {
      title: 'Previous Job Title',
      description: 'Previous job description.',
      sourceType: 'text',
      sourceValue: 'Previous job description.',
    },
    question: {
      text: 'Previous question text.',
    },
    state: 'initialized',
    createdAt: '2026-02-28T10:00:00.000Z',
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  // =========================================================================
  // SCENARIO: Active session exists → reject duplicate
  // =========================================================================

  describe('Scenario: Active session exists → reject with 409', () => {
    beforeEach(() => {
      // Seed: active session exists (status = INIT / 'initialized')
      mockDAO.getActiveSession.mockResolvedValue(existingActiveSession);
      mockDAO.persist.mockImplementation(async (session: any) => ({
        id: '220e8400-e29b-41d4-a716-446655440000',
        resume: session.resume,
        job: session.job,
        question: session.question,
        state: session.state,
        createdAt: session.createdAt,
      }));
    });

    it('should return HTTP 409 when active session exists', async () => {
      const request = createRequest(validBody);
      const response = await POST(request as any);

      expect(response.status).toBe(409);
    });

    it('should return error code SESSION_ALREADY_ACTIVE', async () => {
      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(data.code).toBe('SESSION_ALREADY_ACTIVE');
    });

    it('should return error response matching SessionInitErrorResponse schema', async () => {
      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      const parsed = SessionInitErrorResponseSchema.safeParse(data);
      expect(parsed.success).toBe(true);
    });

    it('should NOT create a new session row (persist not called)', async () => {
      const request = createRequest(validBody);
      await POST(request as any);

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should still call getActiveSession to check for existing session', async () => {
      const request = createRequest(validBody);
      await POST(request as any);

      expect(mockDAO.getActiveSession).toHaveBeenCalledTimes(1);
    });

    it('should leave existing session unchanged (no DAO mutations)', async () => {
      const request = createRequest(validBody);
      await POST(request as any);

      // Only getActiveSession should be called, no persist or other mutations
      expect(mockDAO.getActiveSession).toHaveBeenCalledTimes(1);
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });
  });

  // =========================================================================
  // CONTRAST: No active session → allow creation (Path 310 behavior)
  // =========================================================================

  describe('Contrast: No active session → allow creation (Path 310)', () => {
    beforeEach(() => {
      // No active session
      mockDAO.getActiveSession.mockResolvedValue(null);
      mockDAO.persist.mockImplementation(async (session: any) => ({
        id: '330e8400-e29b-41d4-a716-446655440000',
        resume: session.resume,
        job: session.job,
        question: session.question,
        state: session.state,
        createdAt: session.createdAt,
      }));
    });

    it('should return HTTP 200 when no active session exists', async () => {
      const request = createRequest(validBody);
      const response = await POST(request as any);

      expect(response.status).toBe(200);
    });

    it('should call DAO.persist to create new session', async () => {
      const request = createRequest(validBody);
      await POST(request as any);

      expect(mockDAO.persist).toHaveBeenCalledTimes(1);
    });
  });

  // =========================================================================
  // Reachability: full path from trigger to rejection
  // =========================================================================

  describe('Reachability: full path from trigger to rejection exercised', () => {
    it('should exercise the entire chain: endpoint → handler → service → DAO → verifier → error response', async () => {
      mockDAO.getActiveSession.mockResolvedValue(existingActiveSession);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      // Endpoint received and routed the request
      expect(response.status).toBe(409);

      // Handler transformed domain error to HTTP error
      expect(data.code).toBe('SESSION_ALREADY_ACTIVE');
      expect(data.message).toBeDefined();
      expect(typeof data.message).toBe('string');

      // DAO was called (service delegated to DAO)
      expect(mockDAO.getActiveSession).toHaveBeenCalled();

      // No session was created (verifier rejected)
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });
  });

  // =========================================================================
  // TypeInvariant: types consistent across boundaries
  // =========================================================================

  describe('TypeInvariant: request → command → verifier → error → HTTP response types consistent', () => {
    it('should reject with proper error shape even when request is fully valid', async () => {
      mockDAO.getActiveSession.mockResolvedValue(existingActiveSession);

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      // Request was valid (would have succeeded without active session)
      // But error response still has proper shape
      expect(data).toHaveProperty('code');
      expect(data).toHaveProperty('message');
      expect(typeof data.code).toBe('string');
      expect(typeof data.message).toBe('string');
    });

    it('should still reject with 400 for malformed request (not 409)', async () => {
      mockDAO.getActiveSession.mockResolvedValue(existingActiveSession);

      // Invalid request (missing resume)
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      // Validation error takes priority over uniqueness check
      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST');
      // DAO should not have been called at all
      expect(mockDAO.getActiveSession).not.toHaveBeenCalled();
    });
  });

  // =========================================================================
  // ErrorConsistency: duplicate always produces correct error
  // =========================================================================

  describe('ErrorConsistency: duplicate session always produces correct domain + HTTP error state', () => {
    it('should consistently return 409 + SESSION_ALREADY_ACTIVE across multiple attempts', async () => {
      mockDAO.getActiveSession.mockResolvedValue(existingActiveSession);

      // First attempt
      const response1 = await POST(createRequest(validBody) as any);
      const data1 = await response1.json();
      expect(response1.status).toBe(409);
      expect(data1.code).toBe('SESSION_ALREADY_ACTIVE');

      // Second attempt (same state)
      const response2 = await POST(createRequest(validBody) as any);
      const data2 = await response2.json();
      expect(response2.status).toBe(409);
      expect(data2.code).toBe('SESSION_ALREADY_ACTIVE');

      // Session was never created
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should return SERVICE_ERROR when DAO.getActiveSession fails', async () => {
      mockDAO.getActiveSession.mockRejectedValue(
        new Error('Database connection refused'),
      );

      const request = createRequest(validBody);
      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('SERVICE_ERROR');
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });
  });
});
