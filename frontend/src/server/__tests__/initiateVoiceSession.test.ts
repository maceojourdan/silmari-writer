/**
 * Integration Test - Terminal Condition: Initiate Voice-Assisted Answer Session
 *
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Exercise full path:
 * 1. Authenticated request
 * 2. Auth filter validates
 * 3. Handler delegates to service
 * 4. Service creates AnswerSession (INIT) + StoryRecord (INIT)
 * 5. Response returns sessionId and INIT state
 *
 * Proves:
 * - Reachability: Trigger → API → Handler → Service → DAO → Response
 * - TypeInvariant: All DTOs and DB entities validated via Zod schemas
 * - ErrorConsistency: Each failure branch returns defined error types
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';
import { AnswerSessionSchema, AnswerStoryRecordSchema, CreateSessionResponseSchema } from '@/server/data_structures/AnswerSession';

// Mock the DAO layer (simulates in-memory test DB)
vi.mock('@/server/data_access_objects/SessionDAO', () => {
  const sessions: Map<string, any> = new Map();
  const stories: Map<string, any> = new Map();

  return {
    SessionDAO: {
      createSession: vi.fn(async (userId: string) => {
        const session = {
          id: '550e8400-e29b-41d4-a716-446655440000',
          userId,
          state: 'INIT' as const,
          createdAt: new Date().toISOString(),
          updatedAt: new Date().toISOString(),
        };
        sessions.set(session.id, session);
        return session;
      }),
      createStoryRecord: vi.fn(async (sessionId: string) => {
        const story = {
          id: '550e8400-e29b-41d4-a716-446655440001',
          sessionId,
          status: 'INIT' as const,
          createdAt: new Date().toISOString(),
          updatedAt: new Date().toISOString(),
        };
        stories.set(story.id, story);
        return story;
      }),
      deleteSession: vi.fn(async (sessionId: string) => {
        sessions.delete(sessionId);
      }),
      // Expose internal stores for assertions
      _getSession: (id: string) => sessions.get(id),
      _getStory: (id: string) => stories.get(id),
      _clear: () => { sessions.clear(); stories.clear(); },
    },
  };
});

import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { POST } from '@/app/api/sessions/route';

const mockDAO = vi.mocked(SessionDAO) as any;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function createAuthenticatedRequest(): NextRequest {
  return new NextRequest('http://localhost:3000/api/sessions', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      'Authorization': 'Bearer test-integration-token',
    },
    body: JSON.stringify({}),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Integration: Initiate Voice-Assisted Answer Session (full path)', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    if (mockDAO._clear) mockDAO._clear();
  });

  // -------------------------------------------------------------------------
  // Full Path: Happy Path
  // -------------------------------------------------------------------------

  describe('Full Path: Trigger → API → Handler → Service → DAO → Response', () => {
    it('should return HTTP 200 with sessionId and state INIT', async () => {
      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.sessionId).toBeDefined();
      expect(data.state).toBe('INIT');
    });

    it('should create Session row with state INIT in DB', async () => {
      const request = createAuthenticatedRequest();
      await POST(request);

      const session = mockDAO._getSession('550e8400-e29b-41d4-a716-446655440000');
      expect(session).toBeDefined();
      expect(session.state).toBe('INIT');

      // Validate against Zod schema
      const validation = AnswerSessionSchema.safeParse(session);
      expect(validation.success).toBe(true);
    });

    it('should create StoryRecord row with status INIT in DB', async () => {
      const request = createAuthenticatedRequest();
      await POST(request);

      const story = mockDAO._getStory('550e8400-e29b-41d4-a716-446655440001');
      expect(story).toBeDefined();
      expect(story.status).toBe('INIT');

      // Validate against Zod schema
      const validation = AnswerStoryRecordSchema.safeParse(story);
      expect(validation.success).toBe(true);
    });

    it('should return response conforming to CreateSessionResponse schema', async () => {
      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      const validation = CreateSessionResponseSchema.safeParse(data);
      expect(validation.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // Error Paths
  // -------------------------------------------------------------------------

  describe('Error Paths', () => {
    it('should return 401 when no auth header provided', async () => {
      const request = new NextRequest('http://localhost:3000/api/sessions', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({}),
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('UNAUTHORIZED');
    });

    it('should return 500 when session creation fails', async () => {
      mockDAO.createSession.mockRejectedValueOnce(new Error('DB down'));

      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('SESSION_PERSISTENCE_ERROR');
    });

    it('should return 500 and rollback session when story creation fails', async () => {
      mockDAO.createStoryRecord.mockRejectedValueOnce(new Error('Story table missing'));

      const request = createAuthenticatedRequest();
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('STORY_PERSISTENCE_ERROR');
      expect(mockDAO.deleteSession).toHaveBeenCalled();
    });
  });
});
