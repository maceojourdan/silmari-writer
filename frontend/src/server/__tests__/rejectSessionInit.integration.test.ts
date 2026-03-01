/**
 * Integration test for Path 312: reject-session-initialization-when-required-objects-missing-or-invalid
 *
 * Terminal Condition: Exercises full path from trigger:
 *   POST /api/sessions/initialize → RequestHandler → Service → validation error → response
 *
 * The DAO is mocked to simulate Supabase persistence. All other layers
 * run their real implementations to verify integration.
 *
 * Assertions:
 * - Reachability: Full endpoint → handler → service → error response
 * - TypeInvariant: All boundaries enforce typed schemas
 * - ErrorConsistency: Validation error always produced; no session created
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { ResumeObject, JobObject, QuestionObject } from '@/server/data_structures/SessionObjects';

// Mock ONLY the DAO (lowest layer) to simulate DB
vi.mock('@/server/data_access_objects/InitializeSessionDAO', () => {
  return {
    InitializeSessionDAO: {
      getActiveSession: vi.fn().mockResolvedValue(null),
      persist: vi.fn().mockImplementation(async (session: any) => ({
        id: '550e8400-e29b-41d4-a716-446655440000',
        resume: session.resume,
        job: session.job,
        question: session.question,
        state: session.state,
        createdAt: session.createdAt,
      })),
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

describe('Path 312 Integration: reject-session-initialization-when-required-objects-missing-or-invalid', () => {
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

  beforeEach(() => {
    vi.clearAllMocks();
    mockDAO.getActiveSession.mockResolvedValue(null);
    mockDAO.persist.mockImplementation(async (session: any) => ({
      id: '550e8400-e29b-41d4-a716-446655440000',
      resume: session.resume,
      job: session.job,
      question: session.question,
      state: session.state,
      createdAt: session.createdAt,
    }));
  });

  describe('Terminal: Send request with missing JobObject → full rejection flow', () => {
    it('should return HTTP 400 for missing JobObject', async () => {
      const request = createRequest({
        resume: validResume,
        question: validQuestion,
        // job is missing
      });

      const response = await POST(request as any);

      expect(response.status).toBe(400);
    });

    it('should explicitly identify "job" in the error response for missing JobObject', async () => {
      const request = createRequest({
        resume: validResume,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.message).toBeDefined();
      // The error message should reference the missing object
      expect(data.message.toLowerCase()).toContain('job');
    });

    it('should NOT insert a record in sessions table when JobObject is missing', async () => {
      const request = createRequest({
        resume: validResume,
        question: validQuestion,
      });

      await POST(request as any);

      expect(mockDAO.persist).not.toHaveBeenCalled();
    });
  });

  describe('Terminal: Send request with missing ResumeObject → full rejection flow', () => {
    it('should return HTTP 400 for missing ResumeObject', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });

    it('should explicitly identify "resume" in error response', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.message.toLowerCase()).toContain('resume');
    });

    it('should NOT insert any session record', async () => {
      const request = createRequest({
        job: validJob,
        question: validQuestion,
      });

      await POST(request as any);
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });
  });

  describe('Terminal: Send request with missing QuestionObject → full rejection flow', () => {
    it('should return HTTP 400 for missing QuestionObject', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
      });

      const response = await POST(request as any);
      expect(response.status).toBe(400);
    });

    it('should explicitly identify "question" in error response', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data.message.toLowerCase()).toContain('question');
    });
  });

  describe('Terminal: Send request with invalid object structure → full rejection flow', () => {
    it('should return HTTP 400 for empty resume content (caught at endpoint)', async () => {
      const request = createRequest({
        resume: { ...validResume, content: '' },
        job: validJob,
        question: validQuestion,
      });

      const response = await POST(request as any);

      expect(response.status).toBe(400);
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should return HTTP 400 for empty question text (caught at endpoint)', async () => {
      const request = createRequest({
        resume: validResume,
        job: validJob,
        question: { text: '' },
      });

      const response = await POST(request as any);

      expect(response.status).toBe(400);
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });

    it('should return HTTP 400 for invalid job sourceType', async () => {
      const request = createRequest({
        resume: validResume,
        job: { ...validJob, sourceType: 'invalid_type' },
        question: validQuestion,
      });

      const response = await POST(request as any);

      expect(response.status).toBe(400);
      expect(mockDAO.persist).not.toHaveBeenCalled();
    });
  });

  describe('Reachability: full endpoint → handler → service → error response', () => {
    it('should exercise complete rejection chain with all objects missing', async () => {
      const request = createRequest({});

      const response = await POST(request as any);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('INVALID_REQUEST_FORMAT');
      expect(mockDAO.persist).not.toHaveBeenCalled();
      expect(mockDAO.getActiveSession).not.toHaveBeenCalled();
    });
  });

  describe('TypeInvariant: all boundaries enforce typed schemas', () => {
    it('should return structured { code, message } for all error cases', async () => {
      const request = createRequest({
        resume: validResume,
        question: validQuestion,
      });

      const response = await POST(request as any);
      const data = await response.json();

      expect(data).toHaveProperty('code');
      expect(data).toHaveProperty('message');
      expect(typeof data.code).toBe('string');
      expect(typeof data.message).toBe('string');
    });
  });

  describe('ErrorConsistency: validation error always produced; no session created', () => {
    it('should NEVER create a session for any invalid input variation', async () => {
      // Test multiple invalid inputs in sequence
      const invalidInputs = [
        { job: validJob, question: validQuestion }, // missing resume
        { resume: validResume, question: validQuestion }, // missing job
        { resume: validResume, job: validJob }, // missing question
        {}, // all missing
        { resume: { ...validResume, content: '' }, job: validJob, question: validQuestion }, // invalid resume
        { resume: validResume, job: { ...validJob, title: '' }, question: validQuestion }, // invalid job
      ];

      for (const input of invalidInputs) {
        vi.clearAllMocks();
        mockDAO.getActiveSession.mockResolvedValue(null);

        const request = createRequest(input);
        const response = await POST(request as any);

        expect(response.status).toBeGreaterThanOrEqual(400);
        expect(mockDAO.persist).not.toHaveBeenCalled();
      }
    });
  });
});
