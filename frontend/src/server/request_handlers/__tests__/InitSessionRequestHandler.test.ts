/**
 * Tests for InitSessionRequestHandler
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: service returns IDs → handler returns { sessionId, resumeId, jobId, questionId }
 * - TypeInvariant: response matches InitSessionResponseSchema
 * - ErrorConsistency: unexpected exception → logs error and returns GenericErrors.InternalError
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { z } from 'zod';
import { GenericError } from '../../error_definitions/GenericErrors';
import type { SessionInitResult } from '../../data_structures/SessionObjects';

// Mock the processor
vi.mock('../../processors/SessionInputProcessor', () => ({
  SessionInputProcessor: {
    process: vi.fn(),
  },
}));

// Mock the service
vi.mock('../../services/SessionInitService', () => ({
  SessionInitService: {
    initialize: vi.fn(),
  },
}));

// Mock the logger
vi.mock('../../logging/logger', () => ({
  logger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SessionInputProcessor } from '../../processors/SessionInputProcessor';
import { SessionInitService } from '../../services/SessionInitService';
import { logger } from '../../logging/logger';
import { InitSessionRequestHandler } from '../InitSessionRequestHandler';

const mockProcessor = vi.mocked(SessionInputProcessor);
const mockService = vi.mocked(SessionInitService);
const mockLogger = vi.mocked(logger);

// Response schema for TypeInvariant testing
const InitSessionResponseSchema = z.object({
  sessionId: z.string().min(1),
  resumeId: z.string().min(1),
  jobId: z.string().min(1),
  questionId: z.string().min(1),
});

describe('InitSessionRequestHandler', () => {
  const validPayload = {
    resume: 'Experienced software engineer...',
    jobText: 'Senior Developer at Acme Corp',
    questionText: 'Tell me about a challenge.',
  };

  const parsedInput = {
    resume: {
      content: 'Experienced software engineer...',
      name: 'Uploaded Resume',
      wordCount: 3,
    },
    job: {
      title: 'Senior Developer at Acme Corp',
      description: 'Senior Developer at Acme Corp',
      sourceType: 'text' as const,
      sourceValue: 'Senior Developer at Acme Corp',
    },
    question: {
      text: 'Tell me about a challenge.',
    },
  };

  const serviceResult: SessionInitResult = {
    sessionId: '550e8400-e29b-41d4-a716-446655440000',
    resumeId: '550e8400-e29b-41d4-a716-446655440001',
    jobId: '550e8400-e29b-41d4-a716-446655440002',
    questionId: '550e8400-e29b-41d4-a716-446655440003',
  };

  function setupSuccessfulMocks() {
    mockProcessor.process.mockResolvedValue(parsedInput);
    mockService.initialize.mockResolvedValue(serviceResult);
  }

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: valid payload → handler returns IDs', () => {
    it('should process input and initialize session', async () => {
      setupSuccessfulMocks();

      const result = await InitSessionRequestHandler.handle(validPayload);

      expect(mockProcessor.process).toHaveBeenCalledWith(validPayload);
      expect(mockService.initialize).toHaveBeenCalledWith(parsedInput);
      expect(result.sessionId).toBe(serviceResult.sessionId);
      expect(result.resumeId).toBe(serviceResult.resumeId);
      expect(result.jobId).toBe(serviceResult.jobId);
      expect(result.questionId).toBe(serviceResult.questionId);
    });
  });

  describe('TypeInvariant: response matches InitSessionResponseSchema', () => {
    it('should return response matching the schema', async () => {
      setupSuccessfulMocks();

      const result = await InitSessionRequestHandler.handle(validPayload);

      const parsed = InitSessionResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: unexpected errors → GenericErrors.InternalError', () => {
    it('should rethrow SessionError as-is (from processor)', async () => {
      const { SessionErrors } = await import('../../error_definitions/SessionErrors');
      mockProcessor.process.mockRejectedValue(
        SessionErrors.ParseFailure('Cannot parse resume'),
      );

      await expect(InitSessionRequestHandler.handle(validPayload)).rejects.toThrow(
        'Cannot parse resume',
      );
    });

    it('should wrap unexpected errors in GenericError and log', async () => {
      mockProcessor.process.mockRejectedValue(new TypeError('undefined is not a function'));

      await expect(InitSessionRequestHandler.handle(validPayload)).rejects.toThrow(
        GenericError,
      );

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should set GenericError code to INTERNAL_ERROR', async () => {
      mockProcessor.process.mockRejectedValue(new Error('Unexpected'));

      try {
        await InitSessionRequestHandler.handle(validPayload);
      } catch (e) {
        expect(e).toBeInstanceOf(GenericError);
        expect((e as GenericError).code).toBe('INTERNAL_ERROR');
      }
    });
  });
});
