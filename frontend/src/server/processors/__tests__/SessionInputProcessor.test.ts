/**
 * Tests for SessionInputProcessor
 *
 * Resource: db-b7r2 (processor)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: call process(rawInput) → returns { resume, job, question }
 * - TypeInvariant: each matches Zod schema from SessionObjects.ts
 * - ErrorConsistency:
 *   - Transformer throws → expect SessionErrors.ParseFailure
 *   - Verifier fails → expect SessionErrors.ValidationFailure
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SessionError } from '../../error_definitions/SessionErrors';
import {
  ResumeObjectSchema,
  JobObjectSchema,
  QuestionObjectSchema,
} from '../../data_structures/SessionObjects';

// Mock the transformer
vi.mock('../../transformers/SessionInputTransformer', () => ({
  SessionInputTransformer: {
    transform: vi.fn(),
  },
}));

// Mock the shared verifier
vi.mock('../../verifiers/SessionObjectVerifier', () => ({
  SessionObjectVerifier: {
    validate: vi.fn(),
  },
}));

import { SessionInputTransformer } from '../../transformers/SessionInputTransformer';
import { SessionObjectVerifier } from '../../verifiers/SessionObjectVerifier';
import { SessionInputProcessor } from '../SessionInputProcessor';

const mockTransformer = vi.mocked(SessionInputTransformer);
const mockVerifier = vi.mocked(SessionObjectVerifier);

describe('SessionInputProcessor', () => {
  const rawInput = {
    resume: 'Experienced software engineer with 10 years of expertise...',
    jobText: 'Senior Software Engineer at Acme Corp. Must have experience with distributed systems.',
    questionText: 'Tell me about a time you led a complex technical project.',
  };

  const transformedObjects = {
    resume: {
      content: 'Experienced software engineer with 10 years of expertise...',
      name: 'Uploaded Resume',
      wordCount: 8,
    },
    job: {
      title: 'Senior Software Engineer',
      description: 'Senior Software Engineer at Acme Corp. Must have experience with distributed systems.',
      sourceType: 'text' as const,
      sourceValue: 'Senior Software Engineer at Acme Corp. Must have experience with distributed systems.',
    },
    question: {
      text: 'Tell me about a time you led a complex technical project.',
    },
  };

  function setupSuccessfulMocks() {
    mockTransformer.transform.mockReturnValue(transformedObjects);
    mockVerifier.validate.mockReturnValue({ valid: true });
  }

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: valid input → returns parsed objects', () => {
    it('should call transformer and verifier, returning structured objects', async () => {
      setupSuccessfulMocks();

      const result = await SessionInputProcessor.process(rawInput);

      expect(mockTransformer.transform).toHaveBeenCalledWith(rawInput);
      expect(mockVerifier.validate).toHaveBeenCalledWith(transformedObjects);
      expect(result).toHaveProperty('resume');
      expect(result).toHaveProperty('job');
      expect(result).toHaveProperty('question');
    });

    it('should return the exact objects from the transformer', async () => {
      setupSuccessfulMocks();

      const result = await SessionInputProcessor.process(rawInput);

      expect(result.resume.content).toBe(rawInput.resume);
      expect(result.job.sourceType).toBe('text');
      expect(result.question.text).toBe(rawInput.questionText);
    });
  });

  describe('TypeInvariant: each object matches its Zod schema', () => {
    it('should produce a resume matching ResumeObjectSchema', async () => {
      setupSuccessfulMocks();

      const result = await SessionInputProcessor.process(rawInput);

      const parsed = ResumeObjectSchema.safeParse(result.resume);
      expect(parsed.success).toBe(true);
    });

    it('should produce a job matching JobObjectSchema', async () => {
      setupSuccessfulMocks();

      const result = await SessionInputProcessor.process(rawInput);

      const parsed = JobObjectSchema.safeParse(result.job);
      expect(parsed.success).toBe(true);
    });

    it('should produce a question matching QuestionObjectSchema', async () => {
      setupSuccessfulMocks();

      const result = await SessionInputProcessor.process(rawInput);

      const parsed = QuestionObjectSchema.safeParse(result.question);
      expect(parsed.success).toBe(true);
    });
  });

  describe('ErrorConsistency: transformer/verifier failures', () => {
    it('should throw PARSE_FAILURE when transformer throws', async () => {
      mockTransformer.transform.mockImplementation(() => {
        throw new Error('Cannot parse resume content');
      });

      await expect(SessionInputProcessor.process(rawInput)).rejects.toThrow(
        SessionError,
      );

      try {
        await SessionInputProcessor.process(rawInput);
      } catch (e) {
        expect((e as SessionError).code).toBe('PARSE_FAILURE');
      }
    });

    it('should throw VALIDATION_FAILURE when verifier returns invalid', async () => {
      mockTransformer.transform.mockReturnValue(transformedObjects);
      mockVerifier.validate.mockReturnValue({
        valid: false,
        errors: ['Resume content too short', 'Job title missing'],
      });

      await expect(SessionInputProcessor.process(rawInput)).rejects.toThrow(
        SessionError,
      );

      try {
        await SessionInputProcessor.process(rawInput);
      } catch (e) {
        expect((e as SessionError).code).toBe('VALIDATION_FAILURE');
        expect((e as SessionError).message).toContain('Resume content too short');
      }
    });
  });
});
