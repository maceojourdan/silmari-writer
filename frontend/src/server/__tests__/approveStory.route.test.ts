/**
 * Tests for the approve-story backend endpoint
 *
 * Resource: api-m5g7 (endpoint), api-p3e6 (filter), api-n8k2 (request_handler)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * TLA+ properties tested:
 * - Reachability: POST valid payload with mocked auth → 200 and handler invoked
 * - TypeInvariant: Transformed command type equals ApproveStoryCommand
 * - ErrorConsistency: Missing auth → UNAUTHORIZED; Missing field → VALIDATION_ERROR
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { AuthAndValidationFilter, type AuthContext } from '../filters/AuthAndValidationFilter';
import { ApproveStoryRequestHandler } from '../request_handlers/ApproveStoryRequestHandler';
import { StoryError } from '../error_definitions/StoryErrors';
import type { ApproveStoryCommand } from '../data_structures/StoryRecord';

// Mock the processor
vi.mock('../processors/ApproveStoryProcessor', () => ({
  ApproveStoryProcessor: {
    process: vi.fn(),
  },
}));

import { ApproveStoryProcessor } from '../processors/ApproveStoryProcessor';
const mockProcess = vi.mocked(ApproveStoryProcessor.process);

describe('approve-story endpoint (Step 2)', () => {
  const validBody = {
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
  };

  const validAuthContext: AuthContext = {
    userId: 'user-001',
    authenticated: true,
  };

  beforeEach(() => {
    mockProcess.mockReset();
  });

  describe('AuthAndValidationFilter', () => {
    describe('Reachability: Auth validation', () => {
      it('should return authenticated context for valid auth header', () => {
        const result = AuthAndValidationFilter.authenticate('Bearer valid-token');
        expect(result.authenticated).toBe(true);
        expect(result.userId).toBeDefined();
      });
    });

    describe('ErrorConsistency: Auth failures', () => {
      it('should throw UNAUTHORIZED when auth header is missing', () => {
        expect(() => AuthAndValidationFilter.authenticate(undefined)).toThrow(StoryError);
        try {
          AuthAndValidationFilter.authenticate(undefined);
        } catch (e) {
          expect((e as StoryError).code).toBe('UNAUTHORIZED');
          expect((e as StoryError).statusCode).toBe(401);
        }
      });

      it('should throw UNAUTHORIZED when auth header is empty', () => {
        expect(() => AuthAndValidationFilter.authenticate('')).toThrow(StoryError);
        try {
          AuthAndValidationFilter.authenticate('');
        } catch (e) {
          expect((e as StoryError).code).toBe('UNAUTHORIZED');
        }
      });
    });

    describe('Reachability: Body validation', () => {
      it('should return validated body for valid payload', () => {
        const result = AuthAndValidationFilter.validateBody(validBody);
        expect(result).toEqual(validBody);
      });
    });

    describe('ErrorConsistency: Body validation failures', () => {
      it('should throw VALIDATION_ERROR when required field is missing', () => {
        const { draftId, ...incomplete } = validBody;
        expect(() => AuthAndValidationFilter.validateBody(incomplete)).toThrow(StoryError);
        try {
          AuthAndValidationFilter.validateBody(incomplete);
        } catch (e) {
          expect((e as StoryError).code).toBe('VALIDATION_ERROR');
          expect((e as StoryError).statusCode).toBe(400);
        }
      });

      it('should throw VALIDATION_ERROR for completely empty body', () => {
        expect(() => AuthAndValidationFilter.validateBody({})).toThrow(StoryError);
        try {
          AuthAndValidationFilter.validateBody({});
        } catch (e) {
          expect((e as StoryError).code).toBe('VALIDATION_ERROR');
        }
      });
    });
  });

  describe('ApproveStoryRequestHandler', () => {
    describe('TypeInvariant: Command transformation', () => {
      it('should map validated body + auth to ApproveStoryCommand', () => {
        const command = ApproveStoryRequestHandler.toCommand(validBody, validAuthContext);

        expect(command).toEqual({
          draftId: 'draft-001',
          resumeId: 'resume-001',
          jobId: 'job-001',
          questionId: 'question-001',
          voiceSessionId: 'session-001',
          userId: 'user-001',
        } satisfies ApproveStoryCommand);
      });
    });

    describe('Reachability: Handler invokes processor', () => {
      it('should call ApproveStoryProcessor.process with the command', async () => {
        const mockResult = {
          storyRecordId: 'story-001',
          status: 'FINALIZED' as const,
          persistedAt: '2026-02-28T12:00:00.000Z',
        };
        mockProcess.mockResolvedValueOnce(mockResult);

        const result = await ApproveStoryRequestHandler.handle(validBody, validAuthContext);

        expect(mockProcess).toHaveBeenCalledTimes(1);
        const commandArg = mockProcess.mock.calls[0][0];
        expect(commandArg.draftId).toBe('draft-001');
        expect(commandArg.userId).toBe('user-001');
        expect(result).toEqual(mockResult);
      });
    });

    describe('ErrorConsistency: Processor errors propagate', () => {
      it('should propagate StoryError from processor', async () => {
        mockProcess.mockRejectedValueOnce(
          new StoryError('Related entity not found: resume', 'RELATED_ENTITY_NOT_FOUND', 404),
        );

        await expect(
          ApproveStoryRequestHandler.handle(validBody, validAuthContext),
        ).rejects.toThrow(StoryError);
      });
    });
  });
});
