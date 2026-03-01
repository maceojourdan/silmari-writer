/**
 * captureSpokenAnswer.318.test.ts - Step 1: Capture spoken answer
 *
 * TLA+ Properties:
 * - Reachability: Call SessionWorkflowService.captureSpokenAnswer → returns { transcript, questionTypeId }
 * - TypeInvariant: transcript is non-empty string; questionTypeId matches session context
 * - ErrorConsistency: Empty audio → VoiceErrors.TRANSCRIPTION_FAILED; attemptCount incremented and ≤3
 *
 * Resource: db-h2s4 (service)
 * Path: 318-complete-voice-answer-advances-workflow
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import type { VoiceInteractionContext } from '@/server/data_structures/VoiceInteractionContext';
import { BEHAVIORAL_QUESTION_TYPE } from '@/server/data_structures/VoiceInteractionContext';

// Mock the workflow voice logger
vi.mock('@/server/logging/workflowVoiceLogger', () => ({
  workflowVoiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { SessionWorkflowService } from '../SessionWorkflowService';
import type { TranscriptionClient } from '../VoiceRecallService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createContext(overrides: Partial<VoiceInteractionContext> = {}): VoiceInteractionContext {
  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE,
    slotState: { slots: [] },
    retryCount: 0,
    maxRetries: 2,
    ...overrides,
  };
}

function createMockTranscriptionClient(transcript: string): TranscriptionClient {
  return {
    transcribe: vi.fn().mockResolvedValue({ transcript }),
  };
}

function createFailingTranscriptionClient(): TranscriptionClient {
  return {
    transcribe: vi.fn().mockRejectedValue(new Error('Transcription service unavailable')),
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('SessionWorkflowService.captureSpokenAnswer — Step 1: Capture spoken answer', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return transcript and questionTypeId on valid audio', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient(
        'I led a team of engineers to deliver a critical project on time.',
      );

      const result = await SessionWorkflowService.captureSpokenAnswer(
        context,
        audioBlob,
        client,
      );

      expect(result).toBeDefined();
      expect(result.transcript).toBe(
        'I led a team of engineers to deliver a critical project on time.',
      );
      expect(result.questionTypeId).toBe('behavioral_question');
    });

    it('should call transcription client with audio blob', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('I managed a project.');

      await SessionWorkflowService.captureSpokenAnswer(context, audioBlob, client);

      expect(client.transcribe).toHaveBeenCalledOnce();
      expect(client.transcribe).toHaveBeenCalledWith(audioBlob);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return transcript as non-empty string', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('I managed a large-scale migration.');

      const result = await SessionWorkflowService.captureSpokenAnswer(
        context,
        audioBlob,
        client,
      );

      expect(typeof result.transcript).toBe('string');
      expect(result.transcript.length).toBeGreaterThan(0);
    });

    it('should return questionTypeId matching session context', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('I coordinated cross-team efforts.');

      const result = await SessionWorkflowService.captureSpokenAnswer(
        context,
        audioBlob,
        client,
      );

      expect(result.questionTypeId).toBe(context.questionType.name);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw TRANSCRIPTION_FAILED when audio is empty', async () => {
      const context = createContext();
      const audioBlob = new Blob([], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('');

      try {
        await SessionWorkflowService.captureSpokenAnswer(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSCRIPTION_FAILED');
      }
    });

    it('should throw TRANSCRIPTION_FAILED when transcription client fails', async () => {
      const context = createContext();
      const audioBlob = new Blob(['bad-audio'], { type: 'audio/wav' });
      const client = createFailingTranscriptionClient();

      try {
        await SessionWorkflowService.captureSpokenAnswer(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSCRIPTION_FAILED');
      }
    });

    it('should allow retries when attemptCount is within limit', async () => {
      const context = createContext({ retryCount: 1, maxRetries: 2 });
      const audioBlob = new Blob(['silence'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('');

      try {
        await SessionWorkflowService.captureSpokenAnswer(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).retryable).toBe(true);
      }
    });

    it('should set non-retryable after max attempts exceeded', async () => {
      const context = createContext({ retryCount: 2, maxRetries: 2 });
      const audioBlob = new Blob(['silence'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('');

      try {
        await SessionWorkflowService.captureSpokenAnswer(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).retryable).toBe(false);
      }
    });
  });
});
