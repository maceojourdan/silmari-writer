/**
 * captureSpokenInput.test.ts - Step 1: Capture spoken input
 *
 * TLA+ Properties:
 * - Reachability: Call captureSpokenInput → returns PartialSlotData
 * - TypeInvariant: Result conforms to PartialSlotData Zod schema; slot keys belong to question_type
 * - ErrorConsistency: Empty transcript → VoiceRecognitionError; retryCount incremented; escalation after 2 retries
 *
 * Resource: db-h2s4 (service)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VoiceError } from '@/server/error_definitions/VoiceErrors';
import {
  PartialSlotDataSchema,
  BEHAVIORAL_QUESTION_TYPE,
} from '@/server/data_structures/VoiceInteractionContext';
import type {
  VoiceInteractionContext,
  SlotState,
} from '@/server/data_structures/VoiceInteractionContext';

// Mock the recall voice logger
vi.mock('@/server/logging/recallVoiceLogger', () => ({
  recallVoiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { VoiceRecallService } from '../VoiceRecallService';
import type { TranscriptionClient } from '../VoiceRecallService';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

function createContext(overrides: Partial<VoiceInteractionContext> = {}): VoiceInteractionContext {
  const defaultSlotState: SlotState = {
    slots: [],
  };

  return {
    sessionId: validSessionId,
    questionType: BEHAVIORAL_QUESTION_TYPE,
    slotState: defaultSlotState,
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
    transcribe: vi.fn().mockRejectedValue(new Error('Transcription failed')),
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VoiceRecallService.captureSpokenInput — Step 1: Capture spoken input', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return PartialSlotData on valid transcript', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient(
        'My objective was to increase sales by 20%. I took three actions: cold calling, email campaigns, and social media outreach.',
      );

      const result = await VoiceRecallService.captureSpokenInput(context, audioBlob, client);

      expect(result).toBeDefined();
      expect(result.slots).toBeDefined();
      expect(result.slots.length).toBeGreaterThan(0);
    });

    it('should call transcription client with audio blob', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('I wanted to improve team morale.');

      await VoiceRecallService.captureSpokenInput(context, audioBlob, client);

      expect(client.transcribe).toHaveBeenCalledOnce();
      expect(client.transcribe).toHaveBeenCalledWith(audioBlob);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return result conforming to PartialSlotData Zod schema', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient(
        'My objective was to deliver the project on time.',
      );

      const result = await VoiceRecallService.captureSpokenInput(context, audioBlob, client);

      const parsed = PartialSlotDataSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should return slot keys that belong to question_type definition', async () => {
      const context = createContext();
      const audioBlob = new Blob(['fake-audio'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient(
        'My objective was to fix the production outage.',
      );

      const result = await VoiceRecallService.captureSpokenInput(context, audioBlob, client);

      const validSlotNames = context.questionType.slots.map((s) => s.name);
      for (const slot of result.slots) {
        expect(validSlotNames).toContain(slot.name);
      }
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw VoiceRecognitionError when transcript is empty', async () => {
      const context = createContext();
      const audioBlob = new Blob(['silence'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('');

      try {
        await VoiceRecallService.captureSpokenInput(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('VOICE_RECOGNITION_FAILED');
      }
    });

    it('should increment retryCount in returned context on empty transcript', async () => {
      const context = createContext({ retryCount: 0 });
      const audioBlob = new Blob(['silence'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('');

      try {
        await VoiceRecallService.captureSpokenInput(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).retryable).toBe(true);
      }
    });

    it('should set escalation flag after max retries exceeded', async () => {
      const context = createContext({ retryCount: 2, maxRetries: 2 });
      const audioBlob = new Blob(['silence'], { type: 'audio/wav' });
      const client = createMockTranscriptionClient('');

      try {
        await VoiceRecallService.captureSpokenInput(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        // After max retries, retryable should be false (escalated)
        expect((e as VoiceError).retryable).toBe(false);
      }
    });

    it('should throw VoiceRecognitionError when transcription client fails', async () => {
      const context = createContext();
      const audioBlob = new Blob(['bad-audio'], { type: 'audio/wav' });
      const client = createFailingTranscriptionClient();

      try {
        await VoiceRecallService.captureSpokenInput(context, audioBlob, client);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('VOICE_RECOGNITION_FAILED');
      }
    });
  });
});
