/**
 * Integration test for the backend-say-event-triggers-voice-and-transcript path
 *
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 *
 * This proves end-to-end:
 * - Reachability: Full chain from SAY event → voice synthesis → TRANSCRIPT_FINAL → UI render
 * - TypeInvariant: Types preserved across all boundaries (Zod schemas validated)
 * - ErrorConsistency: Injected failures produce defined VoiceErrors
 *
 * Full flow exercises:
 * 1. Intercept SAY event (step 1)
 * 2. Validate session context (step 2)
 * 3. Transform prompt to speech request (step 3)
 * 4. Synthesize and stream audio (step 4)
 * 5. Emit TRANSCRIPT_FINAL event (step 5)
 * 6. (UI render tested in component test)
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SayEventProcessChain } from '../process_chains/SayEventProcessChain';
import { SaySessionVerifier } from '../verifiers/SaySessionVerifier';
import type { SessionStore } from '../verifiers/SaySessionVerifier';
import { SpeechRequestTransformer } from '../transformers/SpeechRequestTransformer';
import { VoiceSynthesisService } from '../services/VoiceSynthesisService';
import type { VoiceClient } from '../services/VoiceSynthesisService';
import { VoiceError } from '../error_definitions/VoiceErrors';
import { validateTranscriptPayload } from '@/verifiers/TranscriptVerifier';
import {
  SayEventWithSessionContextSchema,
  ValidatedSayCommandSchema,
  SpeechSynthesisRequestSchema,
  TranscriptFinalEventSchema,
} from '../data_structures/VoiceEvent';

// Mock the backend logger to capture calls
vi.mock('../logging/voiceLogger', () => ({
  voiceLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { voiceLogger } from '../logging/voiceLogger';
const mockLogger = vi.mocked(voiceLogger);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const activeSessionStore: SessionStore = {
  async isActive(_sessionId: string): Promise<boolean> {
    return true;
  },
};

const inactiveSessionStore: SessionStore = {
  async isActive(_sessionId: string): Promise<boolean> {
    return false;
  },
};

function createSuccessfulVoiceClient(transcript: string): VoiceClient {
  return {
    async synthesize(_request) {
      return { transcript };
    },
  };
}

function createFailingVoiceClient(failCount: number, transcript: string): VoiceClient {
  let calls = 0;
  return {
    async synthesize(_request) {
      calls++;
      if (calls <= failCount) {
        throw new Error(`Synthesis attempt ${calls} failed`);
      }
      return { transcript };
    },
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Backend SAY Event Integration — Path 304', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: Full path from SAY → TRANSCRIPT_FINAL
  // -------------------------------------------------------------------------

  describe('Reachability: Full chain from SAY → TRANSCRIPT_FINAL', () => {
    it('should complete the full happy path: SAY → validate → transform → synthesize → dispatch', async () => {
      // Step 1: Intercept SAY event
      const sayEvent = { type: 'SAY' as const, sessionId: validSessionId, text: 'Hello world' };
      const eventWithContext = await SayEventProcessChain.handleEvent(sayEvent);
      expect(eventWithContext.sessionContext.isActive).toBe(true);

      // Step 2: Validate session context
      const validatedCommand = await SaySessionVerifier.validateActiveSession(
        eventWithContext,
        activeSessionStore,
      );
      expect(validatedCommand.sessionId).toBe(validSessionId);
      expect(validatedCommand.text).toBe('Hello world');

      // Step 3: Transform to speech request
      const speechRequest = SpeechRequestTransformer.toSpeechRequest(validatedCommand);
      expect(speechRequest.text).toBe('Hello world');
      expect(speechRequest.voiceId).toBeDefined();

      // Step 4: Synthesize and stream audio
      const voiceClient = createSuccessfulVoiceClient('Hello world');
      const transcript = await VoiceSynthesisService.synthesizeAndStream(
        speechRequest,
        voiceClient,
      );
      expect(transcript).toBe('Hello world');

      // Step 5: Emit TRANSCRIPT_FINAL
      const dispatcher = vi.fn().mockResolvedValue(undefined);
      const transcriptEvent = await SayEventProcessChain.emitTranscriptFinal(
        transcript,
        validSessionId,
        dispatcher,
      );
      expect(transcriptEvent.type).toBe('TRANSCRIPT_FINAL');
      expect(transcriptEvent.text).toBe('Hello world');

      // Step 6 validation: frontend verifier would validate before rendering
      const validation = validateTranscriptPayload(transcriptEvent);
      expect(validation.success).toBe(true);
    });

    it('should complete with retry recovery in synthesis step', async () => {
      // Steps 1-3 compressed
      const eventWithContext = await SayEventProcessChain.handleEvent({
        type: 'SAY',
        sessionId: validSessionId,
        text: 'Retry test',
      });
      const validatedCommand = await SaySessionVerifier.validateActiveSession(
        eventWithContext,
        activeSessionStore,
      );
      const speechRequest = SpeechRequestTransformer.toSpeechRequest(validatedCommand);

      // Step 4: Synthesize with 2 failures then success
      const retryClient = createFailingVoiceClient(2, 'Recovered transcript');
      const transcript = await VoiceSynthesisService.synthesizeAndStream(
        speechRequest,
        retryClient,
      );
      expect(transcript).toBe('Recovered transcript');

      // Step 5: Dispatch succeeds
      const dispatcher = vi.fn().mockResolvedValue(undefined);
      const event = await SayEventProcessChain.emitTranscriptFinal(
        transcript,
        validSessionId,
        dispatcher,
      );
      expect(event.text).toBe('Recovered transcript');

      // Logger should have been called for the 2 synthesis failures
      expect(mockLogger.error).toHaveBeenCalledTimes(2);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: Types preserved across boundaries
  // -------------------------------------------------------------------------

  describe('TypeInvariant: Types preserved across all boundaries', () => {
    it('should pass Zod schema validation at every step boundary', async () => {
      // Step 1 output
      const eventWithContext = await SayEventProcessChain.handleEvent({
        type: 'SAY',
        sessionId: validSessionId,
        text: 'Schema validation test',
      });
      expect(SayEventWithSessionContextSchema.safeParse(eventWithContext).success).toBe(true);

      // Step 2 output
      const validatedCommand = await SaySessionVerifier.validateActiveSession(
        eventWithContext,
        activeSessionStore,
      );
      expect(ValidatedSayCommandSchema.safeParse(validatedCommand).success).toBe(true);

      // Step 3 output
      const speechRequest = SpeechRequestTransformer.toSpeechRequest(validatedCommand);
      expect(SpeechSynthesisRequestSchema.safeParse(speechRequest).success).toBe(true);

      // Step 4 output (transcript is a string)
      const voiceClient = createSuccessfulVoiceClient('Schema validation test');
      const transcript = await VoiceSynthesisService.synthesizeAndStream(
        speechRequest,
        voiceClient,
      );
      expect(typeof transcript).toBe('string');

      // Step 5 output
      const dispatcher = vi.fn().mockResolvedValue(undefined);
      const event = await SayEventProcessChain.emitTranscriptFinal(
        transcript,
        validSessionId,
        dispatcher,
      );
      expect(TranscriptFinalEventSchema.safeParse(event).success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: Injected failures produce defined VoiceErrors
  // -------------------------------------------------------------------------

  describe('ErrorConsistency: Injected failures produce defined VoiceErrors', () => {
    it('should abort at step 1 for malformed SAY payload', async () => {
      try {
        await SayEventProcessChain.handleEvent({ type: 'SAY', text: null });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('INVALID_SAY_PAYLOAD');
      }
    });

    it('should abort at step 2 for inactive session', async () => {
      const eventWithContext = await SayEventProcessChain.handleEvent({
        type: 'SAY',
        sessionId: validSessionId,
        text: 'Inactive session test',
      });

      try {
        await SaySessionVerifier.validateActiveSession(
          eventWithContext,
          inactiveSessionStore,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('SESSION_INACTIVE');
      }
    });

    it('should abort at step 3 for empty text transformation', async () => {
      // Manually construct a validated command with empty text
      // (bypassing step 1 validation which would catch it)
      try {
        SpeechRequestTransformer.toSpeechRequest({
          sessionId: validSessionId,
          text: '',
          validatedAt: new Date().toISOString(),
        });
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSFORMATION_FAILED');
      }
    });

    it('should abort at step 4 after 3 synthesis failures', async () => {
      const eventWithContext = await SayEventProcessChain.handleEvent({
        type: 'SAY',
        sessionId: validSessionId,
        text: 'Synthesis failure test',
      });
      const validatedCommand = await SaySessionVerifier.validateActiveSession(
        eventWithContext,
        activeSessionStore,
      );
      const speechRequest = SpeechRequestTransformer.toSpeechRequest(validatedCommand);

      const failingClient = createFailingVoiceClient(3, 'Never reached');

      try {
        await VoiceSynthesisService.synthesizeAndStream(speechRequest, failingClient);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('SYNTHESIS_FAILED');
        expect((e as VoiceError).retryable).toBe(true);
      }
    });

    it('should abort at step 5 after 3 dispatch failures', async () => {
      const dispatcher = vi.fn()
        .mockRejectedValue(new Error('Persistent dispatch failure'));

      try {
        await SayEventProcessChain.emitTranscriptFinal(
          'Some transcript',
          validSessionId,
          dispatcher,
        );
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VoiceError);
        expect((e as VoiceError).code).toBe('TRANSCRIPT_DISPATCH_FAILED');
      }
    });

    it('should reject invalid transcript at frontend verifier', () => {
      const result = validateTranscriptPayload({
        type: 'TRANSCRIPT_FINAL',
        text: '',
        sessionId: validSessionId,
      });

      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBeGreaterThan(0);
      }
    });
  });
});
