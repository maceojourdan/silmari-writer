/**
 * Tests for VoiceResponseProcessor
 *
 * Resource: db-b7r2 (processor)
 * Path: 307-process-voice-input-and-progress-session
 *
 * TLA+ properties tested:
 * - Reachability: INIT session + transcript → returns { nextState: IN_PROGRESS, updatedContent }
 * - TypeInvariant: result matches VoiceResponseProcessorResult type
 * - ErrorConsistency: non-INIT session → returns current state (no-op transition)
 */

import { describe, it, expect } from 'vitest';
import { VoiceResponseProcessor } from '../VoiceResponseProcessor';
import type { VoiceResponseProcessorResult } from '../VoiceResponseProcessor';
import type { AnswerSession } from '../../data_structures/AnswerSession';

describe('VoiceResponseProcessor', () => {
  const initSession: AnswerSession = {
    id: '550e8400-e29b-41d4-a716-446655440000',
    userId: 'user-123',
    state: 'INIT',
    createdAt: '2026-02-28T00:00:00Z',
    updatedAt: '2026-02-28T00:00:00Z',
  };

  const transcript = 'I led a cross-functional team that reduced deployment time by 40 percent.';

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return IN_PROGRESS state for INIT session', () => {
      const result = VoiceResponseProcessor.process(transcript, initSession);

      expect(result.nextState).toBe('IN_PROGRESS');
    });

    it('should set updatedContent to the transcript', () => {
      const result = VoiceResponseProcessor.process(transcript, initSession);

      expect(result.updatedContent).toBe(transcript);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object matching VoiceResponseProcessorResult type', () => {
      const result: VoiceResponseProcessorResult = VoiceResponseProcessor.process(
        transcript,
        initSession,
      );

      expect(typeof result.nextState).toBe('string');
      expect(typeof result.updatedContent).toBe('string');
      expect(['INIT', 'IN_PROGRESS']).toContain(result.nextState);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return current state for non-INIT session (no-op)', () => {
      const inProgressSession: AnswerSession = {
        ...initSession,
        state: 'IN_PROGRESS',
      };

      const result = VoiceResponseProcessor.process(transcript, inProgressSession);

      expect(result.nextState).toBe('IN_PROGRESS');
      expect(result.updatedContent).toBe(transcript);
    });
  });
});
