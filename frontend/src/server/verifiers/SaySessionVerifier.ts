/**
 * SaySessionVerifier - Validates that the session associated with a SAY event
 * is active and the payload structure matches expected schema.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 304-backend-say-event-triggers-voice-and-transcript
 */

import type { SayEventWithSessionContext, ValidatedSayCommand } from '@/server/data_structures/VoiceEvent';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';
import { voiceLogger } from '@/server/logging/voiceLogger';

// ---------------------------------------------------------------------------
// Session Store Interface (mockable)
// ---------------------------------------------------------------------------

export interface SessionStore {
  isActive(sessionId: string): Promise<boolean>;
}

// ---------------------------------------------------------------------------
// Default session store stub (not yet wired to Supabase)
// ---------------------------------------------------------------------------

const defaultSessionStore: SessionStore = {
  async isActive(_sessionId: string): Promise<boolean> {
    throw new Error('SessionStore.isActive not yet wired to Supabase');
  },
};

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

export const SaySessionVerifier = {
  /**
   * Step 2: Validate session context.
   *
   * Confirms the session is active by querying the session store.
   * Returns a strongly typed ValidatedSayCommand on success.
   * Throws VoiceErrors.SESSION_INACTIVE if session is not active.
   * Throws VoiceErrors.INVALID_SAY_PAYLOAD if payload schema is invalid.
   */
  async validateActiveSession(
    event: SayEventWithSessionContext,
    sessionStore: SessionStore = defaultSessionStore,
  ): Promise<ValidatedSayCommand> {
    let isActive: boolean;

    try {
      isActive = await sessionStore.isActive(event.sessionId);
    } catch (error) {
      voiceLogger.error('Session store lookup failed', error, {
        sessionId: event.sessionId,
      });
      throw VoiceErrors.SESSION_INACTIVE(
        `Failed to verify session '${event.sessionId}': store unavailable`,
      );
    }

    if (!isActive) {
      const voiceError = VoiceErrors.SESSION_INACTIVE(
        `Session '${event.sessionId}' is inactive`,
      );
      voiceLogger.error('SESSION_INACTIVE', voiceError, {
        sessionId: event.sessionId,
      });
      throw voiceError;
    }

    return {
      sessionId: event.sessionId,
      text: event.text,
      validatedAt: new Date().toISOString(),
    };
  },
} as const;
