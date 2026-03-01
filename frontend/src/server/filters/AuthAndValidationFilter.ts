/**
 * AuthAndValidationFilter - Validates authentication and request body
 * for the approve-story endpoint.
 *
 * Resource: api-p3e6 (filter)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

import { ApproveDraftPayloadSchema, type ApproveDraftPayload } from '@/verifiers/ApproveDraftVerifier';
import { StoryErrors, StoryError } from '@/server/error_definitions/StoryErrors';

export interface AuthContext {
  userId: string;
  authenticated: boolean;
}

export const AuthAndValidationFilter = {
  /**
   * Authenticate request via auth header.
   * In production this would validate against Supabase Auth.
   * For now, extracts user context from Bearer token.
   */
  authenticate(authHeader: string | undefined | null): AuthContext {
    if (!authHeader || authHeader.trim() === '') {
      throw StoryErrors.UNAUTHORIZED('Missing or empty authorization header');
    }

    // In production: validate JWT via Supabase Auth
    // For now, extract a userId from the token (stub implementation)
    const token = authHeader.replace(/^Bearer\s+/i, '');
    if (!token) {
      throw StoryErrors.UNAUTHORIZED('Invalid authorization token');
    }

    return {
      userId: `user-${token.substring(0, 8)}`,
      authenticated: true,
    };
  },

  /**
   * Validate the request body against the ApproveDraft Zod schema.
   */
  validateBody(body: unknown): ApproveDraftPayload {
    const result = ApproveDraftPayloadSchema.safeParse(body);
    if (!result.success) {
      const details = result.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      throw StoryErrors.VALIDATION_ERROR(`Invalid request payload: ${details}`);
    }
    return result.data;
  },
} as const;
