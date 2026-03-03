/**
 * AuthAndValidationFilter - Validates authentication and request body
 * for the approve-story endpoint.
 *
 * Resource: api-p3e6 (filter)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

import { ApproveDraftPayloadSchema, type ApproveDraftPayload } from '@/verifiers/ApproveDraftVerifier';
import { StoryErrors } from '@/server/error_definitions/StoryErrors';
import { createHash } from 'crypto';

export interface AuthContext {
  userId: string;
  authenticated: boolean;
}

function hashIdentity(value: string): string {
  return createHash('sha256').update(value).digest('hex').slice(0, 16);
}

function decodeBase64Url(input: string): string {
  const normalized = input.replace(/-/g, '+').replace(/_/g, '/');
  const padding = normalized.length % 4 === 0 ? '' : '='.repeat(4 - (normalized.length % 4));
  return Buffer.from(`${normalized}${padding}`, 'base64').toString('utf8');
}

function tryDecodeJwtSub(token: string): string | null {
  const tokenParts = token.split('.');
  if (tokenParts.length < 2) {
    return null;
  }

  try {
    const payloadJson = decodeBase64Url(tokenParts[1]);
    const payload = JSON.parse(payloadJson) as { sub?: unknown };
    if (typeof payload.sub === 'string' && payload.sub.trim().length > 0) {
      return payload.sub;
    }
  } catch {
    // Fallback to token hashing when payload can't be decoded.
  }

  return null;
}

function deriveDeterministicUserId(token: string): string {
  const jwtSub = tryDecodeJwtSub(token);
  const identitySeed = jwtSub ?? `token:${token}`;
  return `user-${hashIdentity(identitySeed)}`;
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
      userId: deriveDeterministicUserId(token),
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
