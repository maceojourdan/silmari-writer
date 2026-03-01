/**
 * Tests for SessionUniquenessVerifier
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 311-reject-duplicate-session-initialization
 *
 * TLA+ properties tested:
 * - Reachability: Given activeSessionExists = true, verifier is called
 * - TypeInvariant: Returns void on pass, throws typed DomainError on failure
 * - ErrorConsistency: If active session exists → SESSION_ALREADY_ACTIVE error;
 *   if no active session → no error
 */

import { describe, it, expect } from 'vitest';
import { SessionUniquenessVerifier } from '../SessionUniquenessVerifier';
import { SessionError } from '@/server/error_definitions/SessionErrors';

describe('SessionUniquenessVerifier — Step 3: Validate session uniqueness constraint', () => {

  describe('Reachability: verifier is callable with boolean flag', () => {
    it('should be callable with activeSessionExists = true', () => {
      expect(() => SessionUniquenessVerifier.verify(true)).toThrow();
    });

    it('should be callable with activeSessionExists = false', () => {
      expect(() => SessionUniquenessVerifier.verify(false)).not.toThrow();
    });
  });

  describe('TypeInvariant: return type is void on pass, throws typed DomainError on failure', () => {
    it('should return void when no active session exists', () => {
      const result = SessionUniquenessVerifier.verify(false);
      expect(result).toBeUndefined();
    });

    it('should throw a SessionError when active session exists', () => {
      try {
        SessionUniquenessVerifier.verify(true);
        // Should not reach here
        expect.unreachable('Expected SessionUniquenessVerifier.verify(true) to throw');
      } catch (error) {
        expect(error).toBeInstanceOf(SessionError);
      }
    });
  });

  describe('ErrorConsistency: correct error code and properties', () => {
    it('should throw SESSION_ALREADY_ACTIVE when active session exists', () => {
      try {
        SessionUniquenessVerifier.verify(true);
        expect.unreachable('Expected to throw');
      } catch (error) {
        expect(error).toBeInstanceOf(SessionError);
        const sessionError = error as SessionError;
        expect(sessionError.code).toBe('SESSION_ALREADY_ACTIVE');
        expect(sessionError.statusCode).toBe(409);
        expect(sessionError.retryable).toBe(false);
        expect(sessionError.message).toBeDefined();
        expect(sessionError.message.length).toBeGreaterThan(0);
      }
    });

    it('should NOT throw when no active session exists', () => {
      expect(() => SessionUniquenessVerifier.verify(false)).not.toThrow();
    });
  });
});
