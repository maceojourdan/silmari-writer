/**
 * Tests for ApproveDraftVerifier
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * TLA+ properties tested:
 * - TypeInvariant: Payload matches Zod schema
 * - ErrorConsistency: Missing fields produce validation error
 */

import { describe, it, expect } from 'vitest';
import {
  ApproveDraftPayloadSchema,
  validateApproveDraftPayload,
  type ApproveDraftPayload,
} from '../ApproveDraftVerifier';

describe('ApproveDraftVerifier', () => {
  const validPayload: ApproveDraftPayload = {
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
  };

  describe('TypeInvariant: Schema validation', () => {
    it('should accept a valid payload with all required fields', () => {
      const result = ApproveDraftPayloadSchema.safeParse(validPayload);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data).toEqual(validPayload);
      }
    });

    it('should enforce string types on all fields', () => {
      const numericPayload = {
        draftId: 123,
        resumeId: 'resume-001',
        jobId: 'job-001',
        questionId: 'question-001',
        voiceSessionId: 'session-001',
      };
      const result = ApproveDraftPayloadSchema.safeParse(numericPayload);
      expect(result.success).toBe(false);
    });
  });

  describe('ErrorConsistency: Missing fields', () => {
    it('should reject when draftId is missing', () => {
      const { draftId, ...payload } = validPayload;
      const result = ApproveDraftPayloadSchema.safeParse(payload);
      expect(result.success).toBe(false);
    });

    it('should reject when resumeId is missing', () => {
      const { resumeId, ...payload } = validPayload;
      const result = ApproveDraftPayloadSchema.safeParse(payload);
      expect(result.success).toBe(false);
    });

    it('should reject when jobId is missing', () => {
      const { jobId, ...payload } = validPayload;
      const result = ApproveDraftPayloadSchema.safeParse(payload);
      expect(result.success).toBe(false);
    });

    it('should reject when questionId is missing', () => {
      const { questionId, ...payload } = validPayload;
      const result = ApproveDraftPayloadSchema.safeParse(payload);
      expect(result.success).toBe(false);
    });

    it('should reject when voiceSessionId is missing', () => {
      const { voiceSessionId, ...payload } = validPayload;
      const result = ApproveDraftPayloadSchema.safeParse(payload);
      expect(result.success).toBe(false);
    });

    it('should reject empty string draftId', () => {
      const result = ApproveDraftPayloadSchema.safeParse({
        ...validPayload,
        draftId: '',
      });
      expect(result.success).toBe(false);
    });

    it('should reject completely empty payload', () => {
      const result = ApproveDraftPayloadSchema.safeParse({});
      expect(result.success).toBe(false);
    });
  });

  describe('validateApproveDraftPayload helper', () => {
    it('should return data on valid payload', () => {
      const result = validateApproveDraftPayload(validPayload);
      expect(result.success).toBe(true);
      if (result.success) {
        expect(result.data).toEqual(validPayload);
      }
    });

    it('should return error messages on invalid payload', () => {
      const result = validateApproveDraftPayload({});
      expect(result.success).toBe(false);
      if (!result.success) {
        expect(result.errors.length).toBeGreaterThan(0);
        expect(result.errors[0]).toContain('draftId');
      }
    });
  });
});
