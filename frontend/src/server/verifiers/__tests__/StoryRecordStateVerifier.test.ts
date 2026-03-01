/**
 * StoryRecordStateVerifier.test.ts - Step 4: Verify session state
 *
 * TLA+ Properties:
 * - Reachability: pass StoryRecord with state FINALIZED → expect failure result.
 * - TypeInvariant: assert verifier input type is StoryRecord, output type { allowed: boolean; reason?: string }
 * - ErrorConsistency: ensure failure reason equals SESSION_ALREADY_FINALIZED.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 309-reject-modifications-to-finalized-session
 */

import { describe, it, expect } from 'vitest';
import { StoryRecordStateVerifier } from '../StoryRecordStateVerifier';
import type { StoryRecord } from '@/server/data_structures/StoryRecord';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const baseFinalizedRecord: StoryRecord = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  draftId: 'draft-001',
  resumeId: 'resume-001',
  jobId: 'job-001',
  questionId: 'question-001',
  voiceSessionId: 'voice-001',
  userId: 'user-001',
  status: 'FINALIZED',
  content: 'A completed story about leadership.',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

const baseDraftRecord: StoryRecord = {
  ...baseFinalizedRecord,
  status: 'DRAFT',
};

const baseApprovedRecord: StoryRecord = {
  ...baseFinalizedRecord,
  status: 'APPROVED',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('StoryRecordStateVerifier — Step 4: Verify session state', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return failure result when StoryRecord state is FINALIZED', () => {
      const result = StoryRecordStateVerifier.canModify(baseFinalizedRecord);

      expect(result.allowed).toBe(false);
    });

    it('should return success result when StoryRecord state is DRAFT', () => {
      const result = StoryRecordStateVerifier.canModify(baseDraftRecord);

      expect(result.allowed).toBe(true);
    });

    it('should return success result when StoryRecord state is APPROVED', () => {
      const result = StoryRecordStateVerifier.canModify(baseApprovedRecord);

      expect(result.allowed).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object with allowed boolean and optional reason string', () => {
      const failureResult = StoryRecordStateVerifier.canModify(baseFinalizedRecord);

      expect(typeof failureResult.allowed).toBe('boolean');
      expect(typeof failureResult.reason).toBe('string');

      const successResult = StoryRecordStateVerifier.canModify(baseDraftRecord);

      expect(typeof successResult.allowed).toBe('boolean');
      expect(successResult.reason).toBeUndefined();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return reason SESSION_ALREADY_FINALIZED when state is FINALIZED', () => {
      const result = StoryRecordStateVerifier.canModify(baseFinalizedRecord);

      expect(result.allowed).toBe(false);
      expect(result.reason).toBe('SESSION_ALREADY_FINALIZED');
    });
  });
});
