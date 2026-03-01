/**
 * step5.enableDrafting.test.ts - Step 5: Enable drafting process
 *
 * TLA+ Properties:
 * - Reachability: All claims verified → session.state === 'DRAFT_ENABLED'
 * - TypeInvariant: Returned state is a valid SessionState enum value
 * - ErrorConsistency: One claim not verified → VerificationStateInconsistentError, state unchanged
 *
 * Resource: db-h2s4 (service)
 * Path: 321-verify-key-claims-via-voice-or-sms
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { VerificationError } from '@/server/error_definitions/VerificationErrors';
import type { Session } from '@/server/data_structures/Session';
import type { ClaimRecord } from '@/server/data_structures/ClaimRecord';

// Mock the verification logger
vi.mock('@/server/logging/verificationLogger', () => ({
  verificationLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// Mock the ClaimDAO
vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getUnverifiedClaimsBySession: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    updateStatusToVerified: vi.fn(),
  },
}));

// Mock the VerificationRequestDAO
vi.mock('@/server/data_access_objects/VerificationRequestDAO', () => ({
  VerificationRequestDAO: {
    create: vi.fn(),
    findByToken: vi.fn(),
    findBySessionId: vi.fn(),
    updateStatus: vi.fn(),
    logDeliveryAttempt: vi.fn(),
  },
}));

// Mock the SessionDAO
vi.mock('@/server/data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
    createSession: vi.fn(),
    createStoryRecord: vi.fn(),
    deleteSession: vi.fn(),
    findAnswerSessionById: vi.fn(),
    findStoryRecordBySessionId: vi.fn(),
    updateSessionAndStoryRecord: vi.fn(),
    saveSlots: vi.fn(),
    updateAnswerSessionState: vi.fn(),
  },
}));

import { VerificationService } from '../VerificationService';
import { ClaimDAO } from '@/server/data_access_objects/ClaimDAO';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';

const mockClaimDAO = vi.mocked(ClaimDAO);
const mockSessionDAO = vi.mocked(SessionDAO);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const sessionId = 'session-321-step5';

function createDraftEnabledSession(): Session {
  return {
    id: sessionId,
    state: 'DRAFT_ENABLED',
    requiredInputsComplete: true,
    createdAt: now,
    updatedAt: now,
  };
}

function createUnverifiedClaim(): ClaimRecord {
  return {
    id: 'claim-unverified',
    sessionId,
    category: 'metrics',
    status: 'unverified',
    contactPhone: '+15551234567',
    contactMethod: 'sms',
    content: 'Revenue +40%',
    verifiedAt: null,
    createdAt: now,
    updatedAt: now,
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationService.enableDrafting — Step 5: Enable drafting process', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return session with state DRAFT_ENABLED when all claims are verified', async () => {
      // No unverified claims remain
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([]);
      mockSessionDAO.updateState.mockResolvedValue(createDraftEnabledSession());

      const result = await VerificationService.enableDrafting(sessionId);

      expect(result.state).toBe('DRAFT_ENABLED');
    });

    it('should call SessionDAO.updateState with DRAFT_ENABLED', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([]);
      mockSessionDAO.updateState.mockResolvedValue(createDraftEnabledSession());

      await VerificationService.enableDrafting(sessionId);

      expect(mockSessionDAO.updateState).toHaveBeenCalledWith(sessionId, 'DRAFT_ENABLED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return state as a string matching SessionState enum', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([]);
      mockSessionDAO.updateState.mockResolvedValue(createDraftEnabledSession());

      const result = await VerificationService.enableDrafting(sessionId);

      expect(typeof result.state).toBe('string');
      expect(['DRAFT', 'DRAFT_ENABLED', 'ACTIVE', 'FINALIZE']).toContain(result.state);
    });

    it('should return a Session object with required fields', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([]);
      mockSessionDAO.updateState.mockResolvedValue(createDraftEnabledSession());

      const result = await VerificationService.enableDrafting(sessionId);

      expect(result).toHaveProperty('id');
      expect(result).toHaveProperty('state');
      expect(result).toHaveProperty('createdAt');
      expect(result).toHaveProperty('updatedAt');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw VerificationStateInconsistentError when unverified claims remain', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([createUnverifiedClaim()]);

      try {
        await VerificationService.enableDrafting(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(VerificationError);
        expect((e as VerificationError).code).toBe('VERIFICATION_STATE_INCONSISTENT');
      }
    });

    it('should NOT call SessionDAO.updateState when unverified claims remain', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([createUnverifiedClaim()]);

      try {
        await VerificationService.enableDrafting(sessionId);
      } catch {
        // expected
      }

      expect(mockSessionDAO.updateState).not.toHaveBeenCalled();
    });

    it('should include unverified count in error message', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([
        createUnverifiedClaim(),
        { ...createUnverifiedClaim(), id: 'claim-2', category: 'scope' },
      ]);

      try {
        await VerificationService.enableDrafting(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as VerificationError).message).toContain('2');
      }
    });

    it('should have statusCode 409 on VerificationStateInconsistentError', async () => {
      mockClaimDAO.getUnverifiedClaimsBySession.mockResolvedValue([createUnverifiedClaim()]);

      try {
        await VerificationService.enableDrafting(sessionId);
        expect.fail('Should have thrown');
      } catch (e) {
        expect((e as VerificationError).statusCode).toBe(409);
      }
    });
  });
});
