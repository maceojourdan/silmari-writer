/**
 * FinalizeSessionService.validate.test.ts - Step 2: Validate session eligibility
 *
 * TLA+ Properties:
 * - Reachability: DAO returns ACTIVE session with requiredInputsComplete=true → validated session returned
 * - TypeInvariant: Returned object conforms to SessionForFinalization type
 * - ErrorConsistency: DAO returns null → SessionNotFoundError; state !== ACTIVE → InvalidSessionStateError;
 *   requiredInputsComplete=false → IncompleteSessionError
 *
 * Resource: db-h2s4 (service)
 * Path: 308-finalize-voice-session-and-persist-storyrecord
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';

// Mock only the DAO
vi.mock('../../data_access_objects/SessionStoryRecordDAO', () => ({
  SessionStoryRecordDAO: {
    findSessionById: vi.fn(),
    updateSessionState: vi.fn(),
    upsertStoryRecord: vi.fn(),
  },
}));

import { SessionStoryRecordDAO } from '../../data_access_objects/SessionStoryRecordDAO';
import { FinalizeSessionService } from '../FinalizeSessionService';

const mockDAO = vi.mocked(SessionStoryRecordDAO);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const activeSession = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  state: 'ACTIVE',
  requiredInputsComplete: true,
  responses: ['Response 1 about leadership', 'Response 2 about challenges'],
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('FinalizeSessionService.validateEligibility — Step 2: Validate session eligibility', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return validated session when state is ACTIVE and inputs complete', async () => {
      mockDAO.findSessionById.mockResolvedValue(activeSession);

      const result = await FinalizeSessionService.validateEligibility(activeSession.id);

      expect(result).toEqual(activeSession);
      expect(mockDAO.findSessionById).toHaveBeenCalledWith(activeSession.id);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object with expected SessionForFinalization shape', async () => {
      mockDAO.findSessionById.mockResolvedValue(activeSession);

      const result = await FinalizeSessionService.validateEligibility(activeSession.id);

      expect(result).toHaveProperty('id');
      expect(result).toHaveProperty('state');
      expect(result).toHaveProperty('requiredInputsComplete');
      expect(result).toHaveProperty('responses');
      expect(result.state).toBe('ACTIVE');
      expect(result.requiredInputsComplete).toBe(true);
      expect(Array.isArray(result.responses)).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw SESSION_NOT_FOUND when DAO returns null', async () => {
      mockDAO.findSessionById.mockResolvedValue(null);

      try {
        await FinalizeSessionService.validateEligibility('nonexistent-id');
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('SESSION_NOT_FOUND');
        expect((e as { statusCode: number }).statusCode).toBe(404);
      }
    });

    it('should throw INVALID_SESSION_STATE when state is not ACTIVE', async () => {
      mockDAO.findSessionById.mockResolvedValue({
        ...activeSession,
        state: 'DRAFT',
      });

      try {
        await FinalizeSessionService.validateEligibility(activeSession.id);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('INVALID_SESSION_STATE');
        expect((e as { statusCode: number }).statusCode).toBe(409);
      }
    });

    it('should throw INCOMPLETE_SESSION when requiredInputsComplete is false', async () => {
      mockDAO.findSessionById.mockResolvedValue({
        ...activeSession,
        requiredInputsComplete: false,
      });

      try {
        await FinalizeSessionService.validateEligibility(activeSession.id);
        expect.fail('Should have thrown');
      } catch (e: unknown) {
        expect((e as { code: string }).code).toBe('INCOMPLETE_SESSION');
        expect((e as { statusCode: number }).statusCode).toBe(422);
      }
    });
  });
});
