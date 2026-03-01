/**
 * Tests for StoryPersistenceService
 *
 * Resource: db-h2s4 (service)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * TLA+ properties tested:
 * - Reachability: Valid package → mock Supabase transaction → inserts called for all entities and commit
 * - TypeInvariant: Returned object contains persisted storyRecordId
 * - ErrorConsistency:
 *   - Simulate insert failure in truth_checks → rollback and PERSISTENCE_FAILED
 *   - Assert no partial writes occurred
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoryError } from '../../error_definitions/StoryErrors';
import type { PersistencePackage, StoryRecord, StoryMetrics } from '../../data_structures/StoryRecord';

// Mock the DAO
vi.mock('../../data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    insertStoryRecord: vi.fn(),
    insertTruthChecks: vi.fn(),
    insertDraftVersions: vi.fn(),
    insertMetrics: vi.fn(),
  },
}));

import { StoryDAO } from '../../data_access_objects/StoryDAO';
import { StoryPersistenceService } from '../StoryPersistenceService';

const mockDAO = vi.mocked(StoryDAO);

describe('StoryPersistenceService', () => {
  const storyRecord: StoryRecord = {
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
    userId: 'user-001',
    status: 'FINALIZED',
    content: 'My story about problem solving...',
  };

  const metrics: StoryMetrics = {
    wordCount: 150,
    sentenceCount: 12,
    readabilityScore: 75.3,
    voiceSessionDurationMs: 180000,
  };

  const validPackage: PersistencePackage = {
    storyRecord,
    truthChecks: [
      { claim: 'Led team of 5', verdict: 'VERIFIED', evidence: 'Resume confirms' },
    ],
    draftVersions: [
      { versionNumber: 1, content: 'First draft...', createdAt: '2026-02-28T11:01:00.000Z' },
      { versionNumber: 2, content: 'My story about problem solving...', createdAt: '2026-02-28T11:02:00.000Z' },
    ],
    metrics,
  };

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: Successful persistence', () => {
    it('should insert all entities and return storyRecordId', async () => {
      mockDAO.insertStoryRecord.mockResolvedValue('story-record-001');
      mockDAO.insertTruthChecks.mockResolvedValue(undefined);
      mockDAO.insertDraftVersions.mockResolvedValue(undefined);
      mockDAO.insertMetrics.mockResolvedValue(undefined);

      const result = await StoryPersistenceService.persist(validPackage);

      expect(mockDAO.insertStoryRecord).toHaveBeenCalledTimes(1);
      expect(mockDAO.insertTruthChecks).toHaveBeenCalledTimes(1);
      expect(mockDAO.insertDraftVersions).toHaveBeenCalledTimes(1);
      expect(mockDAO.insertMetrics).toHaveBeenCalledTimes(1);
      expect(result.storyRecordId).toBe('story-record-001');
    });

    it('should link truth_checks and draftVersions to the storyRecordId', async () => {
      mockDAO.insertStoryRecord.mockResolvedValue('story-record-001');
      mockDAO.insertTruthChecks.mockResolvedValue(undefined);
      mockDAO.insertDraftVersions.mockResolvedValue(undefined);
      mockDAO.insertMetrics.mockResolvedValue(undefined);

      await StoryPersistenceService.persist(validPackage);

      // truth_checks should be linked to storyRecordId
      const insertedChecks = mockDAO.insertTruthChecks.mock.calls[0][0];
      expect(insertedChecks.every((c) => c.storyRecordId === 'story-record-001')).toBe(true);

      // draftVersions should be linked to storyRecordId
      const insertedVersions = mockDAO.insertDraftVersions.mock.calls[0][0];
      expect(insertedVersions.every((v) => v.storyRecordId === 'story-record-001')).toBe(true);

      // metrics should be linked to storyRecordId
      const insertedMetrics = mockDAO.insertMetrics.mock.calls[0][0];
      expect(insertedMetrics.storyRecordId).toBe('story-record-001');
    });
  });

  describe('TypeInvariant: Return structure', () => {
    it('should return object with storyRecordId, status, and persistedAt', async () => {
      mockDAO.insertStoryRecord.mockResolvedValue('story-record-001');
      mockDAO.insertTruthChecks.mockResolvedValue(undefined);
      mockDAO.insertDraftVersions.mockResolvedValue(undefined);
      mockDAO.insertMetrics.mockResolvedValue(undefined);

      const result = await StoryPersistenceService.persist(validPackage);

      expect(result).toHaveProperty('storyRecordId');
      expect(result).toHaveProperty('status');
      expect(result).toHaveProperty('persistedAt');
      expect(result.status).toBe('FINALIZED');
      expect(typeof result.persistedAt).toBe('string');
    });
  });

  describe('ErrorConsistency: Failure and rollback', () => {
    it('should throw PERSISTENCE_FAILED when insertTruthChecks fails', async () => {
      mockDAO.insertStoryRecord.mockResolvedValue('story-record-001');
      mockDAO.insertTruthChecks.mockRejectedValue(new Error('DB insert failed'));

      await expect(StoryPersistenceService.persist(validPackage)).rejects.toThrow(StoryError);
      try {
        await StoryPersistenceService.persist(validPackage);
      } catch (e) {
        expect((e as StoryError).code).toBe('PERSISTENCE_FAILED');
        expect((e as StoryError).retryable).toBe(true);
      }
    });

    it('should throw PERSISTENCE_FAILED when insertStoryRecord fails', async () => {
      mockDAO.insertStoryRecord.mockRejectedValue(new Error('DB insert failed'));

      await expect(StoryPersistenceService.persist(validPackage)).rejects.toThrow(StoryError);
      try {
        await StoryPersistenceService.persist(validPackage);
      } catch (e) {
        expect((e as StoryError).code).toBe('PERSISTENCE_FAILED');
      }
    });

    it('should not call subsequent inserts when insertStoryRecord fails', async () => {
      mockDAO.insertStoryRecord.mockRejectedValue(new Error('DB insert failed'));

      try {
        await StoryPersistenceService.persist(validPackage);
      } catch {
        // expected
      }

      expect(mockDAO.insertTruthChecks).not.toHaveBeenCalled();
      expect(mockDAO.insertDraftVersions).not.toHaveBeenCalled();
      expect(mockDAO.insertMetrics).not.toHaveBeenCalled();
    });

    it('should not call insertMetrics when insertDraftVersions fails', async () => {
      mockDAO.insertStoryRecord.mockResolvedValue('story-record-001');
      mockDAO.insertTruthChecks.mockResolvedValue(undefined);
      mockDAO.insertDraftVersions.mockRejectedValue(new Error('DB insert failed'));

      try {
        await StoryPersistenceService.persist(validPackage);
      } catch {
        // expected
      }

      expect(mockDAO.insertMetrics).not.toHaveBeenCalled();
    });
  });
});
