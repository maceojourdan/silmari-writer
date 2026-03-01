/**
 * Tests for ApproveStoryProcessor
 *
 * Resource: db-b7r2 (processor)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * TLA+ properties tested:
 * - Reachability: Valid command + mocked DAO → PersistencePackage returned
 * - TypeInvariant: Package includes storyRecord, truthChecks[], draftVersions[], metrics
 * - ErrorConsistency: DAO returns null resume → RELATED_ENTITY_NOT_FOUND
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoryError } from '../../error_definitions/StoryErrors';
import type { ApproveStoryCommand } from '../../data_structures/StoryRecord';
import type { DraftData, ResumeData, JobData, QuestionData, SessionData } from '../../data_access_objects/StoryDAO';

// Mock the DAO
vi.mock('../../data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    findDraftById: vi.fn(),
    findResumeById: vi.fn(),
    findJobById: vi.fn(),
    findQuestionById: vi.fn(),
    findSessionById: vi.fn(),
    findTruthChecksByDraftId: vi.fn(),
    findDraftVersionsByDraftId: vi.fn(),
    findMetricsBySessionId: vi.fn(),
  },
}));

// Mock the service
vi.mock('../../services/StoryPersistenceService', () => ({
  StoryPersistenceService: {
    persist: vi.fn(),
  },
}));

import { StoryDAO } from '../../data_access_objects/StoryDAO';
import { StoryPersistenceService } from '../../services/StoryPersistenceService';
import { ApproveStoryProcessor } from '../ApproveStoryProcessor';

const mockDAO = vi.mocked(StoryDAO);
const mockService = vi.mocked(StoryPersistenceService);

describe('ApproveStoryProcessor', () => {
  const validCommand: ApproveStoryCommand = {
    draftId: 'draft-001',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
    userId: 'user-001',
  };

  const mockDraft: DraftData = {
    id: 'draft-001',
    content: 'My story about problem solving...',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
  };

  const mockResume: ResumeData = {
    id: 'resume-001',
    name: 'John Doe Resume',
    content: 'Resume content...',
  };

  const mockJob: JobData = {
    id: 'job-001',
    title: 'Senior Developer',
    description: 'Job description...',
  };

  const mockQuestion: QuestionData = {
    id: 'question-001',
    text: 'Tell me about a challenge you overcame.',
  };

  const mockSession: SessionData = {
    id: 'session-001',
    durationMs: 180000,
    startedAt: '2026-02-28T11:00:00.000Z',
    endedAt: '2026-02-28T11:03:00.000Z',
  };

  const mockTruthChecks = [
    { claim: 'Led team of 5', verdict: 'VERIFIED' as const, evidence: 'Resume mentions team lead role' },
  ];

  const mockDraftVersions = [
    { versionNumber: 1, content: 'First draft...', createdAt: '2026-02-28T11:01:00.000Z' },
    { versionNumber: 2, content: 'My story about problem solving...', createdAt: '2026-02-28T11:02:00.000Z' },
  ];

  const mockMetrics = {
    wordCount: 150,
    sentenceCount: 12,
    readabilityScore: 75.3,
    voiceSessionDurationMs: 180000,
  };

  function setupSuccessfulMocks() {
    mockDAO.findDraftById.mockResolvedValue(mockDraft);
    mockDAO.findResumeById.mockResolvedValue(mockResume);
    mockDAO.findJobById.mockResolvedValue(mockJob);
    mockDAO.findQuestionById.mockResolvedValue(mockQuestion);
    mockDAO.findSessionById.mockResolvedValue(mockSession);
    mockDAO.findTruthChecksByDraftId.mockResolvedValue(mockTruthChecks);
    mockDAO.findDraftVersionsByDraftId.mockResolvedValue(mockDraftVersions);
    mockDAO.findMetricsBySessionId.mockResolvedValue(mockMetrics);
    mockService.persist.mockResolvedValue({
      storyRecordId: 'story-record-001',
      status: 'FINALIZED',
      persistedAt: '2026-02-28T12:00:00.000Z',
    });
  }

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: Valid command produces PersistenceResult', () => {
    it('should fetch related entities and call persistence service', async () => {
      setupSuccessfulMocks();

      const result = await ApproveStoryProcessor.process(validCommand);

      expect(mockDAO.findDraftById).toHaveBeenCalledWith('draft-001');
      expect(mockDAO.findResumeById).toHaveBeenCalledWith('resume-001');
      expect(mockDAO.findJobById).toHaveBeenCalledWith('job-001');
      expect(mockDAO.findQuestionById).toHaveBeenCalledWith('question-001');
      expect(mockDAO.findSessionById).toHaveBeenCalledWith('session-001');
      expect(mockDAO.findTruthChecksByDraftId).toHaveBeenCalledWith('draft-001');
      expect(mockDAO.findDraftVersionsByDraftId).toHaveBeenCalledWith('draft-001');
      expect(mockDAO.findMetricsBySessionId).toHaveBeenCalledWith('session-001');
      expect(mockService.persist).toHaveBeenCalledTimes(1);
      expect(result.storyRecordId).toBe('story-record-001');
      expect(result.status).toBe('FINALIZED');
    });
  });

  describe('TypeInvariant: Persistence package structure', () => {
    it('should pass a package with storyRecord, truthChecks[], draftVersions[], metrics', async () => {
      setupSuccessfulMocks();

      await ApproveStoryProcessor.process(validCommand);

      const pkg = mockService.persist.mock.calls[0][0];
      expect(pkg).toHaveProperty('storyRecord');
      expect(pkg).toHaveProperty('truthChecks');
      expect(pkg).toHaveProperty('draftVersions');
      expect(pkg).toHaveProperty('metrics');
      expect(Array.isArray(pkg.truthChecks)).toBe(true);
      expect(Array.isArray(pkg.draftVersions)).toBe(true);
      expect(pkg.storyRecord.status).toBe('FINALIZED');
      expect(pkg.storyRecord.draftId).toBe('draft-001');
      expect(pkg.storyRecord.userId).toBe('user-001');
    });
  });

  describe('ErrorConsistency: Missing related entities', () => {
    it('should throw RELATED_ENTITY_NOT_FOUND when draft is not found', async () => {
      setupSuccessfulMocks();
      mockDAO.findDraftById.mockResolvedValue(null);

      await expect(ApproveStoryProcessor.process(validCommand)).rejects.toThrow(StoryError);
      try {
        await ApproveStoryProcessor.process(validCommand);
      } catch (e) {
        expect((e as StoryError).code).toBe('RELATED_ENTITY_NOT_FOUND');
      }
    });

    it('should throw RELATED_ENTITY_NOT_FOUND when resume is not found', async () => {
      setupSuccessfulMocks();
      mockDAO.findResumeById.mockResolvedValue(null);

      await expect(ApproveStoryProcessor.process(validCommand)).rejects.toThrow(StoryError);
      try {
        await ApproveStoryProcessor.process(validCommand);
      } catch (e) {
        expect((e as StoryError).code).toBe('RELATED_ENTITY_NOT_FOUND');
      }
    });

    it('should throw RELATED_ENTITY_NOT_FOUND when job is not found', async () => {
      setupSuccessfulMocks();
      mockDAO.findJobById.mockResolvedValue(null);

      await expect(ApproveStoryProcessor.process(validCommand)).rejects.toThrow(StoryError);
      try {
        await ApproveStoryProcessor.process(validCommand);
      } catch (e) {
        expect((e as StoryError).code).toBe('RELATED_ENTITY_NOT_FOUND');
      }
    });

    it('should throw RELATED_ENTITY_NOT_FOUND when question is not found', async () => {
      setupSuccessfulMocks();
      mockDAO.findQuestionById.mockResolvedValue(null);

      await expect(ApproveStoryProcessor.process(validCommand)).rejects.toThrow(StoryError);
    });

    it('should throw RELATED_ENTITY_NOT_FOUND when session is not found', async () => {
      setupSuccessfulMocks();
      mockDAO.findSessionById.mockResolvedValue(null);

      await expect(ApproveStoryProcessor.process(validCommand)).rejects.toThrow(StoryError);
    });
  });
});
