/**
 * Full path integration test for approve-voice-session-and-persist-story-record
 *
 * Path: 293-approve-voice-session-and-persist-story-record
 * Terminal Condition Test
 *
 * Tests the complete flow:
 * AuthAndValidationFilter → ApproveStoryRequestHandler →
 * ApproveStoryProcessor → StoryPersistenceService → StoryDAO
 *
 * Seed test data, execute the full pipeline, and assert:
 * - StoryRecord created with FINALIZED status
 * - truth_checks persisted and linked
 * - draft_versions persisted
 * - metrics persisted
 * - Response contains storyRecordId
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { StoryError } from '../error_definitions/StoryErrors';
import type {
  StoryRecord,
  TruthCheck,
  DraftVersion,
  StoryMetrics,
} from '../data_structures/StoryRecord';
import type { DraftData, ResumeData, JobData, QuestionData, SessionData } from '../data_access_objects/StoryDAO';

// Mock the DAO at the lowest level
vi.mock('../data_access_objects/StoryDAO', () => ({
  StoryDAO: {
    findDraftById: vi.fn(),
    findResumeById: vi.fn(),
    findJobById: vi.fn(),
    findQuestionById: vi.fn(),
    findSessionById: vi.fn(),
    findTruthChecksByDraftId: vi.fn(),
    findDraftVersionsByDraftId: vi.fn(),
    findMetricsBySessionId: vi.fn(),
    insertStoryRecord: vi.fn(),
    insertTruthChecks: vi.fn(),
    insertDraftVersions: vi.fn(),
    insertMetrics: vi.fn(),
  },
}));

import { StoryDAO } from '../data_access_objects/StoryDAO';
import { AuthAndValidationFilter } from '../filters/AuthAndValidationFilter';
import { ApproveStoryRequestHandler } from '../request_handlers/ApproveStoryRequestHandler';

const mockDAO = vi.mocked(StoryDAO);

describe('Full Path Integration: approve-voice-session-and-persist-story-record', () => {
  // ===== Seed test data =====
  const seedDraft: DraftData = {
    id: 'draft-001',
    content: 'I led a team of five engineers to deliver a mission-critical project under tight deadlines. We overcame technical challenges through collaboration and creative problem-solving.',
    resumeId: 'resume-001',
    jobId: 'job-001',
    questionId: 'question-001',
    voiceSessionId: 'session-001',
  };

  const seedResume: ResumeData = {
    id: 'resume-001',
    name: 'Jane Smith Resume',
    content: 'Senior Software Engineer with 8 years experience. Led team of 5 engineers...',
  };

  const seedJob: JobData = {
    id: 'job-001',
    title: 'Engineering Manager',
    description: 'Lead a team of engineers building next-generation products.',
  };

  const seedQuestion: QuestionData = {
    id: 'question-001',
    text: 'Tell me about a time you led a team through a challenging project.',
  };

  const seedSession: SessionData = {
    id: 'session-001',
    durationMs: 240000,
    startedAt: '2026-02-28T10:00:00.000Z',
    endedAt: '2026-02-28T10:04:00.000Z',
  };

  const seedTruthChecks: TruthCheck[] = [
    { claim: 'Led a team of five engineers', verdict: 'VERIFIED', evidence: 'Resume states: Led team of 5 engineers' },
    { claim: 'Delivered mission-critical project', verdict: 'VERIFIED', evidence: 'Consistent with job history' },
    { claim: 'Under tight deadlines', verdict: 'UNVERIFIED', evidence: 'No timeline evidence in resume' },
  ];

  const seedDraftVersions: DraftVersion[] = [
    { versionNumber: 1, content: 'Initial voice capture...', createdAt: '2026-02-28T10:01:00.000Z' },
    { versionNumber: 2, content: 'Refined with truth checks...', createdAt: '2026-02-28T10:02:00.000Z' },
    { versionNumber: 3, content: seedDraft.content, createdAt: '2026-02-28T10:03:00.000Z' },
  ];

  const seedMetrics: StoryMetrics = {
    wordCount: 30,
    sentenceCount: 2,
    readabilityScore: 82.5,
    voiceSessionDurationMs: 240000,
  };

  // Track inserted data for assertions
  let insertedStoryRecord: StoryRecord | null = null;
  let insertedTruthChecks: TruthCheck[] = [];
  let insertedDraftVersions: DraftVersion[] = [];
  let insertedMetrics: StoryMetrics | null = null;

  beforeEach(() => {
    vi.clearAllMocks();
    insertedStoryRecord = null;
    insertedTruthChecks = [];
    insertedDraftVersions = [];
    insertedMetrics = null;

    // Seed DAO find methods
    mockDAO.findDraftById.mockResolvedValue(seedDraft);
    mockDAO.findResumeById.mockResolvedValue(seedResume);
    mockDAO.findJobById.mockResolvedValue(seedJob);
    mockDAO.findQuestionById.mockResolvedValue(seedQuestion);
    mockDAO.findSessionById.mockResolvedValue(seedSession);
    mockDAO.findTruthChecksByDraftId.mockResolvedValue(seedTruthChecks);
    mockDAO.findDraftVersionsByDraftId.mockResolvedValue(seedDraftVersions);
    mockDAO.findMetricsBySessionId.mockResolvedValue(seedMetrics);

    // Capture inserts
    mockDAO.insertStoryRecord.mockImplementation(async (record: StoryRecord) => {
      insertedStoryRecord = record;
      return 'story-record-final-001';
    });
    mockDAO.insertTruthChecks.mockImplementation(async (checks: TruthCheck[]) => {
      insertedTruthChecks = checks;
    });
    mockDAO.insertDraftVersions.mockImplementation(async (versions: DraftVersion[]) => {
      insertedDraftVersions = versions;
    });
    mockDAO.insertMetrics.mockImplementation(async (metrics: StoryMetrics) => {
      insertedMetrics = metrics;
    });
  });

  it('should process full path: authenticate → validate → assemble → persist → return', async () => {
    // 1. Authenticate
    const auth = AuthAndValidationFilter.authenticate('Bearer test-token-12345');
    expect(auth.authenticated).toBe(true);

    // 2. Validate body
    const validBody = {
      draftId: 'draft-001',
      resumeId: 'resume-001',
      jobId: 'job-001',
      questionId: 'question-001',
      voiceSessionId: 'session-001',
    };
    const validated = AuthAndValidationFilter.validateBody(validBody);
    expect(validated).toEqual(validBody);

    // 3. Handle request (transforms, processes, persists)
    const result = await ApproveStoryRequestHandler.handle(validated, auth);

    // 4. Assert StoryRecord created with FINALIZED status
    expect(insertedStoryRecord).not.toBeNull();
    expect(insertedStoryRecord!.status).toBe('FINALIZED');
    expect(insertedStoryRecord!.draftId).toBe('draft-001');
    expect(insertedStoryRecord!.userId).toContain('user-');
    expect(insertedStoryRecord!.content).toBe(seedDraft.content);

    // 5. Assert truth_checks persisted and linked
    expect(insertedTruthChecks.length).toBe(3);
    expect(insertedTruthChecks.every((c) => c.storyRecordId === 'story-record-final-001')).toBe(true);
    expect(insertedTruthChecks[0].claim).toBe('Led a team of five engineers');
    expect(insertedTruthChecks[0].verdict).toBe('VERIFIED');

    // 6. Assert draft_versions persisted
    expect(insertedDraftVersions.length).toBe(3);
    expect(insertedDraftVersions.every((v) => v.storyRecordId === 'story-record-final-001')).toBe(true);
    expect(insertedDraftVersions[0].versionNumber).toBe(1);
    expect(insertedDraftVersions[2].content).toBe(seedDraft.content);

    // 7. Assert metrics persisted
    expect(insertedMetrics).not.toBeNull();
    expect(insertedMetrics!.storyRecordId).toBe('story-record-final-001');
    expect(insertedMetrics!.wordCount).toBe(30);
    expect(insertedMetrics!.voiceSessionDurationMs).toBe(240000);

    // 8. Assert response contains storyRecordId
    expect(result.storyRecordId).toBe('story-record-final-001');
    expect(result.status).toBe('FINALIZED');
    expect(result.persistedAt).toBeDefined();
  });

  it('should fail gracefully when authentication is missing', () => {
    expect(() => AuthAndValidationFilter.authenticate(undefined)).toThrow(StoryError);
    try {
      AuthAndValidationFilter.authenticate(undefined);
    } catch (e) {
      expect((e as StoryError).code).toBe('UNAUTHORIZED');
      expect((e as StoryError).statusCode).toBe(401);
    }
  });

  it('should fail gracefully when validation fails', () => {
    expect(() => AuthAndValidationFilter.validateBody({ draftId: 'only-one-field' })).toThrow(StoryError);
    try {
      AuthAndValidationFilter.validateBody({ draftId: 'only-one-field' });
    } catch (e) {
      expect((e as StoryError).code).toBe('VALIDATION_ERROR');
    }
  });

  it('should fail when related entity is not found during processing', async () => {
    mockDAO.findResumeById.mockResolvedValue(null);

    const auth = AuthAndValidationFilter.authenticate('Bearer test-token-12345');
    const validated = AuthAndValidationFilter.validateBody({
      draftId: 'draft-001',
      resumeId: 'resume-001',
      jobId: 'job-001',
      questionId: 'question-001',
      voiceSessionId: 'session-001',
    });

    await expect(ApproveStoryRequestHandler.handle(validated, auth)).rejects.toThrow(StoryError);
    try {
      await ApproveStoryRequestHandler.handle(validated, auth);
    } catch (e) {
      expect((e as StoryError).code).toBe('RELATED_ENTITY_NOT_FOUND');
    }
  });

  it('should fail when database persistence fails', async () => {
    mockDAO.insertStoryRecord.mockRejectedValue(new Error('Connection refused'));

    const auth = AuthAndValidationFilter.authenticate('Bearer test-token-12345');
    const validated = AuthAndValidationFilter.validateBody({
      draftId: 'draft-001',
      resumeId: 'resume-001',
      jobId: 'job-001',
      questionId: 'question-001',
      voiceSessionId: 'session-001',
    });

    await expect(ApproveStoryRequestHandler.handle(validated, auth)).rejects.toThrow(StoryError);
    try {
      await ApproveStoryRequestHandler.handle(validated, auth);
    } catch (e) {
      expect((e as StoryError).code).toBe('PERSISTENCE_FAILED');
      expect((e as StoryError).retryable).toBe(true);
    }
  });
});
