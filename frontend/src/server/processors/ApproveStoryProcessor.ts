/**
 * ApproveStoryProcessor - Aggregates approved draft and related artifacts
 * into a persistence package, then delegates to StoryPersistenceService.
 *
 * Resource: db-b7r2 (processor)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

import type {
  ApproveStoryCommand,
  PersistencePackage,
  PersistenceResult,
  StoryRecord,
  TruthCheck,
  DraftVersion,
  StoryMetrics,
} from '@/server/data_structures/StoryRecord';
import { StoryDAO } from '@/server/data_access_objects/StoryDAO';
import { StoryErrors } from '@/server/error_definitions/StoryErrors';
import { StoryPersistenceService } from '@/server/services/StoryPersistenceService';

export const ApproveStoryProcessor = {
  /**
   * Process an approved story command:
   * 1. Fetch all related entities via StoryDAO
   * 2. Validate all required entities exist
   * 3. Construct PersistencePackage
   * 4. Delegate to StoryPersistenceService
   */
  async process(command: ApproveStoryCommand): Promise<PersistenceResult> {
    // 1. Fetch all related entities concurrently
    const [
      draft,
      resume,
      job,
      question,
      session,
      truthChecks,
      draftVersions,
      metrics,
    ] = await Promise.all([
      StoryDAO.findDraftById(command.draftId),
      StoryDAO.findResumeById(command.resumeId),
      StoryDAO.findJobById(command.jobId),
      StoryDAO.findQuestionById(command.questionId),
      StoryDAO.findSessionById(command.voiceSessionId),
      StoryDAO.findTruthChecksByDraftId(command.draftId),
      StoryDAO.findDraftVersionsByDraftId(command.draftId),
      StoryDAO.findMetricsBySessionId(command.voiceSessionId),
    ]);

    // 2. Validate all required entities exist
    if (!draft) throw StoryErrors.RELATED_ENTITY_NOT_FOUND('draft');
    if (!resume) throw StoryErrors.RELATED_ENTITY_NOT_FOUND('resume');
    if (!job) throw StoryErrors.RELATED_ENTITY_NOT_FOUND('job');
    if (!question) throw StoryErrors.RELATED_ENTITY_NOT_FOUND('question');
    if (!session) throw StoryErrors.RELATED_ENTITY_NOT_FOUND('session');

    // 3. Construct the persistence package
    const storyRecord: StoryRecord = {
      draftId: command.draftId,
      resumeId: command.resumeId,
      jobId: command.jobId,
      questionId: command.questionId,
      voiceSessionId: command.voiceSessionId,
      userId: command.userId,
      status: 'FINALIZED',
      content: draft.content,
    };

    const storyMetrics: StoryMetrics = metrics ?? {
      wordCount: draft.content.split(/\s+/).length,
      sentenceCount: draft.content.split(/[.!?]+/).filter(Boolean).length,
      readabilityScore: 0,
      voiceSessionDurationMs: session.durationMs,
    };

    const pkg: PersistencePackage = {
      storyRecord,
      truthChecks: truthChecks as TruthCheck[],
      draftVersions: draftVersions as DraftVersion[],
      metrics: storyMetrics,
    };

    // 4. Delegate persistence
    return StoryPersistenceService.persist(pkg);
  },
} as const;
