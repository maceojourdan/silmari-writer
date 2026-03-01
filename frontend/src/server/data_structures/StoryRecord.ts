/**
 * StoryRecord - TypeScript interfaces matching the Postgres schema
 * for story_records, truth_checks, draft_versions, and metrics.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 293-approve-voice-session-and-persist-story-record
 */

export type StoryStatus = 'DRAFT' | 'APPROVED' | 'FINALIZED';

export interface StoryRecord {
  id?: string;
  draftId: string;
  resumeId: string;
  jobId: string;
  questionId: string;
  voiceSessionId: string;
  userId: string;
  status: StoryStatus;
  content: string;
  createdAt?: string;
  updatedAt?: string;
}

export interface TruthCheck {
  id?: string;
  storyRecordId?: string;
  claim: string;
  verdict: 'VERIFIED' | 'UNVERIFIED' | 'DISPUTED';
  evidence: string;
  checkedAt?: string;
}

export interface DraftVersion {
  id?: string;
  storyRecordId?: string;
  versionNumber: number;
  content: string;
  createdAt?: string;
}

export interface StoryMetrics {
  id?: string;
  storyRecordId?: string;
  wordCount: number;
  sentenceCount: number;
  readabilityScore: number;
  voiceSessionDurationMs: number;
  createdAt?: string;
}

/**
 * PersistencePackage — aggregated entity package for transactional write.
 * Assembled by ApproveStoryProcessor, consumed by StoryPersistenceService.
 */
export interface PersistencePackage {
  storyRecord: StoryRecord;
  truthChecks: TruthCheck[];
  draftVersions: DraftVersion[];
  metrics: StoryMetrics;
}

/**
 * ApproveStoryCommand — validated command sent from request handler to processor.
 */
export interface ApproveStoryCommand {
  draftId: string;
  resumeId: string;
  jobId: string;
  questionId: string;
  voiceSessionId: string;
  userId: string;
}

/**
 * PersistenceResult — returned after successful transactional write.
 */
export interface PersistenceResult {
  storyRecordId: string;
  status: StoryStatus;
  persistedAt: string;
}
