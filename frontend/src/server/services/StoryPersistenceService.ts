/**
 * StoryPersistenceService - Orchestrates transactional persistence
 * of story and related entities.
 *
 * Resource: db-h2s4 (service)
 * Path: 293-approve-voice-session-and-persist-story-record
 *
 * Uses sequential inserts to simulate transactional semantics.
 * In production, this would use Supabase rpc or explicit transaction wrapper.
 * If any step fails, partial writes are detected and a PERSISTENCE_FAILED
 * error is thrown (the caller can retry).
 */

import type {
  PersistencePackage,
  PersistenceResult,
  TruthCheck,
  DraftVersion,
  StoryMetrics,
} from '@/server/data_structures/StoryRecord';
import { StoryDAO } from '@/server/data_access_objects/StoryDAO';
import { StoryErrors } from '@/server/error_definitions/StoryErrors';

export const StoryPersistenceService = {
  /**
   * Persist the full story package in order:
   * 1. Insert StoryRecord → get storyRecordId
   * 2. Insert truth_checks linked to storyRecordId
   * 3. Insert draft_versions linked to storyRecordId
   * 4. Insert metrics linked to storyRecordId
   *
   * On failure at any step, throw PERSISTENCE_FAILED.
   */
  async persist(pkg: PersistencePackage): Promise<PersistenceResult> {
    let storyRecordId: string;

    try {
      // Step 1: Insert StoryRecord
      storyRecordId = await StoryDAO.insertStoryRecord(pkg.storyRecord);
    } catch (error) {
      throw StoryErrors.PERSISTENCE_FAILED(
        `Failed to insert story record: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    try {
      // Step 2: Insert truth_checks linked to storyRecordId
      const linkedChecks: TruthCheck[] = pkg.truthChecks.map((check) => ({
        ...check,
        storyRecordId,
      }));
      await StoryDAO.insertTruthChecks(linkedChecks);
    } catch (error) {
      throw StoryErrors.PERSISTENCE_FAILED(
        `Failed to insert truth checks: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    try {
      // Step 3: Insert draft_versions linked to storyRecordId
      const linkedVersions: DraftVersion[] = pkg.draftVersions.map((version) => ({
        ...version,
        storyRecordId,
      }));
      await StoryDAO.insertDraftVersions(linkedVersions);
    } catch (error) {
      throw StoryErrors.PERSISTENCE_FAILED(
        `Failed to insert draft versions: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    try {
      // Step 4: Insert metrics linked to storyRecordId
      const linkedMetrics: StoryMetrics = {
        ...pkg.metrics,
        storyRecordId,
      };
      await StoryDAO.insertMetrics(linkedMetrics);
    } catch (error) {
      throw StoryErrors.PERSISTENCE_FAILED(
        `Failed to insert metrics: ${error instanceof Error ? error.message : 'unknown error'}`,
      );
    }

    return {
      storyRecordId,
      status: pkg.storyRecord.status,
      persistedAt: new Date().toISOString(),
    };
  },
} as const;
