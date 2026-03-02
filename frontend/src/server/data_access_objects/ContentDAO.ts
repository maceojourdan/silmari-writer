/**
 * ContentDAO - Handles database persistence for content entity state transitions.
 *
 * Resource: db-d3w8 (data_access_object)
 * Paths:
 *   - 329-approve-reviewed-content-and-advance-workflow
 *   - 330-edit-content-by-voice-from-review-screen
 *
 * In production, each method performs Supabase queries against
 * the content table. For TDD, methods are designed to be mockable.
 */

import type { ContentEntity, ContentStatus, WorkflowStage } from '@/server/data_structures/ContentEntity';
import { supabase } from '@/lib/supabase';
import { ApprovalPersistenceError, ApprovalError } from '@/server/error_definitions/ApprovalErrors';
import { EditByVoicePersistenceError, EditByVoiceError } from '@/server/error_definitions/EditByVoiceErrors';

function mapContent(data: Record<string, unknown>): ContentEntity {
  return {
    id: data.id as string,
    body: data.body as string | undefined,
    status: data.status as ContentEntity['status'],
    workflowStage: (data.workflow_stage ?? data.workflowStage) as ContentEntity['workflowStage'],
    createdAt: (data.created_at ?? data.createdAt) as string,
    updatedAt: (data.updated_at ?? data.updatedAt) as string,
  };
}

export const ContentDAO = {
  async findById(id: string): Promise<ContentEntity | null> {
    try {
      const { data, error } = await supabase
        .from('content')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw ApprovalPersistenceError.PERSISTENCE_ERROR(`Failed to find content: ${error.message}`);
      if (!data) return null;
      return mapContent(data);
    } catch (err) {
      if (err instanceof ApprovalError) throw err;
      throw ApprovalPersistenceError.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async update(
    id: string,
    status: ContentStatus,
    workflowStage: WorkflowStage,
  ): Promise<ContentEntity> {
    try {
      const { data, error } = await supabase
        .from('content')
        .update({
          status,
          workflow_stage: workflowStage,
          updated_at: new Date().toISOString(),
        })
        .eq('id', id)
        .select()
        .single();

      if (error) throw ApprovalPersistenceError.PERSISTENCE_ERROR(`Failed to update content: ${error.message}`);
      if (!data) throw ApprovalPersistenceError.PERSISTENCE_ERROR('No data returned from content update');
      return mapContent(data);
    } catch (err) {
      if (err instanceof ApprovalError) throw err;
      throw ApprovalPersistenceError.PERSISTENCE_ERROR(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateContent(content: ContentEntity): Promise<ContentEntity> {
    try {
      const { data, error } = await supabase
        .from('content')
        .update({
          body: content.body,
          updated_at: new Date().toISOString(),
        })
        .eq('id', content.id)
        .select()
        .single();

      if (error) throw EditByVoicePersistenceError.PERSISTENCE_FAILURE(`Failed to update content body: ${error.message}`);
      if (!data) throw EditByVoicePersistenceError.PERSISTENCE_FAILURE('No data returned from content body update');
      return mapContent(data);
    } catch (err) {
      if (err instanceof EditByVoiceError) throw err;
      throw EditByVoicePersistenceError.PERSISTENCE_FAILURE(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
