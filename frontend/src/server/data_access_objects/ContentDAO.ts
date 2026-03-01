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

export const ContentDAO = {
  /**
   * Find a content entity by its ID.
   * Returns null if not found.
   */
  async findById(id: string): Promise<ContentEntity | null> {
    // Supabase: supabase.from('content').select('*').eq('id', id).single()
    throw new Error('ContentDAO.findById not yet wired to Supabase');
  },

  /**
   * Update content status and workflow stage, return the updated entity.
   * Throws on database failure.
   */
  async update(
    id: string,
    status: ContentStatus,
    workflowStage: WorkflowStage,
  ): Promise<ContentEntity> {
    // Supabase: supabase.from('content').update({ status, workflowStage, updatedAt: new Date().toISOString() }).eq('id', id).select().single()
    throw new Error('ContentDAO.update not yet wired to Supabase');
  },

  /**
   * Update content entity with revised body text.
   * Used by edit-by-voice to persist content modifications.
   * Returns the updated entity. Throws on database failure.
   *
   * Path: 330-edit-content-by-voice-from-review-screen
   */
  async updateContent(content: ContentEntity): Promise<ContentEntity> {
    // Supabase: supabase.from('content').update({ body: content.body, updatedAt: new Date().toISOString() }).eq('id', content.id).select().single()
    throw new Error('ContentDAO.updateContent not yet wired to Supabase');
  },
} as const;
