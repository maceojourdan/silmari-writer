/**
 * confirmStory - Typed API contract for the story confirmation endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 313-confirm-aligned-story-selection
 */

import { z } from 'zod';
import {
  ConfirmStoryRequestSchema,
  ConfirmStoryResponseSchema,
} from '@/server/data_structures/ConfirmStory';
import type {
  ConfirmStoryRequest,
  ConfirmStoryResponse,
} from '@/server/data_structures/ConfirmStory';

/**
 * Send a story confirmation request to the backend.
 *
 * POST /api/story/confirm
 *
 * @throws Error on network failure, server error, or response validation failure
 */
export async function confirmStory(
  payload: ConfirmStoryRequest,
): Promise<ConfirmStoryResponse> {
  // Validate request payload before sending
  const requestValidation = ConfirmStoryRequestSchema.safeParse(payload);
  if (!requestValidation.success) {
    const details = requestValidation.error.issues
      .map((i) => i.message)
      .join(', ');
    throw new Error(`Invalid confirmation request: ${details}`);
  }

  const response = await fetch('/api/story/confirm', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(requestValidation.data),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Story confirmation failed with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = ConfirmStoryResponseSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from story confirmation: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
    );
  }

  return parsed.data;
}
