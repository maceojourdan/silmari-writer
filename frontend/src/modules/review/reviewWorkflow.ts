/**
 * reviewWorkflow - Module state management for the review approval workflow.
 *
 * Resource: ui-v3n6 (module)
 * Path: 329-approve-reviewed-content-and-advance-workflow
 *
 * Manages the state transitions for review workflow:
 * - Tracks content items under review
 * - Handles approval state updates
 * - Manages workflow stage progression
 * - Handles error states
 */

import type { ApproveContentResponse } from '@/api_contracts/approveContent';

// ---------------------------------------------------------------------------
// State Types
// ---------------------------------------------------------------------------

export interface ReviewWorkflowState {
  contentItems: ReviewContentItem[];
  selectedContentId: string | null;
  workflowStage: string | null;
  error: ReviewWorkflowError | null;
  isSubmitting: boolean;
}

export interface ReviewContentItem {
  id: string;
  title: string;
}

export interface ReviewWorkflowError {
  code?: string;
  message: string;
}

// ---------------------------------------------------------------------------
// Actions
// ---------------------------------------------------------------------------

export type ReviewWorkflowAction =
  | { type: 'SELECT_CONTENT'; contentId: string }
  | { type: 'APPROVE_START' }
  | { type: 'APPROVE_SUCCESS'; response: ApproveContentResponse }
  | { type: 'APPROVE_ERROR'; error: ReviewWorkflowError }
  | { type: 'CLEAR_ERROR' };

// ---------------------------------------------------------------------------
// Reducer
// ---------------------------------------------------------------------------

export function reviewWorkflowReducer(
  state: ReviewWorkflowState,
  action: ReviewWorkflowAction,
): ReviewWorkflowState {
  switch (action.type) {
    case 'SELECT_CONTENT':
      return {
        ...state,
        selectedContentId: action.contentId,
        error: null,
      };

    case 'APPROVE_START':
      return {
        ...state,
        isSubmitting: true,
        error: null,
      };

    case 'APPROVE_SUCCESS':
      return {
        ...state,
        isSubmitting: false,
        contentItems: state.contentItems.filter(
          (item) => item.id !== state.selectedContentId,
        ),
        selectedContentId: null,
        workflowStage: action.response.workflowStage,
        error: null,
      };

    case 'APPROVE_ERROR':
      return {
        ...state,
        isSubmitting: false,
        error: action.error,
      };

    case 'CLEAR_ERROR':
      return {
        ...state,
        error: null,
      };

    default:
      return state;
  }
}

// ---------------------------------------------------------------------------
// Initial State Factory
// ---------------------------------------------------------------------------

export function createInitialState(
  contentItems: ReviewContentItem[],
): ReviewWorkflowState {
  return {
    contentItems,
    selectedContentId: null,
    workflowStage: null,
    error: null,
    isSubmitting: false,
  };
}
