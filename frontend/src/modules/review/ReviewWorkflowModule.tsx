'use client';

/**
 * ReviewWorkflowModule - Encapsulates the review approval UI and state management.
 *
 * Renders a list of content items for review, handles selection,
 * delegates approval to ReviewScreen component, and manages:
 *   - Item removal on successful approval
 *   - Workflow stage display after approval
 *   - Voice-based content editing from review screen
 *   - Error notifications on failure
 *   - Keeping user on review screen when errors occur
 *
 * Resource: ui-v3n6 (module)
 * Paths:
 *   - 329-approve-reviewed-content-and-advance-workflow
 *   - 330-edit-content-by-voice-from-review-screen
 */

import { useState } from 'react';
import ReviewScreen from '@/components/review/ReviewScreen';
import EditByVoiceComponent from '@/components/review/EditByVoiceComponent';
import type { EditByVoicePayload } from '@/components/review/EditByVoiceComponent';
import type { ApproveContentResponse } from '@/api_contracts/approveContent';
import { editByVoice } from '@/api_contracts/editByVoice';
import { frontendLogger } from '@/logging/index';

export interface ContentItem {
  id: string;
  title: string;
}

export interface ReviewWorkflowModuleProps {
  contentItems: ContentItem[];
  onWorkflowStageChange?: (_workflowStage: string) => void;
}

function readErrorCode(value: unknown): string | undefined {
  if (!value || typeof value !== 'object' || !('code' in value)) {
    return undefined;
  }

  const code = (value as { code?: unknown }).code;
  return typeof code === 'string' ? code : undefined;
}

export function ReviewWorkflowModule({
  contentItems: initialItems,
  onWorkflowStageChange,
}: ReviewWorkflowModuleProps) {
  const [contentItems, setContentItems] = useState<ContentItem[]>(initialItems);
  const [selectedContentId, setSelectedContentId] = useState<string | null>(null);
  const [workflowStage, setWorkflowStage] = useState<string | null>(null);
  const [uiError, setUiError] = useState<{ code?: string; message: string } | null>(null);
  const [editSuccess, setEditSuccess] = useState(false);

  const handleSelect = (id: string) => {
    setSelectedContentId(id);
    setUiError(null);
    setEditSuccess(false);
  };

  const handleApproved = (response: ApproveContentResponse) => {
    setUiError(null);

    // Remove approved item from list
    setContentItems((prev) => prev.filter((item) => item.id !== selectedContentId));

    // Update workflow stage
    setWorkflowStage(response.workflowStage);
    onWorkflowStageChange?.(response.workflowStage);

    // Clear selection
    setSelectedContentId(null);
  };

  const handleError = (error: Error) => {
    const code = readErrorCode(error);
    setUiError({
      code,
      message: error.message || 'An unexpected error occurred',
    });
  };

  // Path 330: Edit by voice handler
  const handleVoiceInstruction = async (payload: EditByVoicePayload) => {
    setUiError(null);
    setEditSuccess(false);

    try {
      await editByVoice({
        contentId: payload.contentId,
        instructionText: payload.instructionText,
      });

      setEditSuccess(true);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';

      frontendLogger.error(
        'Voice edit failed in ReviewWorkflowModule',
        err instanceof Error ? err : new Error(message),
        { module: 'ReviewWorkflowModule', action: 'handleVoiceInstruction' },
      );

      setUiError({
        code: readErrorCode(err),
        message,
      });
    }
  };

  const handleVoiceError = (error: Error) => {
    handleError(error);
  };

  return (
    <div data-testid="review-workflow-module" className="flex flex-col gap-4">
      <h2 className="font-serif text-xl font-bold">Content Review</h2>

      {/* Content item list */}
      <div className="flex flex-col gap-2">
        {contentItems.map((item) => (
          <button
            key={item.id}
            className={`p-3 rounded-md border text-left transition-colors ${
              selectedContentId === item.id
                ? 'border-primary bg-primary/10'
                : 'border-border hover:bg-accent/40'
            }`}
            onClick={() => handleSelect(item.id)}
            data-testid={`content-item-${item.id}`}
          >
            {item.title}
          </button>
        ))}
      </div>

      {/* Approval controls */}
      {selectedContentId && (
        <ReviewScreen
          selectedContentId={selectedContentId}
          onApproved={handleApproved}
          onError={handleError}
          showVoiceCapture={false}
        />
      )}

      {/* Edit by Voice controls (Path 330) */}
      {selectedContentId && (
        <EditByVoiceComponent
          contentId={selectedContentId}
          onVoiceInstruction={handleVoiceInstruction}
          onError={handleVoiceError}
        />
      )}

      {/* Edit success display */}
      {editSuccess && (
        <div
          data-testid="edit-success"
          className="rounded-md border border-primary/30 bg-primary/10 p-4"
        >
          <p className="text-sm text-primary">Content updated successfully via voice edit.</p>
        </div>
      )}

      {/* Error notification */}
      {uiError && (
        <div
          data-testid="error-notification"
          className="rounded-md border border-destructive/30 bg-destructive/10 p-4"
          role="alert"
        >
          <p className="text-sm text-destructive">{uiError.message}</p>
        </div>
      )}

      {/* Workflow stage display */}
      {workflowStage && (
        <div
          data-testid="workflow-stage"
          className="rounded-md border border-primary/30 bg-primary/10 p-4"
        >
          <p className="text-sm text-primary">
            Next stage: <span className="font-medium">{workflowStage}</span>
          </p>
        </div>
      )}
    </div>
  );
}
