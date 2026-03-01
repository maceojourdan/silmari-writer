/**
 * ProgressIndicator - Displays progress for Anchors, Actions, and Outcomes.
 *
 * Resource: ui-w8p2 (component)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * Renders completion status for the three RECALL dimensions.
 */

'use client';

import type { RecallProgress } from '@/data_loaders/RecallProgressLoader';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface ProgressIndicatorProps {
  progress: RecallProgress;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function ProgressIndicator({ progress }: ProgressIndicatorProps) {
  return (
    <div data-testid="progress-indicator" className="flex flex-col gap-2 p-4">
      <div className="flex items-center justify-between" data-testid="progress-anchors">
        <span className="text-sm font-medium text-gray-700">Anchors</span>
        <span className="text-lg font-bold text-gray-900">{progress.anchors}</span>
      </div>
      <div className="flex items-center justify-between" data-testid="progress-actions">
        <span className="text-sm font-medium text-gray-700">Actions</span>
        <span className="text-lg font-bold text-gray-900">{progress.actions}</span>
      </div>
      <div className="flex items-center justify-between" data-testid="progress-outcomes">
        <span className="text-sm font-medium text-gray-700">Outcomes</span>
        <span className="text-lg font-bold text-gray-900">{progress.outcomes}</span>
      </div>
    </div>
  );
}
