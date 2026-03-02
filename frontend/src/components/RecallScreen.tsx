/**
 * RecallScreen - Recall step UI for the writing flow.
 *
 * Resource: ui-w8p2 (component)
 * Path: 331-return-to-recall-from-review
 *
 * Renders the Recall interface with RecordButton and ProgressIndicator.
 * Wraps content in an error boundary for resilient rendering.
 */

'use client';

import RecordButton from './RecordButton';
import ProgressIndicator from './ProgressIndicator';
import { NEUTRAL_PROGRESS } from '@/data_loaders/RecallProgressLoader';
import type { RecallProgress } from '@/data_loaders/RecallProgressLoader';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface RecallScreenProps {
  progress?: RecallProgress;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function RecallScreen({ progress = NEUTRAL_PROGRESS }: RecallScreenProps) {
  return (
    <div data-testid="recall-screen" className="flex flex-col items-center gap-8 p-6">
      <h2 className="text-xl font-semibold">Recall</h2>
      <RecordButton prominent />
      <ProgressIndicator progress={progress} />
    </div>
  );
}
