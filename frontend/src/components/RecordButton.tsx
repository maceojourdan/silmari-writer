/**
 * RecordButton - Prominent record button for the RECALL interface.
 *
 * Resource: ui-w8p2 (component)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * Renders a large, enabled record button with prominent Tailwind styling.
 * Falls back to default styling on error and logs via frontendLogger.
 */

'use client';

import { frontendLogger } from '@/logging/index';
import { UiErrors } from '@/server/error_definitions/UiErrors';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface RecordButtonProps {
  prominent?: boolean;
  disabled?: boolean;
  onClick?: () => void;
  label?: string;
  ariaLabel?: string;
}

// ---------------------------------------------------------------------------
// Styling
// ---------------------------------------------------------------------------

const PROMINENT_CLASSES =
  'rounded-full w-24 h-24 text-3xl sm:w-32 sm:h-32 sm:text-4xl border border-destructive-border bg-destructive text-white shadow-destructive-border font-bold transition-colors hover:bg-destructive/90 focus:outline-none focus:ring-4 focus:ring-ring/50 disabled:cursor-not-allowed disabled:opacity-50';

const DEFAULT_CLASSES =
  'text-lg rounded-full w-16 h-16 border border-destructive-border bg-destructive text-white shadow-destructive-border font-medium transition-colors hover:bg-destructive/90 focus:outline-none focus:ring-2 focus:ring-ring/50 disabled:cursor-not-allowed disabled:opacity-50';

function getButtonClasses(prominent: boolean): string {
  try {
    return prominent ? PROMINENT_CLASSES : DEFAULT_CLASSES;
  } catch (error) {
    frontendLogger.error(
      'UI_RECORD_BUTTON_STYLE_ERROR',
      error instanceof Error ? error : UiErrors.RecordButtonStyleError(),
      { module: 'RecordButton', action: 'getButtonClasses' },
    );
    return DEFAULT_CLASSES;
  }
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function RecordButton({
  prominent = true,
  disabled = false,
  onClick,
  label = 'Record',
  ariaLabel = 'Record',
}: RecordButtonProps) {
  const classes = getButtonClasses(prominent);

  return (
    <button
      data-testid="record-button"
      type="button"
      className={classes}
      disabled={disabled}
      onClick={onClick}
      aria-label={ariaLabel}
    >
      {label}
    </button>
  );
}
