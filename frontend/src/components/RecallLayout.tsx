/**
 * RecallLayout - Composes RecordButton and ProgressIndicator for the RECALL interface.
 *
 * Resource: ui-w8p2 (component)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * Wraps child components in an error boundary.
 * On error → renders RecallFallbackError and logs UI_COMPONENT_INIT_ERROR.
 */

'use client';

import { Component } from 'react';
import type { ErrorInfo, ReactNode } from 'react';
import RecordButton from './RecordButton';
import ProgressIndicator from './ProgressIndicator';
import { frontendLogger } from '@/logging/index';
import { UiErrors } from '@/server/error_definitions/UiErrors';
import type { RecallProgress } from '@/data_loaders/RecallProgressLoader';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface RecallLayoutProps {
  progress: RecallProgress;
  /** If true, forces an error to test the error boundary */
  forceError?: boolean;
}

// ---------------------------------------------------------------------------
// Error Boundary
// ---------------------------------------------------------------------------

interface ErrorBoundaryState {
  hasError: boolean;
}

class RecallErrorBoundary extends Component<
  { children: ReactNode },
  ErrorBoundaryState
> {
  constructor(props: { children: ReactNode }) {
    super(props);
    this.state = { hasError: false };
  }

  static getDerivedStateFromError(): ErrorBoundaryState {
    return { hasError: true };
  }

  componentDidCatch(error: Error, errorInfo: ErrorInfo): void {
    frontendLogger.error(
      'UI_COMPONENT_INIT_ERROR',
      error,
      { module: 'RecallLayout', action: 'componentDidCatch', componentStack: errorInfo.componentStack },
    );
  }

  render() {
    if (this.state.hasError) {
      return <RecallFallbackError />;
    }
    return this.props.children;
  }
}

// ---------------------------------------------------------------------------
// Fallback error component
// ---------------------------------------------------------------------------

function RecallFallbackError() {
  return (
    <div
      data-testid="recall-fallback-error"
      className="flex flex-col items-center justify-center p-8 text-center"
      role="alert"
    >
      <p className="text-lg font-medium text-red-600">
        Something went wrong loading the RECALL interface.
      </p>
      <p className="mt-2 text-sm text-gray-500">
        Please try refreshing the page.
      </p>
    </div>
  );
}

// ---------------------------------------------------------------------------
// Throwing component for error boundary testing
// ---------------------------------------------------------------------------

function ThrowingComponent(): ReactNode {
  throw new Error('Forced error for testing');
}

// ---------------------------------------------------------------------------
// Layout Component
// ---------------------------------------------------------------------------

export function RecallLayout({ progress, forceError = false }: RecallLayoutProps) {
  return (
    <RecallErrorBoundary>
      {forceError ? (
        <ThrowingComponent />
      ) : (
        <div className="flex flex-col items-center gap-8 p-6">
          <RecordButton prominent />
          <ProgressIndicator progress={progress} />
        </div>
      )}
    </RecallErrorBoundary>
  );
}
