/**
 * KpiModule - Encapsulates primary KPI flow state management.
 *
 * Resource: ui-v3n6 (module)
 * Path: 339-record-primary-kpi-analytics-event
 */

export type SubmissionStatus = 'idle' | 'submitting' | 'success' | 'error';

export interface KpiModuleState {
  userId: string;
  actionType: string;
  metadata: Record<string, unknown>;
  submissionStatus: SubmissionStatus;
  error: string | null;
  recordId: string | null;
  analyticsEmitted: boolean;
}

export class KpiModule {
  private state: KpiModuleState;

  constructor(userId: string, actionType: string, metadata: Record<string, unknown> = {}) {
    this.state = {
      userId,
      actionType,
      metadata,
      submissionStatus: 'idle',
      error: null,
      recordId: null,
      analyticsEmitted: false,
    };
  }

  getState(): KpiModuleState { return this.state; }
  getUserId(): string { return this.state.userId; }
  getActionType(): string { return this.state.actionType; }
  isSubmitting(): boolean { return this.state.submissionStatus === 'submitting'; }

  startSubmission(): void {
    this.state = { ...this.state, submissionStatus: 'submitting', error: null };
  }

  completeSubmission(recordId: string, analyticsEmitted: boolean): void {
    this.state = {
      ...this.state,
      submissionStatus: 'success',
      recordId,
      analyticsEmitted,
      error: null,
    };
  }

  handleError(errorMessage: string): void {
    this.state = { ...this.state, submissionStatus: 'error', error: errorMessage };
  }

  resetSubmission(): void {
    this.state = { ...this.state, submissionStatus: 'idle', error: null };
  }
}
