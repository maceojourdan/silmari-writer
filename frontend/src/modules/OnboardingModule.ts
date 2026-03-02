/**
 * OnboardingModule - Encapsulates onboarding flow state management.
 *
 * Resource: ui-v3n6 (module)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * Manages:
 *   - Current onboarding step state
 *   - Submission status (idle, submitting, success, error)
 *   - Error state with recovery
 */

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type SubmissionStatus = 'idle' | 'submitting' | 'success' | 'error';

export interface OnboardingState {
  userId: string;
  currentStep: number;
  submissionStatus: SubmissionStatus;
  error: string | null;
  completedSteps: number[];
}

// ---------------------------------------------------------------------------
// Module
// ---------------------------------------------------------------------------

export class OnboardingModule {
  private state: OnboardingState;

  constructor(userId: string, currentStep: number = 1) {
    this.state = {
      userId,
      currentStep,
      submissionStatus: 'idle',
      error: null,
      completedSteps: [],
    };
  }

  // -------------------------------------------------------------------------
  // Getters
  // -------------------------------------------------------------------------

  getState(): OnboardingState {
    return this.state;
  }

  getUserId(): string {
    return this.state.userId;
  }

  getCurrentStep(): number {
    return this.state.currentStep;
  }

  isSubmitting(): boolean {
    return this.state.submissionStatus === 'submitting';
  }

  isStepCompleted(step: number): boolean {
    return this.state.completedSteps.includes(step);
  }

  // -------------------------------------------------------------------------
  // State Mutations
  // -------------------------------------------------------------------------

  /**
   * Begin submitting the current step completion.
   * Clears any previous error.
   */
  startSubmission(): void {
    this.state = {
      ...this.state,
      submissionStatus: 'submitting',
      error: null,
    };
  }

  /**
   * Mark the current step as successfully completed.
   * Adds the step to completedSteps and advances to next step.
   */
  completeStep(step: number): void {
    const completedSteps = this.state.completedSteps.includes(step)
      ? this.state.completedSteps
      : [...this.state.completedSteps, step];

    this.state = {
      ...this.state,
      submissionStatus: 'success',
      completedSteps,
      currentStep: step + 1,
      error: null,
    };
  }

  /**
   * Handle a submission error.
   * Sets error message and resets submission status.
   */
  handleError(errorMessage: string): void {
    this.state = {
      ...this.state,
      submissionStatus: 'error',
      error: errorMessage,
    };
  }

  /**
   * Reset submission status to idle.
   * Used for retry after error.
   */
  resetSubmission(): void {
    this.state = {
      ...this.state,
      submissionStatus: 'idle',
      error: null,
    };
  }
}
