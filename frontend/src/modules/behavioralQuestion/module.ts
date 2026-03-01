/**
 * behavioralQuestionModule - Frontend module managing behavioral question
 * state and submission flow.
 *
 * Resource: ui-v3n6 (module)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Manages:
 * - Draft state (objective, actions, obstacles, outcome, roleClarity)
 * - Validation state (field errors)
 * - Submission state (isSubmitting, apiError)
 * - Status tracking (DRAFT → VERIFY)
 */

import { useState, useCallback, useRef } from 'react';
import type {
  BehavioralQuestionDraft,
  BehavioralQuestionStatus,
} from '@/server/data_structures/BehavioralQuestion';
import { validateMinimumSlots } from '@/verifiers/behavioralQuestionVerifier';
import { evaluateBehavioralQuestion } from '@/api_contracts/evaluateBehavioralQuestion';
import { frontendLogger } from '@/logging/index';

const emptyDraft: BehavioralQuestionDraft = {
  objective: '',
  actions: [],
  obstacles: [],
  outcome: '',
  roleClarity: '',
};

const MAX_FAILED_ATTEMPTS = 5;

export interface BehavioralQuestionModuleState {
  draft: BehavioralQuestionDraft;
  errors: Record<string, string>;
  isSubmitting: boolean;
  status: BehavioralQuestionStatus;
  apiError: string | null;
  questionId: string | null;
  submit: () => Promise<void>;
  updateDraft: (draft: BehavioralQuestionDraft) => void;
  updateField: <K extends keyof BehavioralQuestionDraft>(
    field: K,
    value: BehavioralQuestionDraft[K],
  ) => void;
}

/**
 * React hook managing the behavioral question module state.
 */
export function useBehavioralQuestionModule(
  sessionId: string,
): BehavioralQuestionModuleState {
  const [draft, setDraft] = useState<BehavioralQuestionDraft>(emptyDraft);
  const [errors, setErrors] = useState<Record<string, string>>({});
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [status, setStatus] = useState<BehavioralQuestionStatus>('DRAFT');
  const [apiError, setApiError] = useState<string | null>(null);
  const [questionId, setQuestionId] = useState<string | null>(null);
  const failedAttempts = useRef(0);

  const updateDraft = useCallback((newDraft: BehavioralQuestionDraft) => {
    setDraft(newDraft);
    setErrors({});
    setApiError(null);
  }, []);

  const updateField = useCallback(
    <K extends keyof BehavioralQuestionDraft>(
      field: K,
      value: BehavioralQuestionDraft[K],
    ) => {
      setDraft((prev) => ({ ...prev, [field]: value }));
      // Clear field-specific error
      setErrors((prev) => {
        const next = { ...prev };
        delete next[field];
        return next;
      });
      setApiError(null);
    },
    [],
  );

  const submit = useCallback(async () => {
    setApiError(null);

    // Step 1: Frontend validation
    const validation = validateMinimumSlots(draft);
    if (!validation.isValid) {
      setErrors(validation.errors);
      return;
    }

    // Step 1.5: Check retry limit (only counts failed API calls)
    if (failedAttempts.current >= MAX_FAILED_ATTEMPTS) {
      setApiError(
        'Too many failed attempts. Please wait for a cooldown period before trying again.',
      );
      frontendLogger.warn('Submission blocked due to cooldown', {
        module: 'behavioralQuestion',
        action: 'submit',
        failedAttempts: failedAttempts.current,
      });
      return;
    }

    // Step 2: Call backend API
    setIsSubmitting(true);
    try {
      const result = await evaluateBehavioralQuestion({
        sessionId,
        ...draft,
      });

      // Step 3: Update status on success
      try {
        setStatus(result.status);
        setQuestionId(result.questionId);
      } catch (stateError) {
        frontendLogger.error(
          'Failed to update UI state after successful evaluation',
          stateError,
          { module: 'behavioralQuestion', action: 'setStatus' },
        );
      }
    } catch (error) {
      failedAttempts.current += 1;
      const message =
        error instanceof Error ? error.message : 'An unexpected error occurred';
      setApiError(message);
      frontendLogger.error('Behavioral question evaluation failed', error, {
        module: 'behavioralQuestion',
        action: 'submit',
        failedAttempts: failedAttempts.current,
      });
    } finally {
      setIsSubmitting(false);
    }
  }, [draft, sessionId]);

  return {
    draft,
    errors,
    isSubmitting,
    status,
    apiError,
    questionId,
    submit,
    updateDraft,
    updateField,
  };
}
