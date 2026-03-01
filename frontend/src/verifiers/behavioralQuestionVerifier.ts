/**
 * behavioralQuestionVerifier - Client-side validation enforcing minimum
 * slot requirements for behavioral questions.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Enforces:
 * - objective: non-empty string
 * - actions: at least 3 non-empty strings
 * - obstacles: at least 1 non-empty string
 * - outcome: non-empty string
 * - roleClarity: non-empty string
 */

import type { BehavioralQuestionDraft } from '@/server/data_structures/BehavioralQuestion';

export interface MinimumSlotsValidationResult {
  isValid: boolean;
  errors: Record<string, string>;
}

/**
 * Validate that a behavioral question draft meets minimum slot requirements.
 */
export function validateMinimumSlots(
  draft: BehavioralQuestionDraft,
): MinimumSlotsValidationResult {
  const errors: Record<string, string> = {};

  if (!draft.objective || draft.objective.trim() === '') {
    errors.objective = 'Objective is required';
  }

  const validActions = draft.actions.filter((a) => a && a.trim() !== '');
  if (validActions.length < 3) {
    errors.actions = `At least 3 actions are required (got ${validActions.length})`;
  }

  const validObstacles = draft.obstacles.filter((o) => o && o.trim() !== '');
  if (validObstacles.length < 1) {
    errors.obstacles = 'At least 1 obstacle is required';
  }

  if (!draft.outcome || draft.outcome.trim() === '') {
    errors.outcome = 'Outcome is required';
  }

  if (!draft.roleClarity || draft.roleClarity.trim() === '') {
    errors.roleClarity = 'Role clarity is required';
  }

  return {
    isValid: Object.keys(errors).length === 0,
    errors,
  };
}

/**
 * Validate a single field of the behavioral question draft.
 * Returns null if valid, or an error string if invalid.
 */
export function validateField(
  fieldName: keyof BehavioralQuestionDraft,
  value: string | string[],
): string | null {
  switch (fieldName) {
    case 'objective':
      return !value || (typeof value === 'string' && value.trim() === '')
        ? 'Objective is required'
        : null;

    case 'actions': {
      if (!Array.isArray(value)) return 'Actions must be an array';
      const validActions = value.filter((a) => a && a.trim() !== '');
      return validActions.length < 3
        ? `At least 3 actions are required (got ${validActions.length})`
        : null;
    }

    case 'obstacles': {
      if (!Array.isArray(value)) return 'Obstacles must be an array';
      const validObstacles = value.filter((o) => o && o.trim() !== '');
      return validObstacles.length < 1
        ? 'At least 1 obstacle is required'
        : null;
    }

    case 'outcome':
      return !value || (typeof value === 'string' && value.trim() === '')
        ? 'Outcome is required'
        : null;

    case 'roleClarity':
      return !value || (typeof value === 'string' && value.trim() === '')
        ? 'Role clarity is required'
        : null;

    default:
      return null;
  }
}
