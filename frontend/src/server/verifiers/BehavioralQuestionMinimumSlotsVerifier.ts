/**
 * BehavioralQuestionMinimumSlotsVerifier - Server-side validation of
 * minimum slot constraints for behavioral questions.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Enforces:
 * - objective: non-empty string
 * - actions: at least 3 non-empty strings
 * - obstacles: at least 1 non-empty string
 * - outcome: non-empty string
 * - roleClarity: non-empty string
 */

export interface MinimumSlotsVerificationResult {
  valid: boolean;
  errors: Record<string, string>;
}

export interface MinimumSlotsInput {
  objective: string;
  actions: string[];
  obstacles: string[];
  outcome: string;
  roleClarity: string;
}

export const BehavioralQuestionMinimumSlotsVerifier = {
  /**
   * Verify that all minimum slot requirements are met.
   * Returns a result with valid=true or valid=false with field-level errors.
   */
  verify(entity: MinimumSlotsInput): MinimumSlotsVerificationResult {
    const errors: Record<string, string> = {};

    if (!entity.objective || entity.objective.trim() === '') {
      errors.objective = 'Objective is required';
    }

    const validActions = entity.actions.filter((a) => a && a.trim() !== '');
    if (validActions.length < 3) {
      errors.actions = `At least 3 actions are required (got ${validActions.length})`;
    }

    const validObstacles = entity.obstacles.filter((o) => o && o.trim() !== '');
    if (validObstacles.length < 1) {
      errors.obstacles = 'At least 1 obstacle is required';
    }

    if (!entity.outcome || entity.outcome.trim() === '') {
      errors.outcome = 'Outcome is required';
    }

    if (!entity.roleClarity || entity.roleClarity.trim() === '') {
      errors.roleClarity = 'Role clarity is required';
    }

    return {
      valid: Object.keys(errors).length === 0,
      errors,
    };
  },
} as const;
