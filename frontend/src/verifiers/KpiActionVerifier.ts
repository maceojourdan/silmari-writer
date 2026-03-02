/**
 * KpiActionVerifier - Client-side validation of primary KPI action input.
 *
 * Resource: ui-a4y1 (frontend_verifier)
 * Path: 339-record-primary-kpi-analytics-event
 */

export type KpiActionPayload = {
  userId: string;
  actionType: string;
  metadata: Record<string, unknown>;
};

type ValidationSuccess = { valid: true; payload: KpiActionPayload };
type ValidationFailure = { valid: false; errors: string[] };
export type KpiActionValidationResult = ValidationSuccess | ValidationFailure;

export function validateKpiAction(
  userId: string,
  actionType: string,
  metadata: Record<string, unknown> = {},
): KpiActionValidationResult {
  const errors: string[] = [];

  if (!userId || userId.trim().length === 0) {
    errors.push('User ID is required');
  }

  if (!actionType || actionType.trim().length === 0) {
    errors.push('Action type is required');
  }

  if (errors.length > 0) {
    return { valid: false, errors };
  }

  return {
    valid: true,
    payload: { userId: userId.trim(), actionType: actionType.trim(), metadata },
  };
}
