/**
 * PrimaryKpiVerifier - Validates primary KPI data against business rules.
 *
 * Resource: db-j6x9 (backend_verifier)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * Business rules:
 * - userId must be non-empty
 * - actionType must be a recognized primary KPI action
 * - timestamp must be a valid ISO string not in the future
 */

import { KpiErrors } from '@/server/error_definitions/KpiErrors';

const VALID_ACTION_TYPES = [
  'purchase',
  'core_conversion',
  'subscription_start',
  'trial_activation',
  'signup',
] as const;

export type ValidActionType = (typeof VALID_ACTION_TYPES)[number];

export const PrimaryKpiVerifier = {
  /**
   * Validate that a KPI action meets business rules.
   *
   * @param userId - The user performing the action
   * @param actionType - The type of primary KPI action
   * @param timestamp - ISO timestamp of the action
   * @throws KpiErrors.DomainValidationError if any rule fails
   */
  validate(userId: string, actionType: string, timestamp: string): void {
    if (!userId || userId.trim().length === 0) {
      throw KpiErrors.DomainValidationError('userId is required and cannot be empty');
    }

    if (!VALID_ACTION_TYPES.includes(actionType as ValidActionType)) {
      throw KpiErrors.DomainValidationError(
        `Invalid actionType '${actionType}'. Must be one of: ${VALID_ACTION_TYPES.join(', ')}`,
      );
    }

    const parsedDate = new Date(timestamp);
    if (isNaN(parsedDate.getTime())) {
      throw KpiErrors.DomainValidationError(
        `Invalid timestamp '${timestamp}'. Must be a valid ISO 8601 date string`,
      );
    }

    // Prevent future-dated events (allow 5 minute tolerance)
    const fiveMinutesFromNow = new Date(Date.now() + 5 * 60 * 1000);
    if (parsedDate > fiveMinutesFromNow) {
      throw KpiErrors.DomainValidationError(
        'Timestamp cannot be more than 5 minutes in the future',
      );
    }
  },
} as const;
