/**
 * LeadingKpis - Canonical leading KPI identifiers.
 *
 * Resource: cfg-k3x7 (constant)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

export const LeadingKpis = {
  ONBOARDING_STEP_1: 'leading_kpi.onboarding_step_1',
  ONBOARDING_STEP_2: 'leading_kpi.onboarding_step_2',
  ONBOARDING_STEP_3: 'leading_kpi.onboarding_step_3',
} as const;

export type LeadingKpiId = (typeof LeadingKpis)[keyof typeof LeadingKpis];

/**
 * Maps onboarding step numbers to their corresponding KPI identifiers.
 * Returns undefined if the step doesn't have a KPI mapping.
 */
export function getKpiForStep(step: number): LeadingKpiId | undefined {
  const mapping: Record<number, LeadingKpiId> = {
    1: LeadingKpis.ONBOARDING_STEP_1,
    2: LeadingKpis.ONBOARDING_STEP_2,
    3: LeadingKpis.ONBOARDING_STEP_3,
  };
  return mapping[step];
}
