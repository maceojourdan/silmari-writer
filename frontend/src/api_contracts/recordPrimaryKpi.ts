/**
 * recordPrimaryKpi - Typed API contract for the record primary KPI endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 339-record-primary-kpi-analytics-event
 */

import { z } from 'zod';

export class RecordPrimaryKpiApiError extends Error {
  code: string;
  constructor(code: string, message: string) {
    super(message);
    this.name = 'RecordPrimaryKpiApiError';
    this.code = code;
  }
}

export const RecordPrimaryKpiApiRequestSchema = z.object({
  userId: z.string().min(1),
  actionType: z.string().min(1),
  metadata: z.record(z.string(), z.any()).optional().default({}),
});

export type RecordPrimaryKpiApiRequest = z.infer<typeof RecordPrimaryKpiApiRequestSchema>;

export const RecordPrimaryKpiApiResponseSchema = z.object({
  id: z.string().uuid(),
  status: z.string(),
  analyticsEmitted: z.boolean(),
});

export type RecordPrimaryKpiApiResponse = z.infer<typeof RecordPrimaryKpiApiResponseSchema>;

export async function recordPrimaryKpi(
  payload: RecordPrimaryKpiApiRequest,
): Promise<RecordPrimaryKpiApiResponse> {
  const response = await fetch('/api/kpi/primary', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload),
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    const code = errorBody.code || 'UNKNOWN_ERROR';
    const message = errorBody.message || `Record KPI failed with status ${response.status}`;
    throw new RecordPrimaryKpiApiError(code, message);
  }

  const data = await response.json();
  const parsed = RecordPrimaryKpiApiResponseSchema.safeParse(data);
  if (!parsed.success) {
    throw new Error(`Invalid response from record KPI: ${parsed.error.issues.map(i => i.message).join(', ')}`);
  }
  return parsed.data;
}
