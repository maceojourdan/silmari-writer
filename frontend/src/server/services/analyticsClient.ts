/**
 * analyticsClient - Sends analytics event payloads to the external analytics provider.
 *
 * Resource: cfg-l8y1 (shared_settings)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * In production, this sends HTTP requests to the configured analytics endpoint.
 * For TDD, this function is designed to be mockable at the module boundary.
 */

import { analyticsProvider } from '@/shared/settings/analyticsProvider';
import type { AnalyticsEventPayload } from '@/server/data_structures/PrimaryKpiRecord';

/**
 * Send an analytics event payload to the external analytics provider.
 *
 * @param payload - The analytics event payload to send
 * @throws Error if the request fails or the provider returns a non-2xx status
 */
export async function sendAnalyticsEvent(
  payload: AnalyticsEventPayload,
): Promise<void> {
  const response = await fetch(analyticsProvider.endpoint, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      'Authorization': `Bearer ${analyticsProvider.apiKey}`,
    },
    body: JSON.stringify(payload),
    signal: AbortSignal.timeout(analyticsProvider.timeoutMs),
  });

  if (!response.ok) {
    const body = await response.text().catch(() => 'unknown');
    throw new Error(
      `Analytics provider returned ${response.status}: ${body}`,
    );
  }
}
