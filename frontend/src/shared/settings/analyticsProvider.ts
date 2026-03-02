/**
 * analyticsProvider - Stores analytics provider configuration and endpoint details.
 *
 * Resource: cfg-l8y1 (shared_settings)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * In production, these values would come from environment variables.
 * For now, provides typed defaults for the analytics provider integration.
 */

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

export const analyticsProvider = {
  /** Base URL for the external analytics endpoint */
  endpoint: process.env.ANALYTICS_PROVIDER_ENDPOINT || 'https://analytics.example.com/events',

  /** API key for authenticating with the analytics provider */
  apiKey: process.env.ANALYTICS_PROVIDER_API_KEY || '',

  /** Maximum retry attempts for failed analytics calls */
  maxRetries: 3,

  /** Timeout in milliseconds for each analytics request */
  timeoutMs: 5000,
} as const;

export type AnalyticsProviderConfig = typeof analyticsProvider;
