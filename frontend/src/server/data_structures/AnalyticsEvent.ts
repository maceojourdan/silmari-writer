/**
 * AnalyticsEvent - Zod schema and TypeScript types for analytics event records.
 *
 * Stores leading KPI contributions triggered by successful user actions.
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Zod Schema
// ---------------------------------------------------------------------------

export const AnalyticsEventSchema = z.object({
  id: z.string().uuid(),
  kpiId: z.string().min(1),
  userId: z.string().min(1),
  timestamp: z.string(),
  metadata: z.record(z.string(), z.any()),
  createdAt: z.string(),
});

export type AnalyticsEvent = z.infer<typeof AnalyticsEventSchema>;

// ---------------------------------------------------------------------------
// Analytics Event Insert (for DAO)
// ---------------------------------------------------------------------------

export const AnalyticsEventInsertSchema = z.object({
  kpiId: z.string().min(1),
  userId: z.string().min(1),
  timestamp: z.string(),
  metadata: z.record(z.string(), z.any()),
});

export type AnalyticsEventInsert = z.infer<typeof AnalyticsEventInsertSchema>;
