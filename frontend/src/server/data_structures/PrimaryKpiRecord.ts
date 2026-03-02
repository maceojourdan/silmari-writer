/**
 * PrimaryKpiRecord - Zod schema and TypeScript types for primary KPI event records.
 *
 * Stores primary KPI events triggered by core conversion actions (e.g., purchase).
 *
 * Resource: db-f8n5 (data_structure)
 * Path: 339-record-primary-kpi-analytics-event
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Primary KPI Event Status
// ---------------------------------------------------------------------------

export const PrimaryKpiStatus = {
  PENDING: 'PENDING',
  PERSISTED: 'PERSISTED',
  ANALYTICS_SENT: 'ANALYTICS_SENT',
  ANALYTICS_FAILED: 'ANALYTICS_FAILED',
} as const;

export type PrimaryKpiStatus = (typeof PrimaryKpiStatus)[keyof typeof PrimaryKpiStatus];

// ---------------------------------------------------------------------------
// Zod Schema — Full persisted record
// ---------------------------------------------------------------------------

export const PrimaryKpiRecordSchema = z.object({
  id: z.string().uuid(),
  userId: z.string().min(1),
  actionType: z.string().min(1),
  metadata: z.record(z.string(), z.any()),
  status: z.enum(['PENDING', 'PERSISTED', 'ANALYTICS_SENT', 'ANALYTICS_FAILED']),
  timestamp: z.string(),
  createdAt: z.string(),
});

export type PrimaryKpiRecord = z.infer<typeof PrimaryKpiRecordSchema>;

// ---------------------------------------------------------------------------
// Insert schema (for DAO — no id/createdAt)
// ---------------------------------------------------------------------------

export const PrimaryKpiInsertSchema = z.object({
  userId: z.string().min(1),
  actionType: z.string().min(1),
  metadata: z.record(z.string(), z.any()).default({}),
  status: z.enum(['PENDING', 'PERSISTED', 'ANALYTICS_SENT', 'ANALYTICS_FAILED']).default('PENDING'),
  timestamp: z.string(),
});

export type PrimaryKpiInsert = z.infer<typeof PrimaryKpiInsertSchema>;

// ---------------------------------------------------------------------------
// Analytics Event Payload (sent to external analytics system)
// ---------------------------------------------------------------------------

export const AnalyticsEventPayloadSchema = z.object({
  eventId: z.string().uuid(),
  userId: z.string().min(1),
  actionType: z.string().min(1),
  metadata: z.record(z.string(), z.any()),
  timestamp: z.string(),
});

export type AnalyticsEventPayload = z.infer<typeof AnalyticsEventPayloadSchema>;

// ---------------------------------------------------------------------------
// API Request/Response schemas
// ---------------------------------------------------------------------------

export const RecordPrimaryKpiRequestSchema = z.object({
  userId: z.string().min(1),
  actionType: z.string().min(1),
  metadata: z.record(z.string(), z.any()).optional().default({}),
});

export type RecordPrimaryKpiRequest = z.infer<typeof RecordPrimaryKpiRequestSchema>;

export const RecordPrimaryKpiResponseSchema = z.object({
  id: z.string().uuid(),
  status: z.enum(['PENDING', 'PERSISTED', 'ANALYTICS_SENT', 'ANALYTICS_FAILED']),
  analyticsEmitted: z.boolean(),
});

export type RecordPrimaryKpiResponse = z.infer<typeof RecordPrimaryKpiResponseSchema>;
