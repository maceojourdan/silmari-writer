/**
 * RecordPrimaryKpiHandler - Maps the validated request to the KPI recording
 * flow and delegates to PrimaryKpiService.
 *
 * Resource: api-n8k2 (request_handler)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * Known errors (KpiError) are rethrown as-is.
 * Unknown errors are wrapped in KpiErrors.SerializationError.
 */

import { PrimaryKpiService } from '@/server/services/PrimaryKpiService';
import { KpiError, KpiErrors } from '@/server/error_definitions/KpiErrors';
import { kpiLogger } from '@/server/logging/kpiLogger';
import type { RecordPrimaryKpiRequest, PrimaryKpiRecord } from '@/server/data_structures/PrimaryKpiRecord';

export const RecordPrimaryKpiHandler = {
  /**
   * Handle the full record-primary-kpi flow:
   * 1. Delegate to service for validation + persistence
   * 2. Attempt analytics emission (non-fatal)
   * 3. Return the persisted record + analytics status
   *
   * Known KpiErrors are rethrown.
   * Unknown errors are wrapped as SERIALIZATION_ERROR.
   */
  async handle(request: RecordPrimaryKpiRequest): Promise<{ record: PrimaryKpiRecord; analyticsEmitted: boolean }> {
    try {
      const result = await PrimaryKpiService.record(request);

      // Attempt analytics emission (non-fatal)
      const analyticsEmitted = await PrimaryKpiService.emitAnalytics(result.record);

      return { record: result.record, analyticsEmitted };
    } catch (error) {
      // Known errors → rethrow
      if (error instanceof KpiError) {
        throw error;
      }

      // Unknown errors → log and wrap
      kpiLogger.error(
        'Unexpected error during primary KPI recording',
        error,
        { path: '339-record-primary-kpi-analytics-event', resource: 'api-n8k2' },
      );

      throw KpiErrors.SerializationError(
        `Failed to record primary KPI: ${error instanceof Error ? error.message : 'unknown'}`,
      );
    }
  },
} as const;
