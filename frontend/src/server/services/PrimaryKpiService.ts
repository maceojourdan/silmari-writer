/**
 * PrimaryKpiService - Orchestrates primary KPI recording and analytics emission.
 *
 * Resource: db-h2s4 (service)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * Responsibilities:
 * - Validate KPI action via PrimaryKpiVerifier (business rules)
 * - Persist primary KPI record via PrimaryKpiDAO
 * - Emit analytics event with retry logic (max 3 attempts)
 * - Log outcomes via kpiLogger
 *
 * Throws KpiError on validation or persistence failure.
 * Analytics emission failures are non-fatal (logged, not thrown).
 */

import { PrimaryKpiDAO } from '@/server/data_access_objects/PrimaryKpiDAO';
import { PrimaryKpiVerifier } from '@/server/verifiers/PrimaryKpiVerifier';
import { KpiError, KpiErrors } from '@/server/error_definitions/KpiErrors';
import { kpiLogger } from '@/server/logging/kpiLogger';
import { sendAnalyticsEvent } from './analyticsClient';
import { AnalyticsEventPayloadSchema } from '@/server/data_structures/PrimaryKpiRecord';
import type {
  PrimaryKpiRecord,
  PrimaryKpiInsert,
  RecordPrimaryKpiRequest,
  AnalyticsEventPayload,
} from '@/server/data_structures/PrimaryKpiRecord';
import { analyticsProvider } from '@/shared/settings/analyticsProvider';

export const PrimaryKpiService = {
  /**
   * Step 3: Process and persist primary KPI action.
   *
   * 1. Validate via PrimaryKpiVerifier
   * 2. Persist via PrimaryKpiDAO.insert
   * 3. Return persisted record + analyticsEmitted flag
   *
   * @throws KpiError(DOMAIN_VALIDATION_ERROR) if business rules fail
   * @throws KpiError(PERSISTENCE_ERROR) if DAO insert fails
   */
  async record(
    request: RecordPrimaryKpiRequest,
  ): Promise<{ record: PrimaryKpiRecord; analyticsEmitted: boolean }> {
    const timestamp = new Date().toISOString();

    // Step 1: Validate business rules
    try {
      PrimaryKpiVerifier.validate(request.userId, request.actionType, timestamp);
    } catch (error) {
      kpiLogger.error(
        'Primary KPI validation failed',
        error,
        { userId: request.userId, actionType: request.actionType },
      );
      throw error;
    }

    // Step 2: Persist to database
    const insertData: PrimaryKpiInsert = {
      userId: request.userId,
      actionType: request.actionType,
      metadata: request.metadata ?? {},
      status: 'PENDING',
      timestamp,
    };

    let record: PrimaryKpiRecord;
    try {
      record = await PrimaryKpiDAO.insert(insertData);
    } catch (error) {
      kpiLogger.error(
        'Failed to persist primary KPI record',
        error,
        { userId: request.userId, actionType: request.actionType },
      );

      if (error instanceof KpiError) {
        throw error;
      }

      throw KpiErrors.PersistenceError(
        `Failed to persist primary KPI record for user '${request.userId}'`,
      );
    }

    // Step 3: Log success and return
    kpiLogger.info(
      'Primary KPI record persisted successfully',
      { userId: request.userId, actionType: request.actionType, recordId: record.id },
    );

    return { record, analyticsEmitted: false };
  },

  /**
   * Steps 4-5: Emit analytics event for a persisted KPI record.
   *
   * 1. Transform record → AnalyticsEventPayload
   * 2. Validate payload
   * 3. Retry loop: send to external analytics (max 3 attempts)
   * 4. Update record status based on outcome
   *
   * Never throws — returns boolean indicating success/failure.
   * Failures are logged via kpiLogger.
   */
  async emitAnalytics(record: PrimaryKpiRecord): Promise<boolean> {
    // Step 1: Transform record to analytics payload
    let payload: AnalyticsEventPayload;
    try {
      payload = {
        eventId: record.id,
        userId: record.userId,
        actionType: record.actionType,
        metadata: record.metadata,
        timestamp: record.timestamp,
      };

      // Validate the constructed payload
      const parsed = AnalyticsEventPayloadSchema.safeParse(payload);
      if (!parsed.success) {
        throw new Error(
          `Payload validation failed: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
        );
      }
    } catch (error) {
      kpiLogger.error(
        'Analytics payload transform failed',
        error instanceof Error ? error : new Error(String(error)),
        { recordId: record.id },
      );
      return false;
    }

    // Step 2: Send with retry loop (max 3 attempts)
    const maxRetries = analyticsProvider.maxRetries;
    let lastError: Error | undefined;

    for (let attempt = 1; attempt <= maxRetries; attempt++) {
      try {
        await sendAnalyticsEvent(payload);

        // Success — update status
        try {
          await PrimaryKpiDAO.updateStatus(record.id, 'ANALYTICS_SENT');
        } catch {
          // Status update failure is non-fatal
        }

        return true;
      } catch (error) {
        lastError = error instanceof Error ? error : new Error(String(error));
        kpiLogger.warn(
          `Analytics emission attempt ${attempt}/${maxRetries} failed`,
          { recordId: record.id, attempt },
        );
      }
    }

    // All attempts failed
    kpiLogger.error(
      'Analytics emission final_failure',
      lastError,
      { recordId: record.id },
    );

    // Update status to ANALYTICS_FAILED
    try {
      await PrimaryKpiDAO.updateStatus(record.id, 'ANALYTICS_FAILED');
    } catch {
      // Status update failure is non-fatal
    }

    return false;
  },
} as const;
