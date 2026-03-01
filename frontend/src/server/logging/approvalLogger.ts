/**
 * approvalLogger - Logs approval events for session state transitions.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 299-approve-draft-and-transition-to-finalize
 *
 * Writes approval event entries to backend log store.
 * On failure, falls back to shared logger and rethrows.
 */

import { logger } from './logger';
import { frontendLogger } from '../../logging/index';

export interface ApprovalLogEntry {
  sessionId: string;
  action: 'APPROVE';
  timestamp: string;
}

export const approvalLogger = {
  /**
   * Log an approval event for the given session.
   * On failure, falls back to shared/fallback logger and rethrows.
   */
  async logApproval(sessionId: string): Promise<ApprovalLogEntry> {
    const entry: ApprovalLogEntry = {
      sessionId,
      action: 'APPROVE',
      timestamp: new Date().toISOString(),
    };

    try {
      logger.info('Approval event logged', {
        sessionId: entry.sessionId,
        action: entry.action,
        timestamp: entry.timestamp,
        path: '299-approve-draft-and-transition-to-finalize',
        resource: 'cfg-q9c5',
      });

      return entry;
    } catch (error) {
      // Fallback to shared logger
      frontendLogger.error(
        'Primary approval logger failed',
        error instanceof Error ? error : new Error(String(error)),
        { sessionId },
      );

      throw error;
    }
  },
} as const;
