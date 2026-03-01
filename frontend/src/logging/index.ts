/**
 * Frontend logging utility for structured error and info logging.
 *
 * Resource: cfg-r3d7 (frontend_logging)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Client-side logger for capturing UI state update failures
 * and rendering issues. In production, this would integrate
 * with a client-side error tracking service (e.g., Sentry).
 */

export interface FrontendLogContext {
  component?: string;
  module?: string;
  action?: string;
  [key: string]: unknown;
}

export const frontendLogger = {
  info(message: string, context?: FrontendLogContext): void {
    console.log(
      JSON.stringify({
        level: 'info',
        message,
        ...context,
        timestamp: new Date().toISOString(),
      }),
    );
  },

  warn(message: string, context?: FrontendLogContext): void {
    console.warn(
      JSON.stringify({
        level: 'warn',
        message,
        ...context,
        timestamp: new Date().toISOString(),
      }),
    );
  },

  error(message: string, error?: unknown, context?: FrontendLogContext): void {
    const errorInfo =
      error instanceof Error
        ? { errorName: error.name, errorMessage: error.message, stack: error.stack }
        : { errorValue: String(error) };

    console.error(
      JSON.stringify({
        level: 'error',
        message,
        ...errorInfo,
        ...context,
        timestamp: new Date().toISOString(),
      }),
    );
  },
} as const;
