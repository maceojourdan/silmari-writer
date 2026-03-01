/**
 * logger - Backend logging utility for structured error and info logging.
 *
 * Resource: cfg-q9c5 (backend_logging)
 * Path: 294-parse-and-store-session-input-objects
 *
 * In production, this would integrate with a structured logging service
 * (e.g., Pino, Winston, or a cloud provider's logging SDK).
 * For now, wraps console with structured output.
 */

export interface LogContext {
  path?: string;
  resource?: string;
  [key: string]: unknown;
}

export const logger = {
  info(message: string, context?: LogContext): void {
    console.log(JSON.stringify({ level: 'info', message, ...context, timestamp: new Date().toISOString() }));
  },

  warn(message: string, context?: LogContext): void {
    console.warn(JSON.stringify({ level: 'warn', message, ...context, timestamp: new Date().toISOString() }));
  },

  error(message: string, error?: unknown, context?: LogContext): void {
    const errorInfo = error instanceof Error
      ? { errorName: error.name, errorMessage: error.message, stack: error.stack }
      : { errorValue: String(error) };

    console.error(JSON.stringify({
      level: 'error',
      message,
      ...errorInfo,
      ...context,
      timestamp: new Date().toISOString(),
    }));
  },
} as const;
