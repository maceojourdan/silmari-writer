/**
 * Tool Error Handling (REQ_009)
 *
 * Consistent error handling patterns for all tool handlers with structured error responses.
 */

// =============================================================================
// REQ_009.1: ToolErrorCode type alias
// =============================================================================

/**
 * Error codes for tool operations
 * REQ_009.1: Union type for type-safe error code usage
 */
export type ToolErrorCode =
  | 'RATE_LIMIT'
  | 'INVALID_REQUEST'
  | 'API_ERROR'
  | 'TIMEOUT'
  | 'NETWORK'
  | 'CONFIG_ERROR'
  | 'VALIDATION_ERROR';

// =============================================================================
// REQ_009.1: ToolError interface extending Error
// =============================================================================

/**
 * Structured error for tool operations
 * REQ_009.1: Extends Error class to support stack traces and instanceof checks
 *
 * @example
 * ```typescript
 * const error = new ToolError(
 *   'Rate limit exceeded',
 *   'RATE_LIMIT',
 *   true,
 *   'Wait 30 seconds before retrying'
 * );
 * console.log(error.toJSON()); // { code: 'RATE_LIMIT', message: '...', ... }
 * ```
 */
export class ToolError extends Error {
  /** Error code for programmatic handling */
  code: ToolErrorCode;
  /** Whether the operation can be retried */
  retryable: boolean;
  /** Optional user-actionable guidance */
  suggestedAction?: string;
  /** Correlation ID for tracing */
  correlationId?: string;
  /** Original error for debugging (not exposed to clients) */
  originalError?: Error;

  /**
   * Create a new ToolError
   * REQ_009.1: Constructor accepts (message, code, retryable, suggestedAction?) parameters
   */
  constructor(
    message: string,
    code: ToolErrorCode,
    retryable: boolean,
    suggestedAction?: string
  ) {
    super(message);
    this.name = 'ToolError';
    this.code = code;
    this.retryable = retryable;
    this.suggestedAction = suggestedAction;

    // Maintain proper stack trace for where error was thrown (V8 engines)
    if (Error.captureStackTrace) {
      Error.captureStackTrace(this, ToolError);
    }
  }

  /**
   * Convert to JSON for API responses
   * REQ_009.1: toJSON() method returns serializable object
   */
  toJSON(): {
    code: ToolErrorCode;
    message: string;
    retryable: boolean;
    suggestedAction?: string;
  } {
    return {
      code: this.code,
      message: this.message,
      retryable: this.retryable,
      ...(this.suggestedAction && { suggestedAction: this.suggestedAction }),
    };
  }

  // ==========================================================================
  // REQ_009.1: Static factory methods
  // ==========================================================================

  /**
   * Create a rate limit error
   * REQ_009.1: ToolError.rateLimit() factory method
   */
  static rateLimit(waitSeconds?: number): ToolError {
    const message = waitSeconds
      ? `Rate limit exceeded. Retry after ${waitSeconds} seconds.`
      : 'Rate limit exceeded. Please try again later.';
    const suggestedAction = waitSeconds
      ? `Wait ${waitSeconds} seconds before retrying`
      : 'Wait a moment before retrying';
    return new ToolError(message, 'RATE_LIMIT', true, suggestedAction);
  }

  /**
   * Create a timeout error
   * REQ_009.1: ToolError.timeout() factory method
   */
  static timeout(durationMs?: number): ToolError {
    const message = durationMs
      ? `Operation timed out after ${Math.round(durationMs / 1000)} seconds`
      : 'Operation timed out';
    return new ToolError(message, 'TIMEOUT', true, 'Try again or use a simpler query');
  }

  /**
   * Create an API error
   * REQ_009.1: ToolError.apiError() factory method
   */
  static apiError(message: string = 'An error occurred processing your request'): ToolError {
    return new ToolError(message, 'API_ERROR', false);
  }

  /**
   * Create a network error
   * REQ_009.1: ToolError.network() factory method
   */
  static network(message: string = 'Network error. Please check your connection.'): ToolError {
    return new ToolError(message, 'NETWORK', true, 'Check your internet connection and try again');
  }

  /**
   * Create a validation error
   * REQ_009.1: Static factory for validation errors
   */
  static validation(message: string): ToolError {
    return new ToolError(message, 'VALIDATION_ERROR', false);
  }

  /**
   * Create a config error
   * REQ_009.1: Static factory for configuration errors
   */
  static configError(message: string): ToolError {
    return new ToolError(message, 'CONFIG_ERROR', false, 'Check your configuration settings');
  }
}

// =============================================================================
// REQ_009.2: Rate limit error handling with Retry-After header parsing
// =============================================================================

/**
 * Parse Retry-After header value
 * REQ_009.2: Supports both seconds format and HTTP-date format
 *
 * @param retryAfter - The Retry-After header value
 * @returns Delay in milliseconds, or null if invalid
 */
export function parseRetryAfter(retryAfter: string | null): number | null {
  if (!retryAfter) {
    return null;
  }

  // Check if it starts with a digit (numeric format) or minus sign (negative)
  const trimmed = retryAfter.trim();
  if (/^-?\d/.test(trimmed)) {
    const seconds = parseInt(trimmed, 10);
    // Reject negative numbers and NaN
    if (isNaN(seconds) || seconds < 0) {
      return null;
    }
    return seconds * 1000;
  }

  // Try parsing as HTTP-date format (RFC 7231)
  const date = new Date(retryAfter);
  if (!isNaN(date.getTime())) {
    const delayMs = date.getTime() - Date.now();
    return delayMs > 0 ? delayMs : 0;
  }

  return null;
}

/**
 * Configuration for rate limit handling
 */
export interface RateLimitConfig {
  /** Default delay when Retry-After header is missing (ms) */
  defaultDelayMs?: number;
  /** Minimum acceptable delay (ms) */
  minDelayMs?: number;
  /** Maximum acceptable delay (ms) */
  maxDelayMs?: number;
}

const DEFAULT_RATE_LIMIT_CONFIG: Required<RateLimitConfig> = {
  defaultDelayMs: 10000, // 10 seconds
  minDelayMs: 1000,      // 1 second
  maxDelayMs: 300000,    // 300 seconds (5 minutes)
};

/**
 * Handle rate limit response
 * REQ_009.2: Parse Retry-After, validate bounds, return ToolError with timing info
 *
 * @param response - The HTTP response with 429 status
 * @param config - Optional configuration for delay bounds
 * @returns ToolError with rate limit information
 */
export function handleRateLimit(
  response: Response,
  config: RateLimitConfig = {}
): ToolError {
  const mergedConfig = { ...DEFAULT_RATE_LIMIT_CONFIG, ...config };
  const retryAfter = response.headers?.get?.('Retry-After');

  let delayMs = parseRetryAfter(retryAfter) ?? mergedConfig.defaultDelayMs;

  // REQ_009.2: Validate parsed delay is within acceptable bounds
  delayMs = Math.max(mergedConfig.minDelayMs, Math.min(mergedConfig.maxDelayMs, delayMs));

  const waitSeconds = Math.ceil(delayMs / 1000);
  const error = ToolError.rateLimit(waitSeconds);

  return error;
}

/**
 * Check if response is a rate limit error
 * REQ_009.2: Detects HTTP 429 status code
 */
export function isRateLimitResponse(response: Response): boolean {
  return response.status === 429;
}

// =============================================================================
// REQ_009.3: Safe error handling with no sensitive data exposure
// =============================================================================

/**
 * Patterns to detect and redact sensitive data
 */
const SENSITIVE_PATTERNS: RegExp[] = [
  // API keys (OpenAI format: sk-... with any length)
  /sk-[a-zA-Z0-9]+/gi,
  // Generic API key patterns
  /api[_-]?key[=:\s]+["']?[a-zA-Z0-9_-]+["']?/gi,
  // Bearer tokens
  /bearer\s+[a-zA-Z0-9_.-]+/gi,
  // Authorization headers
  /authorization[=:\s]+["']?[a-zA-Z0-9_.-]+["']?/gi,
  // File paths (Unix and Windows)
  /(?:\/[\w.-]+)+\.(ts|js|json|env)/gi,
  /(?:[A-Z]:\\[\w\\.-]+)+\.(ts|js|json|env)/gi,
  // Environment variable patterns
  /process\.env\.[A-Z_]+/gi,
  // Connection strings
  /(?:mongodb|postgres|mysql):\/\/[^\s"']+/gi,
];

/**
 * Redact sensitive data from a string
 * REQ_009.3: Sanitize error messages to remove sensitive data
 */
export function redactSensitiveData(input: string): string {
  let sanitized = input;
  for (const pattern of SENSITIVE_PATTERNS) {
    sanitized = sanitized.replace(pattern, '[REDACTED]');
  }
  return sanitized;
}

/**
 * Sensitive headers that should be stripped from logged requests
 * REQ_009.3: Headers to redact
 */
export const SENSITIVE_HEADERS = [
  'authorization',
  'x-api-key',
  'api-key',
  'cookie',
  'set-cookie',
  'x-auth-token',
];

/**
 * Redact headers from a headers object
 * REQ_009.3: Strip sensitive headers before logging
 */
export function redactHeaders(
  headers: Record<string, string> | Headers
): Record<string, string> {
  const result: Record<string, string> = {};

  if (headers instanceof Headers) {
    headers.forEach((value, key) => {
      if (SENSITIVE_HEADERS.includes(key.toLowerCase())) {
        result[key] = '[REDACTED]';
      } else {
        result[key] = value;
      }
    });
  } else {
    for (const [key, value] of Object.entries(headers)) {
      if (SENSITIVE_HEADERS.includes(key.toLowerCase())) {
        result[key] = '[REDACTED]';
      } else {
        result[key] = value;
      }
    }
  }

  return result;
}

/**
 * OpenAI error code to user-friendly message mapping
 * REQ_009.3: Map API errors to user-friendly equivalents
 */
export const ERROR_MESSAGE_MAP: Record<string, string> = {
  invalid_api_key: 'Authentication failed. Please check your API configuration.',
  insufficient_quota: 'Usage quota exceeded. Please check your billing settings.',
  model_not_found: 'The requested model is not available.',
  context_length_exceeded: 'Your input is too long. Please shorten your message.',
  rate_limit_exceeded: 'Too many requests. Please wait a moment and try again.',
  server_error: 'The service is temporarily unavailable. Please try again.',
  timeout: 'The request took too long. Please try again with a simpler query.',
  content_policy_violation: 'Your request was flagged by our content policy.',
  invalid_request_error: 'Invalid request. Please check your input.',
};

/**
 * Sanitize an API error for safe client exposure
 * REQ_009.3: Creates safe error message while preserving error code
 */
export function sanitizeApiError(error: Error | unknown): {
  message: string;
  code: ToolErrorCode;
  originalMessage?: string;
} {
  if (!(error instanceof Error)) {
    return {
      message: 'An unexpected error occurred',
      code: 'API_ERROR',
    };
  }

  // Check for known error types by code or message
  const errorCode = (error as Error & { code?: string }).code;
  const errorMessage = error.message.toLowerCase();

  // Map to user-friendly messages
  for (const [key, friendlyMessage] of Object.entries(ERROR_MESSAGE_MAP)) {
    if (errorCode === key || errorMessage.includes(key.replace(/_/g, ' '))) {
      return {
        message: friendlyMessage,
        code: key.includes('rate_limit') ? 'RATE_LIMIT' : 'API_ERROR',
        originalMessage: error.message,
      };
    }
  }

  // Generic sanitization for unknown errors
  const sanitizedMessage = redactSensitiveData(error.message);

  // If message was redacted, use generic message
  if (sanitizedMessage !== error.message || sanitizedMessage.includes('[REDACTED]')) {
    return {
      message: 'An error occurred processing your request',
      code: 'API_ERROR',
      originalMessage: error.message,
    };
  }

  return {
    message: sanitizedMessage,
    code: 'API_ERROR',
    originalMessage: error.message,
  };
}

/**
 * Create a safe ToolError from any error
 * REQ_009.3: Wrapper that logs full error but returns sanitized version
 */
export function createSafeToolError(
  error: Error | unknown,
  logger?: StructuredLogger
): ToolError {
  const sanitized = sanitizeApiError(error);

  // Log the original error with full context (server-side only)
  if (logger && error instanceof Error) {
    logger.error('API error occurred', {
      tool: 'unknown',
      error: error.message,
      stack: error.stack,
      code: sanitized.code,
    });
  }

  const toolError = new ToolError(sanitized.message, sanitized.code, false);
  if (error instanceof Error) {
    toolError.originalError = error;
  }

  return toolError;
}

// =============================================================================
// REQ_009.4: Timeout handling with configurable durations
// =============================================================================

/**
 * Default timeout durations per tool type (milliseconds)
 * REQ_009.4: Configurable durations per tool type
 */
export const TOOL_TIMEOUTS: Record<string, number> = {
  image_generation: 120000,   // 120 seconds
  deep_research: 300000,      // 300 seconds (initial request)
  deep_research_polling: 1800000, // 30 minutes (total polling)
  document_generation: 60000, // 60 seconds
  chat_completion: 30000,     // 30 seconds
  default: 30000,             // 30 seconds fallback
};

/**
 * Get timeout duration for a tool type
 * REQ_009.4: Returns configured or default timeout
 */
export function getToolTimeout(toolType: string): number {
  return TOOL_TIMEOUTS[toolType] ?? TOOL_TIMEOUTS.default;
}

/**
 * Options for creating a timeout controller
 */
export interface TimeoutOptions {
  /** Timeout duration in milliseconds */
  timeoutMs: number;
  /** Existing abort signal to combine with timeout */
  signal?: AbortSignal;
  /** Cleanup function to run on timeout */
  onTimeout?: () => void;
}

/**
 * Result of creating a timeout controller
 */
export interface TimeoutController {
  /** Combined abort signal (timeout + optional user signal) */
  signal: AbortSignal;
  /** Clear the timeout (call when operation completes) */
  clear: () => void;
  /** Check if timeout was triggered */
  isTimeout: () => boolean;
}

/**
 * Create an AbortController with timeout
 * REQ_009.4: Implements AbortController for cancellable requests
 */
export function createTimeoutController(options: TimeoutOptions): TimeoutController {
  const controller = new AbortController();
  let timedOut = false;

  const timeoutId = setTimeout(() => {
    timedOut = true;
    options.onTimeout?.();
    controller.abort();
  }, options.timeoutMs);

  // Handle external abort signal
  if (options.signal) {
    if (options.signal.aborted) {
      clearTimeout(timeoutId);
      controller.abort();
    } else {
      options.signal.addEventListener('abort', () => {
        clearTimeout(timeoutId);
        controller.abort();
      });
    }
  }

  return {
    signal: controller.signal,
    clear: () => clearTimeout(timeoutId),
    isTimeout: () => timedOut,
  };
}

/**
 * Execute a fetch with timeout
 * REQ_009.4: Wrapper for fetch with automatic timeout handling
 */
export async function fetchWithTimeout(
  url: string,
  init: RequestInit = {},
  timeoutMs: number = TOOL_TIMEOUTS.default
): Promise<Response> {
  const controller = createTimeoutController({
    timeoutMs,
    signal: init.signal as AbortSignal | undefined,
  });

  try {
    const response = await fetch(url, {
      ...init,
      signal: controller.signal,
    });
    controller.clear();
    return response;
  } catch (error) {
    controller.clear();

    if (controller.isTimeout()) {
      throw ToolError.timeout(timeoutMs);
    }

    if (error instanceof DOMException && error.name === 'AbortError') {
      throw new ToolError('Operation cancelled', 'TIMEOUT', false);
    }

    throw error;
  }
}

// =============================================================================
// REQ_009.5: Structured logging format
// =============================================================================

/**
 * Log levels
 * REQ_009.5: Appropriate log levels for different scenarios
 */
export type LogLevel = 'debug' | 'info' | 'warn' | 'error';

/**
 * Structured log entry
 * REQ_009.5: Consistent structured format for all tool errors
 */
export interface StructuredLogEntry {
  timestamp: string;
  level: LogLevel;
  tool: string;
  code?: ToolErrorCode | string;
  message: string;
  correlationId?: string;
  metadata?: Record<string, unknown>;
}

/**
 * Context for structured logging
 * REQ_009.5: Contextual metadata for log entries
 */
export interface LogContext {
  tool: string;
  correlationId?: string;
  userId?: string;
  sessionId?: string;
  requestId?: string;
  operation?: string;
}

/**
 * Structured logger interface
 * REQ_009.5: Consistent logging across all tool handlers
 */
export interface StructuredLogger {
  debug(message: string, metadata?: Record<string, unknown>): void;
  info(message: string, metadata?: Record<string, unknown>): void;
  warn(message: string, metadata?: Record<string, unknown>): void;
  error(message: string, metadata?: Record<string, unknown>): void;
  withContext(context: Partial<LogContext>): StructuredLogger;
}

/**
 * Create a structured log entry
 * REQ_009.5: Format log entries as JSON for log aggregation
 */
export function createLogEntry(
  level: LogLevel,
  message: string,
  context: LogContext,
  metadata?: Record<string, unknown>
): StructuredLogEntry {
  // Redact sensitive data from metadata
  const safeMetadata = metadata
    ? JSON.parse(redactSensitiveData(JSON.stringify(metadata)))
    : undefined;

  return {
    timestamp: new Date().toISOString(),
    level,
    tool: context.tool,
    message: redactSensitiveData(message),
    correlationId: context.correlationId,
    ...(safeMetadata && { metadata: safeMetadata }),
  };
}

/**
 * Format a log entry for console output
 * REQ_009.5: JSON-formatted for log aggregation tools
 */
export function formatLogEntry(entry: StructuredLogEntry): string {
  return JSON.stringify(entry);
}

/**
 * Default structured logger implementation
 * REQ_009.5: Integration with existing console.error pattern
 */
export function createStructuredLogger(initialContext: LogContext): StructuredLogger {
  let context = { ...initialContext };

  const log = (level: LogLevel, message: string, metadata?: Record<string, unknown>) => {
    const entry = createLogEntry(level, message, context, metadata);
    const formatted = formatLogEntry(entry);

    // Map to appropriate console method
    switch (level) {
      case 'debug':
        console.debug(formatted);
        break;
      case 'info':
        console.log(formatted);
        break;
      case 'warn':
        console.warn(formatted);
        break;
      case 'error':
        console.error(formatted);
        break;
    }
  };

  return {
    debug: (message, metadata) => log('debug', message, metadata),
    info: (message, metadata) => log('info', message, metadata),
    warn: (message, metadata) => log('warn', message, metadata),
    error: (message, metadata) => log('error', message, metadata),
    withContext: (newContext) => {
      context = { ...context, ...newContext };
      return createStructuredLogger(context);
    },
  };
}

/**
 * Generate a correlation ID
 * REQ_009.5: Unique ID for linking related log entries
 */
export function generateCorrelationId(): string {
  return `${Date.now().toString(36)}-${Math.random().toString(36).substr(2, 9)}`;
}

/**
 * Log a ToolError with appropriate level
 * REQ_009.5: ERROR for failures, WARN for retryable errors
 */
export function logToolError(
  logger: StructuredLogger,
  error: ToolError,
  metadata?: Record<string, unknown>
): void {
  const level: LogLevel = error.retryable ? 'warn' : 'error';
  const logMetadata = {
    code: error.code,
    retryable: error.retryable,
    suggestedAction: error.suggestedAction,
    ...metadata,
  };

  if (level === 'warn') {
    logger.warn(error.message, logMetadata);
  } else {
    logger.error(error.message, logMetadata);
  }
}

// =============================================================================
// Utility exports for compatibility with existing code
// =============================================================================

/**
 * Check if an error is a ToolError
 */
export function isToolError(error: unknown): error is ToolError {
  return error instanceof ToolError;
}

/**
 * Convert any error to a ToolError
 */
export function toToolError(error: unknown): ToolError {
  if (error instanceof ToolError) {
    return error;
  }

  // Check for AbortError (DOMException) - may not be instanceof Error in Node.js
  if (
    error !== null &&
    typeof error === 'object' &&
    'name' in error &&
    (error as { name: string }).name === 'AbortError'
  ) {
    return new ToolError('Operation cancelled', 'TIMEOUT', false);
  }

  if (error instanceof Error) {
    // Check for network errors
    const errorCode = (error as Error & { code?: string }).code;
    if (errorCode === 'ECONNREFUSED' || errorCode === 'ETIMEDOUT' || errorCode === 'ENOTFOUND') {
      return ToolError.network(error.message);
    }

    return createSafeToolError(error);
  }

  return ToolError.apiError('An unexpected error occurred');
}
