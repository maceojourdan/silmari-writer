/**
 * Tests for Tool Error Handling (REQ_009)
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  ToolError,
  ToolErrorCode,
  parseRetryAfter,
  handleRateLimit,
  isRateLimitResponse,
  redactSensitiveData,
  redactHeaders,
  SENSITIVE_HEADERS,
  ERROR_MESSAGE_MAP,
  sanitizeApiError,
  createSafeToolError,
  TOOL_TIMEOUTS,
  getToolTimeout,
  createTimeoutController,
  fetchWithTimeout,
  createStructuredLogger,
  createLogEntry,
  formatLogEntry,
  generateCorrelationId,
  logToolError,
  isToolError,
  toToolError,
  type LogLevel,
  type LogContext,
  type StructuredLogEntry,
} from '@/lib/tool-error';

// =============================================================================
// REQ_009.1: ToolError interface tests
// =============================================================================

describe('REQ_009.1: ToolError interface', () => {
  describe('ToolError class structure', () => {
    it('should include code field as union type', () => {
      const validCodes: ToolErrorCode[] = [
        'RATE_LIMIT',
        'INVALID_REQUEST',
        'API_ERROR',
        'TIMEOUT',
        'NETWORK',
        'CONFIG_ERROR',
        'VALIDATION_ERROR',
      ];

      validCodes.forEach((code) => {
        const error = new ToolError('Test', code, false);
        expect(error.code).toBe(code);
      });
    });

    it('should include message field as string for human-readable error description', () => {
      const error = new ToolError('Human readable message', 'API_ERROR', false);
      expect(typeof error.message).toBe('string');
      expect(error.message).toBe('Human readable message');
    });

    it('should include retryable boolean field', () => {
      const retryable = new ToolError('Test', 'RATE_LIMIT', true);
      const nonRetryable = new ToolError('Test', 'API_ERROR', false);

      expect(typeof retryable.retryable).toBe('boolean');
      expect(retryable.retryable).toBe(true);
      expect(nonRetryable.retryable).toBe(false);
    });

    it('should include optional suggestedAction field as string', () => {
      const withAction = new ToolError('Test', 'RATE_LIMIT', true, 'Wait 30 seconds');
      const withoutAction = new ToolError('Test', 'API_ERROR', false);

      expect(withAction.suggestedAction).toBe('Wait 30 seconds');
      expect(withoutAction.suggestedAction).toBeUndefined();
    });

    it('should extend Error class to support stack traces', () => {
      const error = new ToolError('Test error', 'API_ERROR', false);

      expect(error).toBeInstanceOf(Error);
      expect(error.stack).toBeDefined();
      expect(typeof error.stack).toBe('string');
    });

    it('should support instanceof checks', () => {
      const error = new ToolError('Test', 'API_ERROR', false);

      expect(error instanceof ToolError).toBe(true);
      expect(error instanceof Error).toBe(true);
    });

    it('should have constructor accepting (message, code, retryable, suggestedAction?)', () => {
      const fullError = new ToolError('Message', 'TIMEOUT', true, 'Suggested action');

      expect(fullError.message).toBe('Message');
      expect(fullError.code).toBe('TIMEOUT');
      expect(fullError.retryable).toBe(true);
      expect(fullError.suggestedAction).toBe('Suggested action');
    });

    it('should have name property set to ToolError', () => {
      const error = new ToolError('Test', 'API_ERROR', false);
      expect(error.name).toBe('ToolError');
    });
  });

  describe('toJSON() method', () => {
    it('should return serializable object for API responses', () => {
      const error = new ToolError('Test message', 'RATE_LIMIT', true, 'Wait and retry');
      const json = error.toJSON();

      expect(json).toEqual({
        code: 'RATE_LIMIT',
        message: 'Test message',
        retryable: true,
        suggestedAction: 'Wait and retry',
      });
    });

    it('should omit suggestedAction when not provided', () => {
      const error = new ToolError('Test', 'API_ERROR', false);
      const json = error.toJSON();

      expect(json).toEqual({
        code: 'API_ERROR',
        message: 'Test',
        retryable: false,
      });
      expect('suggestedAction' in json).toBe(false);
    });

    it('should be JSON.stringify compatible', () => {
      const error = new ToolError('Test', 'NETWORK', true);
      const jsonString = JSON.stringify(error);
      const parsed = JSON.parse(jsonString);

      expect(parsed.code).toBe('NETWORK');
      expect(parsed.retryable).toBe(true);
    });
  });

  describe('Static factory methods', () => {
    it('should have ToolError.rateLimit() factory', () => {
      const error = ToolError.rateLimit(30);

      expect(error.code).toBe('RATE_LIMIT');
      expect(error.retryable).toBe(true);
      expect(error.message).toContain('30 seconds');
      expect(error.suggestedAction).toContain('30 seconds');
    });

    it('should have ToolError.rateLimit() without wait time', () => {
      const error = ToolError.rateLimit();

      expect(error.code).toBe('RATE_LIMIT');
      expect(error.retryable).toBe(true);
      expect(error.message).toContain('try again later');
    });

    it('should have ToolError.timeout() factory', () => {
      const error = ToolError.timeout(30000);

      expect(error.code).toBe('TIMEOUT');
      expect(error.retryable).toBe(true);
      expect(error.message).toContain('30 seconds');
      expect(error.suggestedAction).toBeDefined();
    });

    it('should have ToolError.apiError() factory', () => {
      const error = ToolError.apiError('Custom message');

      expect(error.code).toBe('API_ERROR');
      expect(error.retryable).toBe(false);
      expect(error.message).toBe('Custom message');
    });

    it('should have ToolError.network() factory', () => {
      const error = ToolError.network();

      expect(error.code).toBe('NETWORK');
      expect(error.retryable).toBe(true);
      expect(error.suggestedAction).toContain('connection');
    });

    it('should have ToolError.validation() factory', () => {
      const error = ToolError.validation('Invalid input');

      expect(error.code).toBe('VALIDATION_ERROR');
      expect(error.retryable).toBe(false);
      expect(error.message).toBe('Invalid input');
    });

    it('should have ToolError.configError() factory', () => {
      const error = ToolError.configError('Missing API key');

      expect(error.code).toBe('CONFIG_ERROR');
      expect(error.retryable).toBe(false);
      expect(error.suggestedAction).toContain('configuration');
    });
  });
});

// =============================================================================
// REQ_009.2: Rate limit error handling tests
// =============================================================================

describe('REQ_009.2: Rate limit error handling', () => {
  describe('parseRetryAfter', () => {
    it('should parse numeric Retry-After (seconds format)', () => {
      expect(parseRetryAfter('30')).toBe(30000);
      expect(parseRetryAfter('60')).toBe(60000);
      expect(parseRetryAfter('0')).toBe(0);
    });

    it('should parse HTTP-date format Retry-After', () => {
      const futureDate = new Date(Date.now() + 60000);
      const httpDate = futureDate.toUTCString();
      const parsed = parseRetryAfter(httpDate);

      expect(parsed).toBeGreaterThan(0);
      expect(parsed).toBeLessThanOrEqual(61000);
    });

    it('should return null for missing header', () => {
      expect(parseRetryAfter(null)).toBeNull();
      expect(parseRetryAfter('')).toBeNull();
    });

    it('should return null for invalid values', () => {
      expect(parseRetryAfter('invalid')).toBeNull();
      expect(parseRetryAfter('abc123')).toBeNull();
    });

    it('should handle negative seconds as invalid', () => {
      expect(parseRetryAfter('-10')).toBeNull();
      expect(parseRetryAfter('-1')).toBeNull();
    });
  });

  describe('handleRateLimit', () => {
    it('should detect HTTP 429 status code', () => {
      const response = new Response(null, { status: 429 });
      expect(isRateLimitResponse(response)).toBe(true);
    });

    it('should return false for non-429 status', () => {
      expect(isRateLimitResponse(new Response(null, { status: 200 }))).toBe(false);
      expect(isRateLimitResponse(new Response(null, { status: 500 }))).toBe(false);
    });

    it('should parse Retry-After header when present', () => {
      const response = new Response(null, {
        status: 429,
        headers: { 'Retry-After': '45' },
      });

      const error = handleRateLimit(response);
      expect(error.message).toContain('45');
    });

    it('should fall back to default delay when Retry-After is missing', () => {
      const response = new Response(null, { status: 429 });
      const error = handleRateLimit(response);

      expect(error.code).toBe('RATE_LIMIT');
      expect(error.retryable).toBe(true);
    });

    it('should validate delay within min bound (1s)', () => {
      const response = new Response(null, {
        status: 429,
        headers: { 'Retry-After': '0' },
      });

      const error = handleRateLimit(response, { minDelayMs: 1000 });
      expect(error.message).toMatch(/1 second/);
    });

    it('should validate delay within max bound (300s)', () => {
      const response = new Response(null, {
        status: 429,
        headers: { 'Retry-After': '600' },
      });

      const error = handleRateLimit(response, { maxDelayMs: 300000 });
      expect(error.message).toMatch(/300 seconds/);
    });

    it('should return ToolError with code=RATE_LIMIT and retryable=true', () => {
      const response = new Response(null, { status: 429 });
      const error = handleRateLimit(response);

      expect(error.code).toBe('RATE_LIMIT');
      expect(error.retryable).toBe(true);
      expect(error.suggestedAction).toBeDefined();
    });
  });
});

// =============================================================================
// REQ_009.3: Safe error handling tests
// =============================================================================

describe('REQ_009.3: Safe error handling with no API key exposure', () => {
  describe('redactSensitiveData', () => {
    it('should not include API keys in error messages', () => {
      const input = 'Error: Invalid API key sk-abcdefghijklmnopqrstuvwxyz123456';
      const sanitized = redactSensitiveData(input);

      expect(sanitized).not.toContain('sk-');
      expect(sanitized).toContain('[REDACTED]');
    });

    it('should sanitize file paths', () => {
      const input = 'Error at /Users/john/projects/api/keys.ts:42:10';
      const sanitized = redactSensitiveData(input);

      expect(sanitized).toContain('[REDACTED]');
    });

    it('should sanitize Bearer tokens', () => {
      const input = 'Authorization failed: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ';
      const sanitized = redactSensitiveData(input);

      expect(sanitized).toContain('[REDACTED]');
      expect(sanitized).not.toContain('eyJ');
    });

    it('should preserve error codes', () => {
      const input = 'RATE_LIMIT: Too many requests';
      const sanitized = redactSensitiveData(input);

      expect(sanitized).toContain('RATE_LIMIT');
    });
  });

  describe('redactHeaders', () => {
    it('should strip sensitive headers', () => {
      const headers = {
        'Content-Type': 'application/json',
        'Authorization': 'Bearer secret-token',
        'X-API-Key': 'my-api-key',
      };

      const redacted = redactHeaders(headers);

      expect(redacted['Content-Type']).toBe('application/json');
      expect(redacted['Authorization']).toBe('[REDACTED]');
      expect(redacted['X-API-Key']).toBe('[REDACTED]');
    });

    it('should handle Headers object', () => {
      const headers = new Headers();
      headers.set('Content-Type', 'application/json');
      headers.set('Authorization', 'Bearer token');

      const redacted = redactHeaders(headers);

      expect(redacted['content-type']).toBe('application/json');
      expect(redacted['authorization']).toBe('[REDACTED]');
    });

    it('should include all sensitive headers in SENSITIVE_HEADERS list', () => {
      expect(SENSITIVE_HEADERS).toContain('authorization');
      expect(SENSITIVE_HEADERS).toContain('x-api-key');
      expect(SENSITIVE_HEADERS).toContain('cookie');
    });
  });

  describe('sanitizeApiError', () => {
    it('should map OpenAI error codes to user-friendly messages', () => {
      const error = Object.assign(new Error('Invalid key'), { code: 'invalid_api_key' });
      const sanitized = sanitizeApiError(error);

      expect(sanitized.message).toBe(ERROR_MESSAGE_MAP.invalid_api_key);
    });

    it('should preserve error code for programmatic handling', () => {
      const error = Object.assign(new Error('Rate limit'), { code: 'rate_limit_exceeded' });
      const sanitized = sanitizeApiError(error);

      expect(sanitized.code).toBe('RATE_LIMIT');
    });

    it('should store original error for debugging', () => {
      const originalMessage = 'sk-abc123 is invalid at /path/to/file.ts';
      const error = new Error(originalMessage);
      const sanitized = sanitizeApiError(error);

      expect(sanitized.originalMessage).toBe(originalMessage);
      expect(sanitized.message).not.toContain('sk-');
    });

    it('should handle nested error objects safely', () => {
      const error = {
        error: {
          message: 'Nested error',
          code: 'API_ERROR',
        },
      };

      const sanitized = sanitizeApiError(error);
      expect(sanitized.code).toBe('API_ERROR');
    });

    it('should handle non-Error values', () => {
      const sanitized = sanitizeApiError('string error');
      expect(sanitized.code).toBe('API_ERROR');
      expect(sanitized.message).toBe('An unexpected error occurred');
    });
  });

  describe('createSafeToolError', () => {
    it('should create ToolError with generic message when sensitive data detected', () => {
      const error = new Error('sk-secret123 failed');
      const toolError = createSafeToolError(error);

      expect(toolError).toBeInstanceOf(ToolError);
      // Redacted message replaces sk-secret123, so message should not contain sk-
      // The sanitization detects redaction happened and uses generic message
      expect(toolError.message).toBe('An error occurred processing your request');
    });

    it('should log original error with full context when logger provided', () => {
      const mockLogger = {
        debug: vi.fn(),
        info: vi.fn(),
        warn: vi.fn(),
        error: vi.fn(),
        withContext: vi.fn(),
      };

      const error = new Error('Detailed error with sk-secret');
      createSafeToolError(error, mockLogger);

      expect(mockLogger.error).toHaveBeenCalledWith(
        'API error occurred',
        expect.objectContaining({
          error: error.message,
        })
      );
    });
  });
});

// =============================================================================
// REQ_009.4: Timeout handling tests
// =============================================================================

describe('REQ_009.4: Timeout handling', () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('TOOL_TIMEOUTS configuration', () => {
    it('should have image_generation timeout of 120s', () => {
      expect(TOOL_TIMEOUTS.image_generation).toBe(120000);
    });

    it('should have deep_research timeout of 300s', () => {
      expect(TOOL_TIMEOUTS.deep_research).toBe(300000);
    });

    it('should have deep_research_polling timeout of 1800s', () => {
      expect(TOOL_TIMEOUTS.deep_research_polling).toBe(1800000);
    });

    it('should have document_generation timeout of 60s', () => {
      expect(TOOL_TIMEOUTS.document_generation).toBe(60000);
    });

    it('should have chat_completion timeout of 30s', () => {
      expect(TOOL_TIMEOUTS.chat_completion).toBe(30000);
    });

    it('should have default timeout of 30s', () => {
      expect(TOOL_TIMEOUTS.default).toBe(30000);
    });
  });

  describe('getToolTimeout', () => {
    it('should return configured timeout for known tools', () => {
      expect(getToolTimeout('image_generation')).toBe(120000);
      expect(getToolTimeout('deep_research')).toBe(300000);
    });

    it('should return default for unknown tools', () => {
      expect(getToolTimeout('unknown_tool')).toBe(30000);
    });
  });

  describe('createTimeoutController', () => {
    it('should implement AbortController for cancellable requests', () => {
      const controller = createTimeoutController({ timeoutMs: 5000 });

      expect(controller.signal).toBeInstanceOf(AbortSignal);
      expect(controller.signal.aborted).toBe(false);
    });

    it('should abort after specified timeout', async () => {
      const onTimeout = vi.fn();
      const controller = createTimeoutController({
        timeoutMs: 1000,
        onTimeout,
      });

      expect(controller.signal.aborted).toBe(false);

      await vi.advanceTimersByTimeAsync(1000);

      expect(controller.signal.aborted).toBe(true);
      expect(controller.isTimeout()).toBe(true);
      expect(onTimeout).toHaveBeenCalled();
    });

    it('should clear timeout when operation completes', async () => {
      const onTimeout = vi.fn();
      const controller = createTimeoutController({
        timeoutMs: 1000,
        onTimeout,
      });

      controller.clear();
      await vi.advanceTimersByTimeAsync(2000);

      expect(controller.signal.aborted).toBe(false);
      expect(onTimeout).not.toHaveBeenCalled();
    });

    it('should support external abort signal', () => {
      const externalController = new AbortController();
      const controller = createTimeoutController({
        timeoutMs: 5000,
        signal: externalController.signal,
      });

      externalController.abort();

      expect(controller.signal.aborted).toBe(true);
      expect(controller.isTimeout()).toBe(false);
    });

    it('should handle already aborted external signal', () => {
      const externalController = new AbortController();
      externalController.abort();

      const controller = createTimeoutController({
        timeoutMs: 5000,
        signal: externalController.signal,
      });

      expect(controller.signal.aborted).toBe(true);
    });
  });

  describe('fetchWithTimeout', () => {
    it('should throw ToolError with code=TIMEOUT on timeout', async () => {
      vi.useRealTimers(); // Use real timers for fetch

      const mockFetch = vi.fn().mockImplementation(
        () => new Promise((_, reject) => {
          // Simulate AbortController aborting
          setTimeout(() => {
            const error = new DOMException('Aborted', 'AbortError');
            reject(error);
          }, 50);
        })
      );
      global.fetch = mockFetch;

      // Use very short timeout
      await expect(fetchWithTimeout('/api/test', {}, 10)).rejects.toMatchObject({
        code: 'TIMEOUT',
      });
    }, 10000);

    it('should include suggested action in timeout error', () => {
      // Test the factory method directly
      const error = ToolError.timeout(30000);
      expect(error.suggestedAction).toBeDefined();
      expect(error.suggestedAction).toContain('simpler query');
    });

    it('should clean up timeout on successful response', async () => {
      vi.useRealTimers();
      const mockFetch = vi.fn().mockResolvedValue(new Response('OK'));
      global.fetch = mockFetch;

      const response = await fetchWithTimeout('/api/test', {}, 5000);

      expect(response).toBeInstanceOf(Response);
      expect(mockFetch).toHaveBeenCalled();
    });
  });
});

// =============================================================================
// REQ_009.5: Structured logging tests
// =============================================================================

describe('REQ_009.5: Structured logging format', () => {
  let consoleSpy: {
    log: ReturnType<typeof vi.spyOn>;
    warn: ReturnType<typeof vi.spyOn>;
    error: ReturnType<typeof vi.spyOn>;
    debug: ReturnType<typeof vi.spyOn>;
  };

  beforeEach(() => {
    consoleSpy = {
      log: vi.spyOn(console, 'log').mockImplementation(() => {}),
      warn: vi.spyOn(console, 'warn').mockImplementation(() => {}),
      error: vi.spyOn(console, 'error').mockImplementation(() => {}),
      debug: vi.spyOn(console, 'debug').mockImplementation(() => {}),
    };
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('createLogEntry', () => {
    it('should include timestamp, level, tool, code, message, correlationId, metadata', () => {
      const context: LogContext = {
        tool: 'image_generation',
        correlationId: 'abc123',
      };

      const entry = createLogEntry('error', 'Test message', context, { key: 'value' });

      expect(entry.timestamp).toBeDefined();
      expect(new Date(entry.timestamp).getTime()).not.toBeNaN();
      expect(entry.level).toBe('error');
      expect(entry.tool).toBe('image_generation');
      expect(entry.correlationId).toBe('abc123');
      expect(entry.metadata).toEqual({ key: 'value' });
    });

    it('should automatically redact sensitive data from logs', () => {
      const context: LogContext = { tool: 'test' };
      const entry = createLogEntry('error', 'API key sk-abc123 failed', context, {
        apiKey: 'sk-secret123',
      });

      // Message should have sk-abc123 redacted
      expect(entry.message).toContain('[REDACTED]');
      expect(entry.message).not.toContain('sk-abc123');
      // Metadata should have apiKey redacted
      expect(JSON.stringify(entry.metadata)).toContain('[REDACTED]');
    });
  });

  describe('formatLogEntry', () => {
    it('should be JSON-formatted for log aggregation tools', () => {
      const entry: StructuredLogEntry = {
        timestamp: '2024-01-01T00:00:00.000Z',
        level: 'error',
        tool: 'test',
        message: 'Test',
      };

      const formatted = formatLogEntry(entry);
      const parsed = JSON.parse(formatted);

      expect(parsed).toEqual(entry);
    });
  });

  describe('createStructuredLogger', () => {
    it('should use ERROR for failures', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      logger.error('Test error', { code: 'API_ERROR' });

      expect(consoleSpy.error).toHaveBeenCalled();
    });

    it('should use WARN for retryable errors', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      logger.warn('Retryable error', { retryable: true });

      expect(consoleSpy.warn).toHaveBeenCalled();
    });

    it('should use INFO for recoveries', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      logger.info('Recovered');

      expect(consoleSpy.log).toHaveBeenCalled();
    });

    it('should include contextual metadata', () => {
      const logger = createStructuredLogger({
        tool: 'image_generation',
        correlationId: 'corr123',
        userId: 'user456',
      });

      logger.info('Test');

      const logCall = consoleSpy.log.mock.calls[0][0];
      const parsed = JSON.parse(logCall);

      expect(parsed.tool).toBe('image_generation');
      expect(parsed.correlationId).toBe('corr123');
    });

    it('should support withContext for updating context', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      const contextLogger = logger.withContext({ requestId: 'req123' });

      contextLogger.info('Test');

      const logCall = consoleSpy.log.mock.calls[0][0];
      const parsed = JSON.parse(logCall);

      expect(parsed.tool).toBe('test');
    });

    it('should integrate with existing console.error pattern', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      logger.error('Test error');

      expect(consoleSpy.error).toHaveBeenCalled();
    });
  });

  describe('generateCorrelationId', () => {
    it('should generate unique correlation IDs', () => {
      const id1 = generateCorrelationId();
      const id2 = generateCorrelationId();

      expect(id1).not.toBe(id2);
      expect(typeof id1).toBe('string');
      expect(id1.length).toBeGreaterThan(0);
    });
  });

  describe('logToolError', () => {
    it('should use ERROR level for non-retryable errors', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      const error = new ToolError('Fatal error', 'API_ERROR', false);

      logToolError(logger, error);

      expect(consoleSpy.error).toHaveBeenCalled();
    });

    it('should use WARN level for retryable errors', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      const error = new ToolError('Retry later', 'RATE_LIMIT', true);

      logToolError(logger, error);

      expect(consoleSpy.warn).toHaveBeenCalled();
    });

    it('should include error code in log metadata', () => {
      const logger = createStructuredLogger({ tool: 'test' });
      const error = new ToolError('Test', 'TIMEOUT', true);

      logToolError(logger, error);

      const logCall = consoleSpy.warn.mock.calls[0][0];
      const parsed = JSON.parse(logCall);

      expect(parsed.metadata?.code).toBe('TIMEOUT');
    });
  });
});

// =============================================================================
// Utility function tests
// =============================================================================

describe('Utility functions', () => {
  describe('isToolError', () => {
    it('should return true for ToolError instances', () => {
      const error = new ToolError('Test', 'API_ERROR', false);
      expect(isToolError(error)).toBe(true);
    });

    it('should return false for regular Error', () => {
      const error = new Error('Test');
      expect(isToolError(error)).toBe(false);
    });

    it('should return false for non-Error values', () => {
      expect(isToolError('string')).toBe(false);
      expect(isToolError(null)).toBe(false);
      expect(isToolError(undefined)).toBe(false);
    });
  });

  describe('toToolError', () => {
    it('should return existing ToolError unchanged', () => {
      const original = new ToolError('Test', 'API_ERROR', false);
      const result = toToolError(original);

      expect(result).toBe(original);
    });

    it('should convert AbortError to timeout ToolError', () => {
      // Create an error that mimics AbortError (in Node.js, DOMException may not be available)
      const abortError = Object.assign(new Error('Aborted'), { name: 'AbortError' });
      const result = toToolError(abortError);

      expect(result.code).toBe('TIMEOUT');
    });

    it('should convert DOMException AbortError to timeout ToolError', () => {
      // Test with actual DOMException if available
      if (typeof DOMException !== 'undefined') {
        const abortError = new DOMException('Aborted', 'AbortError');
        const result = toToolError(abortError);
        expect(result.code).toBe('TIMEOUT');
      }
    });

    it('should convert network errors', () => {
      const networkError = Object.assign(new Error('Connection failed'), {
        code: 'ECONNREFUSED',
      });
      const result = toToolError(networkError);

      expect(result.code).toBe('NETWORK');
      expect(result.retryable).toBe(true);
    });

    it('should convert unknown errors to API_ERROR', () => {
      const result = toToolError('some string');

      expect(result.code).toBe('API_ERROR');
    });
  });
});

// =============================================================================
// Integration tests
// =============================================================================

describe('Integration tests', () => {
  it('should create complete error flow from API error to logged response', () => {
    const consoleSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    const originalError = Object.assign(new Error('API failed'), {
      code: 'rate_limit_exceeded',
    });

    const logger = createStructuredLogger({
      tool: 'image_generation',
      correlationId: generateCorrelationId(),
    });

    const toolError = createSafeToolError(originalError, logger);

    expect(toolError).toBeInstanceOf(ToolError);
    expect(toolError.code).toBe('RATE_LIMIT');
    expect(consoleSpy).toHaveBeenCalled();

    consoleSpy.mockRestore();
  });

  it('should handle timeout flow with cleanup', async () => {
    vi.useFakeTimers();

    const cleanup = vi.fn();
    const controller = createTimeoutController({
      timeoutMs: 1000,
      onTimeout: cleanup,
    });

    await vi.advanceTimersByTimeAsync(1000);

    expect(controller.isTimeout()).toBe(true);
    expect(cleanup).toHaveBeenCalled();

    vi.useRealTimers();
  });
});
