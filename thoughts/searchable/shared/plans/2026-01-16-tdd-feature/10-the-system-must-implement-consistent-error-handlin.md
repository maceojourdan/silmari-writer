# Phase 10: The system must implement consistent error handlin...

## Requirements

### REQ_009: The system must implement consistent error handling patterns

The system must implement consistent error handling patterns across all tool handlers with structured error responses

#### REQ_009.1: Define ToolError interface with code, message, retryable fla

Define ToolError interface with code, message, retryable flag, and suggestedAction fields as the foundation for consistent error handling across all tool handlers

##### Testable Behaviors

1. ToolError interface includes code field as union type: 'RATE_LIMIT' | 'INVALID_REQUEST' | 'API_ERROR' | 'TIMEOUT' | 'NETWORK' | 'CONFIG_ERROR' | 'VALIDATION_ERROR'
2. ToolError interface includes message field as string for human-readable error description
3. ToolError interface includes retryable boolean field indicating whether the operation can be retried
4. ToolError interface includes optional suggestedAction field as string with user-actionable guidance
5. ToolErrorCode type alias is exported for type-safe error code usage
6. Interface extends Error class to support stack traces and instanceof checks
7. ToolError class constructor accepts (message, code, retryable, suggestedAction?) parameters
8. Interface is compatible with existing TranscriptionError and ChatGenerationError patterns
9. toJSON() method returns serializable object for API responses
10. Static factory methods exist: ToolError.rateLimit(), ToolError.timeout(), ToolError.apiError(), ToolError.network()
11. Unit tests verify interface shape matches OpenAPI/JSON schema requirements
12. Interface documentation includes JSDoc comments explaining each field's purpose

#### REQ_009.2: Implement rate limit error handling with Retry-After header 

Implement rate limit error handling with Retry-After header parsing for intelligent backoff timing across all tool handlers

##### Testable Behaviors

1. Detects HTTP 429 status code from OpenAI API responses
2. Parses Retry-After header when present (supports both seconds format and HTTP-date format)
3. Falls back to configurable default delay (10 seconds) when Retry-After header is missing
4. Converts Retry-After HTTP-date format to milliseconds remaining
5. Validates parsed delay is within acceptable bounds (min 1s, max 300s)
6. Returns ToolError with code='RATE_LIMIT', retryable=true, and suggestedAction including wait time
7. Emits rate limit event for monitoring/alerting systems
8. Integrates with existing exponential backoff logic (10s base, 2x multiplier)
9. Unit tests cover: numeric Retry-After, date Retry-After, missing header, invalid values
10. Handles rate limits from different OpenAI endpoints (responses, images, chat)
11. Logs rate limit occurrences with endpoint, delay, and attempt number

#### REQ_009.3: Handle API errors with safe error messages ensuring no API k

Handle API errors with safe error messages ensuring no API key exposure or sensitive data leakage in error responses

##### Testable Behaviors

1. API keys are never included in error messages sent to clients
2. Error messages are sanitized to remove file paths, stack traces, and internal details
3. Original full error is logged server-side for debugging with appropriate log level
4. OpenAI API error messages are mapped to user-friendly equivalents
5. Sensitive headers (Authorization, x-api-key) are stripped from logged requests
6. Request/response bodies containing credentials are redacted before logging
7. Error codes are preserved for programmatic handling while messages are sanitized
8. Creates ToolError with generic message but logs original error with full context
9. Handles nested error objects and error chains safely
10. Unit tests verify no sensitive data appears in sanitized output
11. Integration tests confirm API keys are not exposed in any error scenario
12. Maintains error traceability via correlation IDs without exposing internals

#### REQ_009.4: Implement timeout handling with configurable durations per t

Implement timeout handling with configurable durations per tool type, supporting both short synchronous operations and long-running background tasks

##### Testable Behaviors

1. Each tool type has configurable timeout: image_generation (120s), deep_research (300s initial, 1800s polling), document_generation (60s), chat_completion (30s)
2. Timeout is implemented using AbortController for cancellable requests
3. Timeout error returns ToolError with code='TIMEOUT', retryable=true, suggestedAction='Try again or use a simpler query'
4. Background tasks (deep_research) have separate initial request timeout vs total polling timeout
5. User can cancel long-running operations via UI abort button
6. Partial results are preserved when timeout occurs during streaming responses
7. Timeout configuration is overridable per-request for special cases
8. Cleanup functions run on timeout (e.g., abort pending fetch, release resources)
9. Unit tests verify timeout triggers at correct duration for each tool
10. Timeout events are logged with tool type, configured duration, and elapsed time
11. Handles both fetch timeouts and SDK operation timeouts consistently

#### REQ_009.5: Log errors with structured logging format for monitoring, de

Log errors with structured logging format for monitoring, debugging, and alerting integration across all tool handlers

##### Testable Behaviors

1. All tool errors are logged with consistent structured format: { timestamp, level, tool, code, message, correlationId, metadata }
2. Log levels are appropriate: ERROR for failures, WARN for retryable errors, INFO for recoveries
3. Correlation ID links related log entries across request lifecycle
4. Sensitive data is automatically redacted from logs (API keys, user data)
5. Error stack traces are captured in development but summarized in production
6. Logs include contextual metadata: userId, sessionId, requestId, tool, operation
7. Integration with existing console.error pattern for backward compatibility
8. Structured logs are JSON-formatted for log aggregation tools (e.g., DataDog, CloudWatch)
9. Error frequency and patterns can be queried from logs
10. Log retention considers compliance requirements (PII minimization)
11. Unit tests verify log output format and content for various error scenarios
12. Performance: logging adds <1ms overhead to error handling path


## Success Criteria

- [ ] All tests pass
- [ ] All behaviors implemented
- [ ] Code reviewed