# Phase 01: The system must integrate OpenAI Deep Research API...

## Requirements

### REQ_000: The system must integrate OpenAI Deep Research API capabilit

The system must integrate OpenAI Deep Research API capabilities for autonomous research with citation-rich reports

#### REQ_000.1: Implement POST requests to https://api.openai.com/v1/respons

Implement POST requests to https://api.openai.com/v1/responses endpoint with o3-deep-research and o4-mini-deep-research models for autonomous research execution

##### Testable Behaviors

1. POST requests are sent to https://api.openai.com/v1/responses with correct Authorization header using Bearer token
2. Request body includes model field set to either 'o3-deep-research-2025-06-26' or 'o4-mini-deep-research-2025-06-26'
3. OpenAI API key is securely retrieved from environment variable OPENAI_API_KEY
4. Content-Type header is set to 'application/json' for all requests
5. Request timeout is configured to handle long-running operations (minimum 120 seconds for non-background mode)
6. HTTP errors (4xx, 5xx) are caught and transformed into typed DeepResearchApiError with status code and message
7. Rate limit errors (429) trigger exponential backoff retry with maximum 3 attempts
8. Network failures trigger retry with 2-second base delay and exponential backoff
9. Response body is validated against expected DeepResearchResponse schema before processing
10. API version header 'OpenAI-Beta: responses=v1' is included if required by API documentation
11. Request/response logging captures timing, model used, and response size for monitoring
12. Unit tests mock OpenAI API and verify correct request formation for both models

#### REQ_000.2: Support developer and user role message inputs with input_te

Support developer and user role message inputs with input_text content type for proper prompt structuring in Deep Research requests

##### Testable Behaviors

1. Input array supports objects with role: 'developer' for system-level instructions
2. Input array supports objects with role: 'user' for research queries
3. Each message content is formatted as array with {type: 'input_text', text: string} objects
4. Developer messages can set research guidelines, output format preferences, and domain constraints
5. User messages contain the actual research query to be investigated
6. Multiple user messages in sequence are supported for multi-turn context
7. Empty or whitespace-only text content returns validation error before API call
8. Maximum text length per message is enforced (32,000 characters based on API limits)
9. Developer role messages are optional - user role messages are required
10. Message order is preserved: developer messages should precede user messages
11. Special characters and unicode in text content are properly encoded
12. Unit tests verify correct message structure formation for various input combinations

#### REQ_000.3: Configure reasoning summary options (auto or detailed) based

Configure reasoning summary options (auto or detailed) based on research depth preference to control the verbosity of intermediate thinking steps returned by the API

##### Testable Behaviors

1. Request includes reasoning object with summary field set to 'auto' or 'detailed'
2. When summary='auto', API returns concise reasoning summaries suitable for quick overview
3. When summary='detailed', API returns comprehensive reasoning with full thought process
4. Default reasoning summary is 'auto' when user does not specify preference
5. For depth='thorough' requests, reasoning defaults to 'detailed' for full transparency
6. For depth='quick' requests, reasoning defaults to 'auto' for efficiency
7. User can override default reasoning level regardless of depth selection
8. Invalid reasoning summary values return validation error before API call
9. Reasoning summary preference is stored in user settings for future requests
10. UI clearly explains the difference between auto and detailed reasoning options
11. Token usage difference between auto and detailed is displayed to user
12. Unit tests verify correct reasoning object formation for all option combinations

#### REQ_000.4: Enable background mode (background: true) for long-running r

Enable background mode (background: true) for long-running research tasks that can take tens of minutes, allowing non-blocking request submission and async result retrieval

##### Testable Behaviors

1. Request includes background: true parameter to enable async execution mode
2. API immediately returns job metadata including unique job ID and status URL
3. Job ID is in UUID format and uniquely identifies the research task
4. Status URL follows pattern /api/tools/deep-research/{jobId}/status
5. Initial response includes estimated completion time range (e.g., 5-30 minutes)
6. Job metadata includes created_at timestamp and model used
7. Background mode is enabled by default for all deep research requests
8. Non-background mode (background: false) is supported for testing but discouraged in production
9. Job metadata is stored in database for persistence across server restarts
10. User can view list of their pending/completed research jobs
11. Jobs are automatically cleaned up after 24 hours to free storage
12. Unit tests verify background mode request formation and response parsing

#### REQ_000.5: Implement polling mechanism for background task completion n

Implement polling mechanism for background task completion notification, allowing clients to check job status at intervals until research completes or fails

##### Testable Behaviors

1. GET endpoint /api/tools/deep-research/{jobId}/status returns current job status
2. Status response includes: status ('pending'|'processing'|'completed'|'failed'), progress info, result or error
3. Polling interval starts at 5 seconds and increases to 30 seconds for long-running jobs (adaptive)
4. Client stops polling when status is 'completed' or 'failed'
5. Progress object includes current step description and optional percentage (0-100)
6. Completed status includes full DeepResearchResult with text, citations, and reasoning steps
7. Failed status includes error message and error code for debugging
8. Status endpoint returns 404 for non-existent job IDs with clear error message
9. Status endpoint returns 403 for job IDs belonging to other users
10. Client handles network errors during polling with automatic retry
11. UI displays real-time progress updates as polling retrieves new status
12. Unit tests verify polling logic with various status transitions


## Success Criteria

- [x] All tests pass (47 tests for Phase 1)
- [x] All behaviors implemented
- [ ] Code reviewed

## Implementation Summary

### Files Created
- `frontend/src/app/api/tools/deep-research/route.ts` - Main POST endpoint
- `frontend/src/app/api/tools/deep-research/[jobId]/status/route.ts` - Status polling endpoint
- `frontend/__tests__/api/deep-research.test.ts` - 34 tests for POST endpoint
- `frontend/__tests__/api/deep-research-status.test.ts` - 13 tests for status endpoint

### Key Features Implemented
1. POST requests to OpenAI Deep Research API with o3 and o4-mini models
2. Developer/user role message inputs with input_text content type
3. Reasoning summary options (auto/detailed) with depth-based defaults
4. Background mode for async execution with job metadata
5. Polling endpoint for job status with progress tracking