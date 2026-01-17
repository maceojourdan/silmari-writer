# Phase 09: The system must implement Deep Research Handler th...

## Requirements

### REQ_008: The system must implement Deep Research Handler that execute

The system must implement Deep Research Handler that executes research queries with configurable depth and returns text with citations

#### REQ_008.1: Implement depth parameter selection that routes to o4-mini-d

Implement depth parameter selection that routes to o4-mini-deep-research (~$3/query) for 'quick' depth and o3-deep-research (~$30/query) for 'thorough' depth, with cost estimation displayed before execution

##### Testable Behaviors

1. TypeScript type defines depth options: 'quick' | 'thorough' with corresponding model mappings
2. Default depth is 'quick' to avoid unexpected high costs unless explicitly requested
3. Depth 'quick' maps to model 'o4-mini-deep-research-2025-06-26' (~$3 average per query)
4. Depth 'thorough' maps to model 'o3-deep-research-2025-06-26' (~$30 average per query)
5. Cost estimation is displayed before research execution with depth selection
6. User must acknowledge cost estimate for 'thorough' depth (>$10 estimated)
7. Depth selection persists in user preferences for future research tasks
8. Model name is validated against allowed models before API call
9. Invalid depth values return 400 status with descriptive error message
10. Depth selection is logged for cost tracking and analytics purposes

#### REQ_008.2: Create /api/tools/deep-research POST endpoint with Zod valid

Create /api/tools/deep-research POST endpoint with Zod validation for request body, rate limiting to prevent API abuse, and structured error responses following existing patterns from generate and transcribe routes

##### Testable Behaviors

1. POST /api/tools/deep-research endpoint accepts JSON body with query, depth, tools, and systemPrompt fields
2. Request body is validated using Zod schema with required 'query' field (string, 1-10000 chars)
3. Optional 'depth' field validates against 'quick' | 'thorough' enum, defaults to 'quick'
4. Optional 'tools' array validates tool objects (web_search_preview, code_interpreter)
5. Optional 'systemPrompt' field for developer-role instructions (max 5000 chars)
6. Rate limiting enforces max 5 requests per minute per API key for thorough depth
7. Rate limiting enforces max 20 requests per minute per API key for quick depth
8. 429 status returned when rate limit exceeded with Retry-After header
9. API key validation returns 401 if OPENAI_API_KEY environment variable missing
10. Request logging captures query (truncated to 200 chars), depth, tool count, timestamp
11. Response follows existing pattern: { result: DeepResearchResult } on success
12. Error responses follow pattern: { error: string, code: string, retryable: boolean }
13. DeepResearchError class extends Error with code and retryable properties matching existing ChatGenerationError pattern

#### REQ_008.3: Configure web_search_preview tool (enabled by default) and o

Configure web_search_preview tool (enabled by default) and optional code_interpreter tool with background mode enabled for long-running research tasks, following OpenAI Responses API tool specification

##### Testable Behaviors

1. web_search_preview tool is included by default in all Deep Research requests
2. web_search_preview tool object format: { type: 'web_search_preview' }
3. Optional web_search_preview config supports domains, search_context_size, user_location
4. code_interpreter tool is opt-in and requires explicit user selection
5. code_interpreter tool object format: { type: 'code_interpreter' }
6. code_interpreter cost warning ($0.03/session) displayed when enabled
7. background: true is always set for Deep Research requests
8. Background mode returns response ID for polling instead of blocking
9. Tool array is validated to contain only supported tool types
10. Empty tools array defaults to [{ type: 'web_search_preview' }]
11. Duplicate tools are deduplicated before API call
12. Tool configuration is serialized correctly in API request body

#### REQ_008.4: Implement polling mechanism with exponential backoff startin

Implement polling mechanism with exponential backoff starting at 5 seconds and capping at 60 seconds between polls, with maximum 30 minute total duration before timeout, for background mode Deep Research tasks

##### Testable Behaviors

1. Initial poll occurs 5 seconds after background task creation
2. Poll interval doubles with each attempt: 5s → 10s → 20s → 40s → 60s (capped)
3. Maximum poll interval is 60 seconds between attempts
4. Total polling duration caps at 30 minutes (1800 seconds) before timeout
5. Timeout error includes elapsed time and suggests thorough depth may need longer
6. Poll request uses GET /v1/responses/{response_id} to check status
7. Status 'completed' triggers result extraction and callback
8. Status 'in_progress' continues polling with next backoff interval
9. Status 'failed' triggers error handling with API error details
10. Progress updates are emitted during polling (step count, elapsed time)
11. Polling can be cancelled by user via AbortController
12. Network errors during polling trigger retry with same interval (max 3 retries per poll)
13. Final result is cached to prevent redundant API calls

#### REQ_008.5: Extract final report text from response.output[-1].content[0

Extract final report text from response.output[-1].content[0].text and citations from response.output[-1].content[0].annotations array, with null safety and structured parsing following OpenAI Responses API format

##### Testable Behaviors

1. Final report text extracted from response.output[-1].content[0].text path
2. Returns empty string with warning log if output array is empty or undefined
3. Returns empty string with warning log if content array is empty or undefined
4. Returns empty string with warning log if text field is null, undefined, or empty
5. Citations extracted from response.output[-1].content[0].annotations array
6. Each citation includes: title (string), url (string), start_index (number), end_index (number)
7. Invalid citation URLs are filtered out with warning logged
8. Duplicate citations (same URL) are deduplicated preserving first occurrence
9. Citations array returns empty array [] (not null) when no annotations present
10. Markdown formatting in report text is preserved exactly as returned
11. Parser handles both o3 and o4-mini response formats (same structure)
12. Parser validates response shape before extraction with descriptive errors
13. Unit tests cover: empty response, null content, malformed annotations, valid response


## Success Criteria

- [ ] All tests pass
- [ ] All behaviors implemented
- [ ] Code reviewed