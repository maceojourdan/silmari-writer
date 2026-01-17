# Phase 02: The system must support Deep Research tool configu...

## Requirements

### REQ_001: The system must support Deep Research tool configuration inc

The system must support Deep Research tool configuration including web_search_preview, code_interpreter, file_search, and mcp tools

#### REQ_001.1: Implement web_search_preview tool with configurable domains,

Implement web_search_preview tool with configurable domains, search_context_size (low/medium/high), and user_location parameters for Deep Research API integration

##### Testable Behaviors

1. web_search_preview tool can be enabled/disabled in Deep Research requests via UI toggle
2. domains parameter accepts an array of allowed domains (whitelist mode) OR blocked domains (blacklist mode) with clear mode indicator
3. search_context_size parameter supports 'low', 'medium', 'high' enum values that control context token usage and API costs
4. user_location parameter accepts ISO 3166-1 alpha-2 country code (required) and optional city/region strings for geo-relevant results
5. Domain patterns are validated using regex before API call (format: example.com, not https://example.com/path)
6. Invalid domain patterns return validation errors with specific pattern that failed
7. Empty domains array defaults to unrestricted web search with confirmation prompt
8. Configuration persists to user preferences store across conversation sessions
9. UI displays active search restrictions summary before research begins (e.g., '3 domains whitelisted, US location')
10. search_context_size displays estimated token cost tooltip: low (~500 tokens), medium (~2000 tokens), high (~5000 tokens)
11. Location autocomplete uses a country/city database for valid selections
12. Tool configuration is serialized correctly for OpenAI Responses API format: { type: 'web_search_preview', domains: [...], search_context_size: '...', user_location: {...} }

#### REQ_001.2: Support code_interpreter tool execution for Deep Research wi

Support code_interpreter tool execution for Deep Research with session cost tracking ($0.03/session), result extraction, and file download capabilities

##### Testable Behaviors

1. code_interpreter tool can be enabled/disabled in Deep Research requests via simple toggle switch
2. No additional configuration parameters required - tool object is simply { type: 'code_interpreter' }
3. Code execution results are extracted from response.output array by filtering items where type === 'code_interpreter_call'
4. Execution stdout/stderr outputs are captured and displayed in formatted code blocks
5. Session cost ($0.03/session) is tracked per Deep Research request and displayed to user
6. Cumulative session costs are aggregated in user's usage dashboard
7. Code execution errors are parsed and displayed with syntax-highlighted stack traces
8. Generated files (charts, CSVs, images) are extracted from response and made downloadable
9. Tool is disabled by default to prevent unexpected costs - requires explicit user opt-in
10. Cost acknowledgment checkbox required before first-time enablement
11. Session status indicator shows 'Code Running' during active code execution phases
12. Execution timeout errors (if any) display clear message with execution time limit info

#### REQ_001.3: Enable file_search tool with vector_store_ids support allowi

Enable file_search tool with vector_store_ids support allowing maximum of 2 vector stores for semantic document retrieval during Deep Research

##### Testable Behaviors

1. file_search tool accepts vector_store_ids parameter with array of 1-2 vector store ID strings
2. Attempting to configure more than 2 vector stores returns clear validation error: 'Maximum 2 vector stores allowed'
3. Vector store IDs are validated against OpenAI's vector store API to verify existence before research begins
4. Invalid or non-existent vector_store_id returns error: 'Vector store {id} not found or access denied'
5. UI displays user's existing vector stores with name, document count, and creation date for selection
6. Vector store multi-select component enforces max 2 selection with visual indicator
7. File search results include source document references with filename, page/chunk number, and relevance score
8. Empty vector_store_ids array (or omitted) disables file_search tool from request
9. Vector store ID format is validated using regex before API call (format: vs_xxxxx)
10. Selected vector stores persist as user preference for future research tasks
11. UI allows creating new vector store via file upload flow integrated with OpenAI Vector Stores API
12. Vector store status (ready/processing/failed) is checked and displayed before allowing selection

#### REQ_001.4: Implement mcp (Model Context Protocol) tool with server_url 

Implement mcp (Model Context Protocol) tool with server_url validation (HTTPS required) and require_approval settings for secure custom data source integration

##### Testable Behaviors

1. mcp tool accepts server_url parameter pointing to MCP-compliant server endpoint
2. server_url is strictly validated for HTTPS protocol - HTTP URLs are rejected with error: 'MCP servers require HTTPS'
3. server_url format is validated as valid URL with proper hostname
4. require_approval boolean (default: true) controls whether MCP tool calls need explicit user approval
5. When require_approval is true, UI shows approval dialog before each MCP tool invocation with tool name and input preview
6. MCP server connection is verified via health check endpoint before research begins
7. Failed MCP server connections (timeout, 4xx, 5xx) display clear error with server URL and status code
8. Multiple MCP tools can be configured with different server URLs in single research request
9. MCP tool invocation history is logged with timestamp, server_url, tool_name, input, output for audit
10. User can configure 'trusted' MCP servers that bypass require_approval for future requests
11. Trusted server list is stored per-user and manageable via settings UI
12. MCP server URL is checked against configurable blocklist of known malicious endpoints
13. Approval timeout (60 seconds default) auto-rejects pending approvals to prevent blocking

#### REQ_001.5: Process and display intermediate reasoning steps and web_sea

Process and display intermediate reasoning steps and web_search_call queries for transparency into the Deep Research agent's investigation process

##### Testable Behaviors

1. Intermediate reasoning steps are extracted by filtering response.output items where type === 'reasoning'
2. Each reasoning step's summary field is extracted and displayed chronologically
3. Both 'auto' and 'detailed' reasoning summary modes are supported with appropriate display formatting
4. web_search_call items are filtered from response.output where type === 'web_search_call'
5. Search query text is extracted from each web_search_call item's query field
6. Reasoning steps and search queries are displayed in unified timeline view showing research progression
7. Timeline entries include step type icon (💭 reasoning, 🔍 search), timestamp/order, and content
8. 'Show AI's thinking' toggle allows user to expand/collapse transparency panel
9. Transparency panel is collapsed by default to reduce visual clutter
10. Real-time streaming updates append new reasoning steps and search queries as they occur (background mode)
11. Step count badges show total reasoning steps and search queries performed
12. Individual reasoning steps are expandable/collapsible for detailed vs summary view
13. Search queries are displayed as clickable chips that could trigger manual re-search (future feature)
14. Empty reasoning or search arrays display 'No intermediate steps recorded' message


## Success Criteria

- [ ] All tests pass
- [ ] All behaviors implemented
- [ ] Code reviewed