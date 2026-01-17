# Phase 11: The system must track and display cost estimates f...

## Requirements

### REQ_010: The system must track and display cost estimates for expensi

The system must track and display cost estimates for expensive operations before execution

#### REQ_010.1: Display estimated costs for Deep Research queries (~$3 quick

Display estimated costs for Deep Research queries (~$3 quick, ~$30 thorough) before execution to allow user to make informed decisions about research depth selection

##### Testable Behaviors

1. Cost estimate displays immediately when user selects research depth (quick vs thorough)
2. Quick depth shows estimated cost range of $2-$5 with average ~$3 for o4-mini-deep-research
3. Thorough depth shows estimated cost range of $20-$40 with average ~$30 for o3-deep-research
4. Cost breakdown shows base model cost plus additional tool costs (web search, code interpreter)
5. Estimated token usage is displayed alongside cost estimate
6. Cost estimate updates dynamically as user toggles additional tools (code_interpreter, file_search)
7. Warning indicator appears when estimated cost exceeds user-defined threshold (configurable)
8. Cost estimate tooltip explains pricing factors: input tokens, output tokens, tool calls
9. Historical cost comparison shows average actual costs from user's previous similar queries
10. Unit tests verify correct cost calculations for all model and tool combinations

#### REQ_010.2: Show image generation costs based on model and quality selec

Show image generation costs based on model and quality selection (~$0.01-$0.19) with real-time updates as user adjusts parameters

##### Testable Behaviors

1. Cost display updates in real-time as user changes model, quality, size, and count parameters
2. Low quality shows ~$0.01-$0.02 per image depending on model
3. Medium quality shows ~$0.04-$0.07 per image depending on model
4. High quality shows ~$0.17-$0.19 per image depending on model
5. Total cost calculated as (per-image cost × image count) and displayed prominently
6. Model comparison widget shows cost difference between gpt-image-1.5, gpt-image-1, and gpt-image-1-mini
7. Size parameter impact on cost is shown (if applicable for selected model)
8. Cost estimate includes note about potential prompt revision tokens
9. Batch generation (n > 1) shows per-image cost AND total cost clearly
10. Cost comparison with previous generation requests shown for context

#### REQ_010.3: Track code_interpreter session costs ($0.03/session) and web

Track code_interpreter session costs ($0.03/session) and web search costs ($0.01/call) during Deep Research execution for accurate billing

##### Testable Behaviors

1. Each code_interpreter session activation is tracked and logged with $0.03 cost
2. Each web_search_preview call is tracked and logged with $0.01 cost
3. Running cost total is updated in real-time during Deep Research execution
4. Cost tracker distinguishes between different types of tool calls in the same request
5. Session costs are aggregated correctly when multiple code_interpreter sessions occur
6. Web search call count is extracted from response.output items where type === 'web_search_call'
7. Tool costs are added to base model costs for complete cost picture
8. Cost tracking persists across polling intervals for background mode requests
9. Failed tool calls that still incur charges are tracked appropriately
10. Cost tracker provides breakdown: { modelCost, webSearchCost, codeInterpreterCost, totalCost }

#### REQ_010.4: Implement cost confirmation dialog before executing high-cos

Implement cost confirmation dialog before executing high-cost operations to prevent accidental expensive API calls

##### Testable Behaviors

1. Confirmation dialog appears when estimated cost exceeds user-configurable threshold (default: $5)
2. Dialog clearly displays estimated cost, cost breakdown, and operation details
3. User must explicitly click 'Confirm' to proceed with high-cost operation
4. Option to 'Remember my choice' for this session to avoid repeated confirmations
5. Alternative lower-cost options are suggested in the dialog (e.g., 'Use quick mode instead: ~$3')
6. Dialog shows user's remaining budget if spending limits are configured
7. Cancel button returns user to parameter selection without API call
8. Keyboard shortcuts: Enter to confirm, Escape to cancel
9. Confirmation is logged for audit trail with timestamp and user acknowledgment
10. Threshold can be adjusted per-tool type (different threshold for research vs images)
11. Dialog is accessible (ARIA labels, focus trap, screen reader support)

#### REQ_010.5: Log actual costs for billing tracking and analytics to enabl

Log actual costs for billing tracking and analytics to enable cost monitoring, budget management, and usage reporting

##### Testable Behaviors

1. Actual costs from API responses are logged with request ID, timestamp, and user ID
2. Token usage is captured from response.usage object (input_tokens, output_tokens, cached_tokens)
3. Actual cost is calculated from token usage using current pricing rates
4. Discrepancy detection alerts when actual cost differs significantly from estimate (>20%)
5. Cost logs are queryable by date range, user, operation type, and tool
6. Daily/weekly/monthly cost aggregations are calculated and stored
7. Cost analytics dashboard shows spending trends, top operations, and averages
8. Export functionality for cost reports (CSV, JSON)
9. Retention policy respects data privacy requirements (configurable retention period)
10. Real-time cost webhook notifications when spending exceeds thresholds
11. Cost logs include operation metadata: model, tools used, input length, output length


## Success Criteria

- [ ] All tests pass
- [ ] All behaviors implemented
- [ ] Code reviewed