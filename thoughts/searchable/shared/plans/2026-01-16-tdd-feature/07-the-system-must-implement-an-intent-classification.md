# Phase 07: The system must implement an Intent Classification...

## Requirements

### REQ_006: The system must implement an Intent Classification layer to 

The system must implement an Intent Classification layer to route plain language requests to appropriate tools

#### REQ_006.1: Create classifyIntent function using gpt-4o-mini with json_o

Create classifyIntent function using gpt-4o-mini with json_object response format for tool routing

##### Testable Behaviors

1. Function accepts a userMessage string parameter and optional conversationHistory array for context-aware classification
2. Function makes a POST request to OpenAI API using gpt-4o-mini model with temperature 0 for deterministic output
3. Request includes response_format: { type: 'json_object' } configuration to enforce JSON response
4. Function returns a Promise<ClassifiedIntent> with parsed and validated JSON response
5. Function handles empty or whitespace-only messages by returning error with code 'INVALID_INPUT'
6. Function validates the returned JSON matches ClassifiedIntent structure before returning
7. Function logs classification attempts including userMessage hash, detected tool, confidence, and latency for analytics
8. Function completes classification within 2 seconds for typical messages (95th percentile)
9. Function reuses existing retry logic pattern from generate/route.ts (MAX_RETRIES=3, exponential backoff)
10. Function handles rate limit errors (429) with appropriate backoff and retry
11. Function handles network timeouts with configurable timeout (default 10 seconds)
12. Unit tests verify JSON parsing of all four tool type responses with varying confidence levels
13. Unit tests verify error handling for malformed JSON, API errors, and timeout scenarios
14. Function includes conversation history in prompt when provided for context-aware multi-turn classification

#### REQ_006.2: Define four core intent types: deep_research, image_generati

Define four core intent types: deep_research, image_generation, document_generation, chat_completion

##### Testable Behaviors

1. ToolIntent type is defined as union literal: 'deep_research' | 'image_generation' | 'document_generation' | 'chat_completion'
2. deep_research intent includes DeepResearchParams interface with query (required), depth ('quick' | 'thorough', optional), topics (string[], optional)
3. image_generation intent includes ImageGenerationParams interface with prompt (required), size ('1024x1024' | '1536x1024' | '1024x1536' | 'auto', optional), quality ('low' | 'medium' | 'high', optional), style (string, optional)
4. document_generation intent includes DocumentGenerationParams interface with type ('pdf' | 'docx' | 'xlsx', required), contentDescription (required), template (string, optional), title (string, optional)
5. chat_completion intent includes ChatCompletionParams interface with message (required) - serves as default fallback
6. Each intent type params interface is exported individually for type-safe parameter handling in tool handlers
7. ExtractedParams discriminated union type allows narrowing based on tool type using 'kind' discriminant field
8. Type guard functions exist: isDeepResearchParams(), isImageGenerationParams(), isDocumentGenerationParams(), isChatCompletionParams()
9. isValidToolIntent(value: string): value is ToolIntent type guard validates unknown strings
10. TOOL_INTENT_DISPLAY_NAMES constant object provides human-readable labels: { deep_research: 'Deep Research', image_generation: 'Image Generation', document_generation: 'Document Generation', chat_completion: 'Chat' }
11. TOOL_INTENT_ICONS constant object maps intent to icon names for UI display
12. Unit tests verify each intent type can be correctly serialized/deserialized through JSON.parse/stringify roundtrip
13. Documentation JSDoc comments explain when each intent type should be used with example phrases

#### REQ_006.3: Implement ClassifiedIntent response structure with tool name

Implement ClassifiedIntent response structure with tool name, confidence score (0.0-1.0), and extracted parameters

##### Testable Behaviors

1. ClassifiedIntent interface contains 'tool' field of type ToolIntent (required)
2. ClassifiedIntent interface contains 'confidence' field as number between 0.0 and 1.0 (required)
3. ClassifiedIntent interface contains 'extractedParams' field of type ExtractedParams (required)
4. ClassifiedIntent interface contains optional 'alternativeIntents' field as AlternativeIntent[] for ambiguous cases
5. ClassifiedIntent interface contains optional 'rawMessage' field preserving original user input
6. ClassifiedIntent interface contains optional 'classifiedAt' timestamp field for debugging
7. Confidence score semantics: >0.8 = high certainty (proceed), 0.5-0.8 = medium (proceed with note), <0.5 = low (request clarification)
8. CONFIDENCE_THRESHOLDS constant defines: { HIGH: 0.8, MEDIUM: 0.5, LOW: 0.3, MINIMUM: 0.1 }
9. extractedParams structure varies by tool type but always includes 'kind' discriminant field
10. AlternativeIntent interface: { tool: ToolIntent; confidence: number } for secondary classifications
11. alternativeIntents included when second-best confidence > 0.4 AND within 0.3 of primary confidence
12. validateClassifiedIntent(response: unknown): ClassifiedIntent throws ClassificationError on invalid structure
13. clampConfidence(n: number): number clamps to 0.0-1.0 range with Math.max(0, Math.min(1, n))
14. shouldRequestClarification(intent: ClassifiedIntent): boolean returns true if confidence < CONFIDENCE_THRESHOLDS.MEDIUM
15. getConfidenceLevel(confidence: number): 'high' | 'medium' | 'low' returns semantic confidence level
16. Unit tests verify confidence normalization handles edge cases: negative numbers, >1 values, NaN, undefined
17. Unit tests verify param extraction for sample messages of each tool type

#### REQ_006.4: Create and maintain system prompt with classification criter

Create and maintain system prompt with classification criteria and few-shot examples for each tool type

##### Testable Behaviors

1. INTENT_CLASSIFIER_SYSTEM_PROMPT constant contains complete system prompt for gpt-4o-mini classifier
2. System prompt clearly defines all four tool types with detailed descriptions and use cases
3. deep_research criteria keywords: 'research', 'investigate', 'find out', 'analyze', 'what is the latest', 'study', 'explore', 'look into', 'deep dive'
4. image_generation criteria keywords: 'create image', 'draw', 'generate picture', 'visualize', 'design', 'illustrate', 'make artwork', 'paint', 'render'
5. document_generation criteria keywords: 'create PDF', 'generate report', 'make spreadsheet', 'Word document', 'Excel file', 'export as', 'create document', 'build a report'
6. chat_completion criteria: general conversation, writing assistance, explanations, creative writing, questions - explicit DEFAULT when no other tool matches
7. System prompt includes 2-3 few-shot examples per tool type demonstrating classification with parameters
8. System prompt specifies exact JSON output format with field descriptions and types
9. System prompt includes parameter extraction instructions for each tool type with examples
10. System prompt includes confidence scoring guidance: 'assign 0.9+ for clear matches, 0.6-0.8 for likely matches, 0.3-0.5 for uncertain'
11. System prompt instructs model to include alternativeIntents when confidence < 0.8
12. System prompt includes negative examples showing what NOT to classify as each tool type
13. Prompt stored as template literal constant with version comment header (e.g., // v1.0.0 - 2026-01-16)
14. INTENT_CLASSIFIER_PROMPT_VERSION constant tracks prompt version for A/B testing and rollback
15. Unit tests verify classifier produces expected tool for each trigger phrase category
16. Integration tests verify classifier correctly handles ambiguous multi-intent requests

#### REQ_006.5: Handle low confidence classifications (<0.5) with user clari

Handle low confidence classifications (<0.5) with user clarification prompts

##### Testable Behaviors

1. When confidence < 0.5, system pauses automatic tool execution and prompts user for clarification
2. Clarification prompt displays detected intent with confidence level and asks user to confirm or select alternative
3. User presented with options: (1) Confirm detected intent, (2) Select from alternatives, (3) Type clarification, (4) Cancel/use chat
4. If user confirms detected intent, proceed with tool execution regardless of low confidence (user override)
5. If user selects alternative intent, re-classify with selected tool as hint and extract appropriate parameters
6. If user types clarification, append to original message and re-run classification with enhanced context
7. If user cancels, fall back to chat_completion with original message
8. Clarification dialog shows friendly language: 'I want to make sure I understand...' not technical jargon
9. Clarification state persists if user navigates away and returns within session
10. Analytics track: clarification frequency, user choices, whether clarification improved accuracy
11. CLARIFICATION_TIMEOUT_MS constant (300000 = 5 minutes) after which pending clarification is auto-cancelled
12. Unit tests verify clarification flow triggers at exactly confidence = 0.49 but not at 0.50
13. Unit tests verify each user choice path (confirm, alternative, clarify, cancel) produces correct outcome
14. Accessibility: clarification dialog is keyboard navigable and screen reader friendly


## Success Criteria

- [ ] All tests pass
- [ ] All behaviors implemented
- [ ] Code reviewed