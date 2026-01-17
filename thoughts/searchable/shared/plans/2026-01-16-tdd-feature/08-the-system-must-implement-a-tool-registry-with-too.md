# Phase 08: The system must implement a Tool Registry with too...

## Requirements

### REQ_007: The system must implement a Tool Registry with tool definiti

The system must implement a Tool Registry with tool definitions including name, description, trigger phrases, handler functions, and response types

#### REQ_007.1: Create central toolRegistry Map data structure with ToolDefi

Create central toolRegistry Map data structure with ToolDefinition entries for all supported tools (deep_research, image_generation, document_generation, chat_completion)

##### Testable Behaviors

1. ToolDefinition interface is defined with required fields: name (string), description (string), triggerPhrases (string[]), handler (function reference), responseType (enum)
2. ResponseType type union includes 'text', 'image', and 'file' values
3. toolRegistry is implemented as Map<string, ToolDefinition> for O(1) lookup performance
4. Registry contains entries for: 'deep_research', 'image_generation', 'document_generation', 'chat_completion'
5. Each tool entry includes unique identifier key matching its handler purpose
6. Registry is exported as a singleton module for consistent access across application
7. TypeScript strict mode compilation passes with no type errors
8. Unit tests verify all four tool entries exist and have valid ToolDefinition shape
9. Registry is immutable after initialization (use Object.freeze or readonly Map pattern)
10. getToolByName(name: string) function returns ToolDefinition | undefined
11. getAllTools() function returns array of all registered ToolDefinitions
12. hasToolByName(name: string) function returns boolean for tool existence check

#### REQ_007.2: Define comprehensive trigger phrase arrays for natural langu

Define comprehensive trigger phrase arrays for natural language intent classification enabling voice-to-tool routing

##### Testable Behaviors

1. deep_research tool has trigger phrases: ['research', 'investigate', 'find out about', 'analyze', 'look up', 'dig into', 'explore']
2. image_generation tool has trigger phrases: ['create image', 'draw', 'generate picture', 'visualize', 'make art', 'design', 'illustrate', 'render']
3. document_generation tool has trigger phrases: ['create document', 'generate report', 'make spreadsheet', 'create PDF', 'write a doc', 'make a file', 'export to']
4. chat_completion tool has trigger phrases: ['write', 'help me', 'tell me', 'explain', 'suggest', 'answer', 'chat']
5. Trigger phrases are case-insensitive during matching
6. Trigger phrases support partial word matching (e.g., 'researching' matches 'research')
7. Phrases are ordered by specificity (longer/more specific phrases first to avoid false positives)
8. Unit tests verify each tool's trigger phrases correctly identify sample user inputs
9. Edge cases handled: empty input, input with only stopwords, punctuation-heavy input
10. isPhraseMatch helper returns confidence score (0-1) based on match quality

#### REQ_007.3: Specify responseType enum values (text/image/file) for UI re

Specify responseType enum values (text/image/file) for UI rendering determination enabling type-safe response handling

##### Testable Behaviors

1. ResponseType is defined as union type: 'text' | 'image' | 'file'
2. deep_research tool has responseType: 'text'
3. image_generation tool has responseType: 'image'
4. document_generation tool has responseType: 'file'
5. chat_completion tool has responseType: 'text'
6. Type guard functions correctly narrow ToolResult to specific response types
7. UI components use responseType to determine appropriate rendering strategy
8. ResponseType is used at compile-time for exhaustive switch statement checking
9. Unit tests verify each registered tool has valid responseType value
10. Adding a new ResponseType value requires updating all switch statements (enforced by TypeScript)

#### REQ_007.4: Register handler function references (handleDeepResearch, ha

Register handler function references (handleDeepResearch, handleImageGeneration, handleDocumentGeneration, handleChatCompletion) with proper async function signatures and error handling

##### Testable Behaviors

1. handleDeepResearch handler is registered for 'deep_research' tool
2. handleImageGeneration handler is registered for 'image_generation' tool
3. handleDocumentGeneration handler is registered for 'document_generation' tool
4. handleChatCompletion handler is registered for 'chat_completion' tool (existing /api/generate logic refactored)
5. All handlers conform to ToolHandler type signature: (params: ToolParams) => Promise<ToolResult>
6. Handlers catch and wrap errors in ToolError format with code, message, retryable fields
7. Handlers support cancellation via AbortController signal in params
8. Unit tests verify each handler is correctly registered and callable
9. Integration tests verify handlers make correct API calls to external services
10. Handlers emit events for progress tracking (onStart, onProgress, onComplete, onError)

#### REQ_007.5: Implement invokeToolHandler utility for executing tools thro

Implement invokeToolHandler utility for executing tools through registry lookup with unified error handling and response normalization

##### Testable Behaviors

1. invokeToolHandler accepts toolName string and params object
2. Function looks up tool in registry and throws ToolError if not found
3. Function invokes registered handler with provided params
4. Returns Promise<ToolResult> with normalized response format
5. Errors from handlers are caught and re-thrown as ToolError with appropriate code
6. Execution timing is measured and logged for performance monitoring
7. Function supports optional execution context with signal, callbacks
8. Unit tests verify successful invocation for all registered tools
9. Unit tests verify error handling for unknown tool names
10. Unit tests verify timeout handling for long-running tools
11. Function validates params against tool's expected parameter schema before invocation


## Success Criteria

- [x] All tests pass (58 tests passing)
- [x] All behaviors implemented
- [ ] Code reviewed

## Implementation Notes

**Files Created:**
- `frontend/src/lib/tool-registry.ts` - Core tool registry implementation
- `frontend/__tests__/lib/tool-registry.test.ts` - Comprehensive test suite (58 tests)

**Key Features Implemented:**
1. `ToolDefinition` interface with all required fields
2. `ResponseType` union type ('text' | 'image' | 'file')
3. `toolRegistry` as immutable Map with O(1) lookup
4. All 4 tools registered: deep_research, image_generation, document_generation, chat_completion
5. Trigger phrases with case-insensitive and partial word matching
6. `isPhraseMatch()` helper with confidence scoring (0-1)
7. Handler functions with proper error handling and cancellation support
8. `invokeToolHandler()` utility with timeout support and logging
9. Type guards: `isTextResponse()`, `isImageResponse()`, `isFileResponse()`
10. `ToolError` class with code, message, retryable fields