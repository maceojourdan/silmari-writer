/**
 * Streaming Types for SSE Support (REQ_011)
 *
 * Server-Sent Events types for real-time progress updates
 */

// =============================================================================
// REQ_011.1: SSE Event Types for Deep Research
// =============================================================================

/**
 * SSE Event type discriminator
 */
export type SSEEventType =
  | 'reasoning'
  | 'web_search_call'
  | 'progress'
  | 'done'
  | 'error';

/**
 * Reasoning step type in research process
 * REQ_011.1.2: Step types for research phases
 */
export type ReasoningStepType = 'planning' | 'searching' | 'synthesizing';

/**
 * Base SSE event interface
 * REQ_011.1.12: Consistent schema across all event types
 */
export interface SSEEventBase {
  type: SSEEventType;
  timestamp: string;
  responseId: string;
}

/**
 * Reasoning event
 * REQ_011.1.2: Contains step summary, step index, and step type
 */
export interface SSEReasoningEvent extends SSEEventBase {
  type: 'reasoning';
  stepIndex: number;
  stepType: ReasoningStepType;
  summary: string;
}

/**
 * Web search call event
 * REQ_011.1.3: Emitted when research agent performs web searches
 */
export interface SSEWebSearchCallEvent extends SSEEventBase {
  type: 'web_search_call';
  query: string;
  searchId: string;
}

/**
 * Progress event
 * REQ_011.1.4: Percentage estimate based on typical research duration
 */
export interface SSEProgressEvent extends SSEEventBase {
  type: 'progress';
  percentage: number;
  elapsedMs: number;
  estimatedRemainingMs?: number;
  currentPhase?: ReasoningStepType;
}

/**
 * Done event
 * REQ_011.1.5: Emitted when research completes
 */
export interface SSEDoneEvent extends SSEEventBase {
  type: 'done';
  finalReportAvailable: boolean;
  totalElapsedMs: number;
  resultId?: string;
}

/**
 * Error event
 * REQ_011.1.6: Emitted when research fails
 */
export interface SSEErrorEvent extends SSEEventBase {
  type: 'error';
  code: string;
  message: string;
  retryable: boolean;
}

/**
 * Union type for all SSE events
 */
export type SSEEvent =
  | SSEReasoningEvent
  | SSEWebSearchCallEvent
  | SSEProgressEvent
  | SSEDoneEvent
  | SSEErrorEvent;

// =============================================================================
// REQ_011.2: Image Generation Streaming Types
// =============================================================================

/**
 * Image streaming event type
 */
export type ImageStreamEventType = 'partial_image' | 'final_image' | 'error';

/**
 * Base image stream event
 */
export interface ImageStreamEventBase {
  type: ImageStreamEventType;
  timestamp: string;
  requestId: string;
}

/**
 * Partial image event
 * REQ_011.2.4: Contains base64 data and preview index
 */
export interface ImageStreamPartialEvent extends ImageStreamEventBase {
  type: 'partial_image';
  previewIndex: number;
  totalPreviews: number;
  base64Data: string;
  width?: number;
  height?: number;
}

/**
 * Final image event
 * REQ_011.2.5: Distinguished from partial events
 */
export interface ImageStreamFinalEvent extends ImageStreamEventBase {
  type: 'final_image';
  base64Data: string;
  url: string;
  width: number;
  height: number;
  totalStreamingTimeMs: number;
}

/**
 * Image stream error event
 */
export interface ImageStreamErrorEvent extends ImageStreamEventBase {
  type: 'error';
  code: string;
  message: string;
  partialImagesGenerated: number;
}

/**
 * Union type for image streaming events
 */
export type ImageStreamEvent =
  | ImageStreamPartialEvent
  | ImageStreamFinalEvent
  | ImageStreamErrorEvent;

// =============================================================================
// REQ_011.3: Progress Indicator Types
// =============================================================================

/**
 * Progress phase for different tool types
 */
export interface ProgressPhase {
  id: string;
  label: string;
  status: 'pending' | 'active' | 'completed' | 'error';
  startedAt?: string;
  completedAt?: string;
}

/**
 * Deep Research progress phases
 * REQ_011.3.1: Phases for Deep Research
 */
export const DEEP_RESEARCH_PHASES: readonly ProgressPhase[] = [
  { id: 'analyzing', label: 'Analyzing query', status: 'pending' },
  { id: 'searching', label: 'Searching web', status: 'pending' },
  { id: 'reading', label: 'Reading sources', status: 'pending' },
  { id: 'synthesizing', label: 'Synthesizing report', status: 'pending' },
] as const;

/**
 * Image Generation progress phases
 * REQ_011.3.2: Phases for Image Generation
 */
export const IMAGE_GENERATION_PHASES: readonly ProgressPhase[] = [
  { id: 'processing', label: 'Processing prompt', status: 'pending' },
  { id: 'generating', label: 'Generating image', status: 'pending' },
  { id: 'finalizing', label: 'Finalizing', status: 'pending' },
] as const;

/**
 * Document Generation progress phases
 * REQ_011.3.3: Phases for Document Generation
 */
export const DOCUMENT_GENERATION_PHASES: readonly ProgressPhase[] = [
  { id: 'content', label: 'Generating content', status: 'pending' },
  { id: 'creating', label: 'Creating document', status: 'pending' },
  { id: 'uploading', label: 'Uploading file', status: 'pending' },
] as const;

/**
 * Progress indicator state
 * REQ_011.3: Real-time progress tracking
 */
export interface ProgressIndicatorState {
  /** Tool operation type */
  operationType: 'deep_research' | 'image_generation' | 'document_generation';
  /** List of phases for this operation */
  phases: ProgressPhase[];
  /** Current active phase index */
  currentPhaseIndex: number;
  /** Overall progress percentage (0-100) */
  progressPercentage: number;
  /** Start timestamp */
  startedAt: string;
  /** Elapsed time in milliseconds */
  elapsedMs: number;
  /** Estimated remaining time in milliseconds */
  estimatedRemainingMs?: number;
  /** Operation complete flag */
  isComplete: boolean;
  /** Error message if failed */
  error?: string;
}

// =============================================================================
// REQ_011.4: Intermediate Result Types
// =============================================================================

/**
 * Intermediate result type
 */
export type IntermediateResultType =
  | 'search_query'
  | 'reasoning_summary'
  | 'partial_report'
  | 'partial_image'
  | 'document_outline';

/**
 * Base intermediate result
 */
export interface IntermediateResultBase {
  id: string;
  type: IntermediateResultType;
  timestamp: string;
  expanded: boolean;
}

/**
 * Web search query result
 * REQ_011.4.1: Displays queries as they are executed
 */
export interface SearchQueryResult extends IntermediateResultBase {
  type: 'search_query';
  query: string;
  searchUrl?: string;
  resultCount?: number;
}

/**
 * Reasoning summary result
 * REQ_011.4.2: Displays reasoning as it completes
 */
export interface ReasoningSummaryResult extends IntermediateResultBase {
  type: 'reasoning_summary';
  summary: string;
  stepIndex: number;
  stepType: ReasoningStepType;
}

/**
 * Partial report section
 * REQ_011.4.3: Displays sections as synthesized
 */
export interface PartialReportResult extends IntermediateResultBase {
  type: 'partial_report';
  sectionTitle?: string;
  content: string;
  sectionIndex: number;
}

/**
 * Partial image preview
 * REQ_011.4.4: Displays preview images during generation
 */
export interface PartialImageResult extends IntermediateResultBase {
  type: 'partial_image';
  imageUrl: string;
  previewIndex: number;
  isPreview: true;
}

/**
 * Document outline
 * REQ_011.4.5: Displays outline before full document
 */
export interface DocumentOutlineResult extends IntermediateResultBase {
  type: 'document_outline';
  sections: Array<{ title: string; level: number }>;
}

/**
 * Union type for intermediate results
 */
export type IntermediateResult =
  | SearchQueryResult
  | ReasoningSummaryResult
  | PartialReportResult
  | PartialImageResult
  | DocumentOutlineResult;

// =============================================================================
// REQ_011.5: Cancellation Types
// =============================================================================

/**
 * Cancellation reason
 * REQ_011.5.11: Tracks reason for cancellation
 */
export type CancellationReason = 'user_initiated' | 'timeout' | 'error';

/**
 * Cancellation state
 */
export interface CancellationState {
  /** Operation ID being cancelled */
  operationId: string;
  /** Current cancellation state */
  status: 'idle' | 'cancelling' | 'cancelled' | 'failed';
  /** Reason for cancellation */
  reason?: CancellationReason;
  /** Time when cancellation was initiated */
  initiatedAt?: string;
  /** Time when cancellation completed */
  completedAt?: string;
  /** Partial results preserved before cancellation */
  preservedResults?: IntermediateResult[];
  /** Cost incurred before cancellation */
  incurredCost?: number;
}

/**
 * Cancellation request
 * REQ_011.5: Request to cancel an operation
 */
export interface CancellationRequest {
  operationId: string;
  operationType: 'deep_research' | 'image_generation' | 'document_generation';
  reason: CancellationReason;
}

/**
 * Cancellation response
 */
export interface CancellationResponse {
  success: boolean;
  operationId: string;
  preservedResults?: IntermediateResult[];
  incurredCost?: number;
  message: string;
}

// =============================================================================
// SSE Client Configuration
// =============================================================================

/**
 * SSE connection configuration
 * REQ_011.1.7-8: Connection settings
 */
export interface SSEConnectionConfig {
  /** Response ID to subscribe to */
  responseId: string;
  /** Reconnection delay in ms (default: 3000) */
  retryDelayMs?: number;
  /** Keep-alive interval in ms (default: 15000) */
  keepAliveIntervalMs?: number;
  /** Maximum reconnection attempts */
  maxRetries?: number;
  /** Event handlers */
  onEvent?: (event: SSEEvent) => void;
  onError?: (error: Error) => void;
  onClose?: () => void;
}

/**
 * SSE connection state
 */
export interface SSEConnectionState {
  status: 'connecting' | 'connected' | 'reconnecting' | 'closed' | 'error';
  lastEventAt?: string;
  retryCount: number;
  error?: string;
}

// =============================================================================
// Streaming Store Types
// =============================================================================

/**
 * Active streaming operation
 */
export interface StreamingOperation {
  id: string;
  type: 'deep_research' | 'image_generation' | 'document_generation';
  status: 'pending' | 'streaming' | 'completed' | 'failed' | 'cancelled';
  startedAt: string;
  completedAt?: string;
  progress: ProgressIndicatorState;
  intermediateResults: IntermediateResult[];
  cancellation?: CancellationState;
  abortController?: AbortController;
}

/**
 * Streaming store state
 */
export interface StreamingStoreState {
  /** Active operations by ID */
  operations: Map<string, StreamingOperation>;
  /** SSE connection states by response ID */
  connections: Map<string, SSEConnectionState>;
}

// =============================================================================
// Helper Functions
// =============================================================================

/**
 * Create initial progress state for an operation
 */
export function createProgressState(
  operationType: ProgressIndicatorState['operationType']
): ProgressIndicatorState {
  const phases = operationType === 'deep_research'
    ? [...DEEP_RESEARCH_PHASES]
    : operationType === 'image_generation'
    ? [...IMAGE_GENERATION_PHASES]
    : [...DOCUMENT_GENERATION_PHASES];

  return {
    operationType,
    phases: phases.map(p => ({ ...p })),
    currentPhaseIndex: 0,
    progressPercentage: 0,
    startedAt: new Date().toISOString(),
    elapsedMs: 0,
    isComplete: false,
  };
}

/**
 * Update progress state with new phase
 */
export function updateProgressPhase(
  state: ProgressIndicatorState,
  phaseId: string,
  status: ProgressPhase['status']
): ProgressIndicatorState {
  const phases = state.phases.map((phase, index) => {
    if (phase.id === phaseId) {
      return {
        ...phase,
        status,
        ...(status === 'active' && { startedAt: new Date().toISOString() }),
        ...(status === 'completed' && { completedAt: new Date().toISOString() }),
      };
    }
    return phase;
  });

  const currentPhaseIndex = phases.findIndex(p => p.status === 'active');
  const completedCount = phases.filter(p => p.status === 'completed').length;
  const progressPercentage = Math.round((completedCount / phases.length) * 100);

  return {
    ...state,
    phases,
    currentPhaseIndex: currentPhaseIndex >= 0 ? currentPhaseIndex : state.currentPhaseIndex,
    progressPercentage,
    elapsedMs: Date.now() - new Date(state.startedAt).getTime(),
  };
}

/**
 * Mark progress state as complete
 */
export function completeProgressState(
  state: ProgressIndicatorState
): ProgressIndicatorState {
  return {
    ...state,
    phases: state.phases.map(p => ({ ...p, status: 'completed' as const })),
    currentPhaseIndex: state.phases.length - 1,
    progressPercentage: 100,
    isComplete: true,
    elapsedMs: Date.now() - new Date(state.startedAt).getTime(),
  };
}

/**
 * Mark progress state as errored
 */
export function errorProgressState(
  state: ProgressIndicatorState,
  error: string
): ProgressIndicatorState {
  return {
    ...state,
    phases: state.phases.map((p, i) =>
      i === state.currentPhaseIndex
        ? { ...p, status: 'error' as const }
        : p
    ),
    error,
    elapsedMs: Date.now() - new Date(state.startedAt).getTime(),
  };
}

/**
 * Create a new intermediate result
 */
export function createIntermediateResult<T extends IntermediateResult>(
  type: T['type'],
  data: Omit<T, 'id' | 'timestamp' | 'expanded' | 'type'>
): T {
  return {
    id: `${type}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    type,
    timestamp: new Date().toISOString(),
    expanded: true,
    ...data,
  } as T;
}

// =============================================================================
// Type Guards
// =============================================================================

/**
 * Type guard for SSEReasoningEvent
 */
export function isSSEReasoningEvent(event: SSEEvent): event is SSEReasoningEvent {
  return event.type === 'reasoning';
}

/**
 * Type guard for SSEWebSearchCallEvent
 */
export function isSSEWebSearchCallEvent(event: SSEEvent): event is SSEWebSearchCallEvent {
  return event.type === 'web_search_call';
}

/**
 * Type guard for SSEProgressEvent
 */
export function isSSEProgressEvent(event: SSEEvent): event is SSEProgressEvent {
  return event.type === 'progress';
}

/**
 * Type guard for SSEDoneEvent
 */
export function isSSEDoneEvent(event: SSEEvent): event is SSEDoneEvent {
  return event.type === 'done';
}

/**
 * Type guard for SSEErrorEvent
 */
export function isSSEErrorEvent(event: SSEEvent): event is SSEErrorEvent {
  return event.type === 'error';
}

/**
 * Parse and validate an SSE event from JSON string
 * @throws Error if parsing fails or event is invalid
 */
export function parseSSEEvent(data: string): SSEEvent {
  const parsed = JSON.parse(data);

  if (!parsed || typeof parsed !== 'object' || typeof parsed.type !== 'string') {
    throw new Error('Invalid SSE event: missing type field');
  }

  const validTypes: SSEEventType[] = ['reasoning', 'web_search_call', 'progress', 'done', 'error'];
  if (!validTypes.includes(parsed.type)) {
    throw new Error(`Invalid SSE event type: ${parsed.type}`);
  }

  return parsed as SSEEvent;
}

/**
 * Type guard for ImageStreamPartialEvent
 */
export function isImageStreamPartialEvent(event: ImageStreamEvent): event is ImageStreamPartialEvent {
  return event.type === 'partial_image';
}

/**
 * Type guard for ImageStreamFinalEvent
 */
export function isImageStreamFinalEvent(event: ImageStreamEvent): event is ImageStreamFinalEvent {
  return event.type === 'final_image';
}

/**
 * Type guard for ImageStreamErrorEvent
 */
export function isImageStreamErrorEvent(event: ImageStreamEvent): event is ImageStreamErrorEvent {
  return event.type === 'error';
}

/**
 * Type guard for SearchQueryResult
 */
export function isSearchQueryResult(result: IntermediateResult): result is SearchQueryResult {
  return result.type === 'search_query';
}

/**
 * Type guard for ReasoningSummaryResult
 */
export function isReasoningSummaryResult(result: IntermediateResult): result is ReasoningSummaryResult {
  return result.type === 'reasoning_summary';
}

/**
 * Type guard for PartialReportResult
 */
export function isPartialReportResult(result: IntermediateResult): result is PartialReportResult {
  return result.type === 'partial_report';
}

/**
 * Type guard for PartialImageResult
 */
export function isPartialImageResult(result: IntermediateResult): result is PartialImageResult {
  return result.type === 'partial_image';
}

/**
 * Type guard for DocumentOutlineResult
 */
export function isDocumentOutlineResult(result: IntermediateResult): result is DocumentOutlineResult {
  return result.type === 'document_outline';
}
