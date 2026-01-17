/**
 * Core type definitions for the writing agent UI
 */

export interface Project {
  id: string;
  name: string;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Transcription API types
 */

export interface TranscriptionOptions {
  language?: string;        // ISO 639-1 code (e.g., 'en', 'es')
  prompt?: string;          // Context hint for Whisper
  temperature?: number;     // 0-1, sampling temperature
}

export type TranscriptionErrorCode = 'RATE_LIMIT' | 'FILE_TOO_LARGE' | 'NETWORK' | 'INVALID_API_KEY' | 'API_ERROR' | 'UPLOAD_ERROR';

export class TranscriptionError extends Error {
  code: TranscriptionErrorCode;
  retryable: boolean;

  constructor(message: string, code: TranscriptionErrorCode, retryable: boolean = false) {
    super(message);
    this.name = 'TranscriptionError';
    this.code = code;
    this.retryable = retryable;
  }
}

/**
 * Attachment for messages (files, images, etc.)
 */
export interface Attachment {
  id: string;
  filename: string;
  size: number;
  type: string;
}

/**
 * Message in a conversation
 */
export interface Message {
  id: string;
  role: 'user' | 'assistant';
  content: string;
  timestamp: Date;
  attachments?: Attachment[];
  isVoiceTranscription?: boolean; // Indicates message originated from voice transcription
}

/**
 * Non-blocking operation types (can run alongside blocking operations)
 */
export type NonBlockingOperationType = 'copy';

/**
 * Button operation types (mutually exclusive per message)
 */
export type BlockingOperationType = 'regenerate' | 'sendToAPI' | 'edit';

/**
 * State for non-blocking copy operation
 */
export interface CopyState {
  isActive: boolean;
  timestamp: number;
}

/**
 * State for blocking operations (mutually exclusive)
 */
export interface BlockingOperationState {
  type: BlockingOperationType;
  isLoading: boolean;
  error?: string;
}

/**
 * Per-message button state tracking
 */
export interface MessageButtonState {
  copy?: CopyState;
  blockingOperation?: BlockingOperationState;
}

/**
 * Deep Research API types (REQ_000)
 */

export type DeepResearchModel = 'o3-deep-research-2025-06-26' | 'o4-mini-deep-research-2025-06-26';

export type DeepResearchDepth = 'quick' | 'thorough';

export type ReasoningSummary = 'auto' | 'detailed';

export type DeepResearchErrorCode =
  | 'RATE_LIMIT'
  | 'NETWORK'
  | 'INVALID_API_KEY'
  | 'API_ERROR'
  | 'VALIDATION_ERROR'
  | 'TIMEOUT'
  | 'JOB_NOT_FOUND'
  | 'JOB_FORBIDDEN';

export type DeepResearchJobStatus = 'pending' | 'processing' | 'completed' | 'failed';

/**
 * Developer or user role message input for Deep Research API
 * REQ_000.2: Support developer and user role message inputs
 */
export interface DeepResearchMessage {
  role: 'developer' | 'user';
  content: Array<{ type: 'input_text'; text: string }>;
}

/**
 * Reasoning configuration for Deep Research API
 * REQ_000.3: Configure reasoning summary options
 */
export interface DeepResearchReasoning {
  summary: ReasoningSummary;
}

/**
 * Request body for Deep Research API
 * REQ_000.1-000.4: Full request structure
 */
export interface DeepResearchRequest {
  model: DeepResearchModel;
  input: DeepResearchMessage[];
  reasoning?: DeepResearchReasoning;
  background?: boolean;
}

/**
 * Citation in Deep Research response
 */
export interface DeepResearchCitation {
  type: 'url_citation';
  url: string;
  title?: string;
  start_index: number;
  end_index: number;
}

/**
 * Reasoning step from Deep Research
 */
export interface DeepResearchReasoningStep {
  id: string;
  type: 'reasoning';
  summary: Array<{ type: 'summary_text'; text: string }>;
}

/**
 * Content block in Deep Research response
 */
export interface DeepResearchContentBlock {
  type: 'output_text';
  text: string;
  annotations?: DeepResearchCitation[];
}

/**
 * Output item from Deep Research response
 */
export interface DeepResearchOutputItem {
  id: string;
  type: 'message';
  role: 'assistant';
  content: DeepResearchContentBlock[];
}

/**
 * Progress information for background jobs
 * REQ_000.5: Progress tracking
 */
export interface DeepResearchProgress {
  step: string;
  percentage?: number;
}

/**
 * Job metadata from background mode response
 * REQ_000.4: Background mode response
 */
export interface DeepResearchJobMetadata {
  id: string;
  status: DeepResearchJobStatus;
  statusUrl: string;
  createdAt: string;
  model: DeepResearchModel;
  estimatedCompletion?: {
    min: number; // minutes
    max: number; // minutes
  };
}

/**
 * Full Deep Research API response
 */
export interface DeepResearchApiResponse {
  id: string;
  object: 'response';
  status: DeepResearchJobStatus;
  output?: DeepResearchOutputItem[];
  reasoning?: DeepResearchReasoningStep[];
  usage?: {
    input_tokens: number;
    output_tokens: number;
    reasoning_tokens?: number;
  };
  error?: {
    code: string;
    message: string;
  };
}

/**
 * Processed Deep Research result for UI consumption
 */
export interface DeepResearchResult {
  text: string;
  citations: DeepResearchCitation[];
  reasoningSteps: Array<{ id: string; text: string }>;
  usage?: {
    inputTokens: number;
    outputTokens: number;
    reasoningTokens?: number;
  };
}

/**
 * Status response for polling background jobs
 * REQ_000.5: Polling mechanism
 */
export interface DeepResearchStatusResponse {
  status: DeepResearchJobStatus;
  progress?: DeepResearchProgress;
  result?: DeepResearchResult;
  error?: {
    code: string;
    message: string;
  };
}

/**
 * Deep Research error class
 */
export class DeepResearchError extends Error {
  code: DeepResearchErrorCode;
  retryable: boolean;

  constructor(message: string, code: DeepResearchErrorCode, retryable: boolean = false) {
    super(message);
    this.name = 'DeepResearchError';
    this.code = code;
    this.retryable = retryable;
  }
}

/**
 * Options for initiating a Deep Research request
 */
export interface DeepResearchOptions {
  query: string;
  depth?: DeepResearchDepth;
  developerInstructions?: string;
  reasoningSummary?: ReasoningSummary;
  background?: boolean;
}
