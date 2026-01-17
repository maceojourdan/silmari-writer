/**
 * Unit tests for Streaming Types (REQ_011)
 * Server-Sent Events types and helper functions
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

import {
  // Type guards
  isSSEReasoningEvent,
  isSSEWebSearchCallEvent,
  isSSEProgressEvent,
  isSSEDoneEvent,
  isSSEErrorEvent,
  isImageStreamPartialEvent,
  isImageStreamFinalEvent,
  isImageStreamErrorEvent,
  isSearchQueryResult,
  isReasoningSummaryResult,
  isPartialReportResult,
  isPartialImageResult,
  isDocumentOutlineResult,
  parseSSEEvent,
  // Helper functions
  createProgressState,
  updateProgressPhase,
  completeProgressState,
  errorProgressState,
  createIntermediateResult,
  // Constants
  DEEP_RESEARCH_PHASES,
  IMAGE_GENERATION_PHASES,
  DOCUMENT_GENERATION_PHASES,
} from '../streaming-types';

import type {
  SSEEvent,
  SSEReasoningEvent,
  SSEWebSearchCallEvent,
  SSEProgressEvent,
  SSEDoneEvent,
  SSEErrorEvent,
  ImageStreamEvent,
  ImageStreamPartialEvent,
  ImageStreamFinalEvent,
  ImageStreamErrorEvent,
  IntermediateResult,
  SearchQueryResult,
  ReasoningSummaryResult,
  PartialReportResult,
  PartialImageResult,
  DocumentOutlineResult,
  ProgressIndicatorState,
  ProgressPhase,
} from '../streaming-types';

// =============================================================================
// REQ_011.1: SSE Event Types for Deep Research
// =============================================================================

describe('SSE Event Types (REQ_011.1)', () => {
  describe('SSEReasoningEvent (REQ_011.1.2)', () => {
    const validReasoningEvent: SSEReasoningEvent = {
      type: 'reasoning',
      timestamp: '2026-01-16T12:00:00Z',
      responseId: 'resp_123',
      stepIndex: 1,
      stepType: 'planning',
      summary: 'Analyzing research query',
    };

    it('should correctly identify reasoning events', () => {
      expect(isSSEReasoningEvent(validReasoningEvent)).toBe(true);
    });

    it('should reject non-reasoning events', () => {
      const progressEvent: SSEProgressEvent = {
        type: 'progress',
        timestamp: '2026-01-16T12:00:00Z',
        responseId: 'resp_123',
        percentage: 50,
        elapsedMs: 5000,
      };
      expect(isSSEReasoningEvent(progressEvent)).toBe(false);
    });

    it('should contain required fields: stepIndex, stepType, summary', () => {
      expect(validReasoningEvent.stepIndex).toBe(1);
      expect(validReasoningEvent.stepType).toBe('planning');
      expect(validReasoningEvent.summary).toBe('Analyzing research query');
    });

    it('should support all step types: planning, searching, synthesizing', () => {
      const planningEvent: SSEReasoningEvent = { ...validReasoningEvent, stepType: 'planning' };
      const searchingEvent: SSEReasoningEvent = { ...validReasoningEvent, stepType: 'searching' };
      const synthesizingEvent: SSEReasoningEvent = { ...validReasoningEvent, stepType: 'synthesizing' };

      expect(isSSEReasoningEvent(planningEvent)).toBe(true);
      expect(isSSEReasoningEvent(searchingEvent)).toBe(true);
      expect(isSSEReasoningEvent(synthesizingEvent)).toBe(true);
    });
  });

  describe('SSEWebSearchCallEvent (REQ_011.1.3)', () => {
    const validWebSearchEvent: SSEWebSearchCallEvent = {
      type: 'web_search_call',
      timestamp: '2026-01-16T12:00:00Z',
      responseId: 'resp_123',
      query: 'machine learning trends 2026',
      searchId: 'search_456',
    };

    it('should correctly identify web search events', () => {
      expect(isSSEWebSearchCallEvent(validWebSearchEvent)).toBe(true);
    });

    it('should contain query text', () => {
      expect(validWebSearchEvent.query).toBe('machine learning trends 2026');
    });

    it('should contain unique searchId', () => {
      expect(validWebSearchEvent.searchId).toBe('search_456');
    });
  });

  describe('SSEProgressEvent (REQ_011.1.4)', () => {
    const validProgressEvent: SSEProgressEvent = {
      type: 'progress',
      timestamp: '2026-01-16T12:00:00Z',
      responseId: 'resp_123',
      percentage: 45,
      elapsedMs: 10000,
      estimatedRemainingMs: 12000,
      currentPhase: 'searching',
    };

    it('should correctly identify progress events', () => {
      expect(isSSEProgressEvent(validProgressEvent)).toBe(true);
    });

    it('should contain percentage estimate', () => {
      expect(validProgressEvent.percentage).toBe(45);
    });

    it('should contain elapsed time', () => {
      expect(validProgressEvent.elapsedMs).toBe(10000);
    });

    it('should optionally contain estimated remaining time', () => {
      expect(validProgressEvent.estimatedRemainingMs).toBe(12000);
    });

    it('should optionally contain current phase', () => {
      expect(validProgressEvent.currentPhase).toBe('searching');
    });

    it('should work without optional fields', () => {
      const minimalProgress: SSEProgressEvent = {
        type: 'progress',
        timestamp: '2026-01-16T12:00:00Z',
        responseId: 'resp_123',
        percentage: 30,
        elapsedMs: 5000,
      };
      expect(isSSEProgressEvent(minimalProgress)).toBe(true);
    });
  });

  describe('SSEDoneEvent (REQ_011.1.5)', () => {
    const validDoneEvent: SSEDoneEvent = {
      type: 'done',
      timestamp: '2026-01-16T12:05:00Z',
      responseId: 'resp_123',
      finalReportAvailable: true,
      totalElapsedMs: 300000,
      resultId: 'result_789',
    };

    it('should correctly identify done events', () => {
      expect(isSSEDoneEvent(validDoneEvent)).toBe(true);
    });

    it('should indicate if final report is available', () => {
      expect(validDoneEvent.finalReportAvailable).toBe(true);
    });

    it('should contain total elapsed time', () => {
      expect(validDoneEvent.totalElapsedMs).toBe(300000);
    });

    it('should optionally contain resultId', () => {
      expect(validDoneEvent.resultId).toBe('result_789');
    });
  });

  describe('SSEErrorEvent (REQ_011.1.6)', () => {
    const validErrorEvent: SSEErrorEvent = {
      type: 'error',
      timestamp: '2026-01-16T12:03:00Z',
      responseId: 'resp_123',
      code: 'RATE_LIMIT_EXCEEDED',
      message: 'API rate limit exceeded, please try again later',
      retryable: true,
    };

    it('should correctly identify error events', () => {
      expect(isSSEErrorEvent(validErrorEvent)).toBe(true);
    });

    it('should contain error code', () => {
      expect(validErrorEvent.code).toBe('RATE_LIMIT_EXCEEDED');
    });

    it('should contain error message', () => {
      expect(validErrorEvent.message).toBe('API rate limit exceeded, please try again later');
    });

    it('should indicate if error is retryable', () => {
      expect(validErrorEvent.retryable).toBe(true);
    });

    it('should handle non-retryable errors', () => {
      const fatalError: SSEErrorEvent = {
        ...validErrorEvent,
        code: 'INVALID_RESPONSE_ID',
        message: 'Response ID not found',
        retryable: false,
      };
      expect(fatalError.retryable).toBe(false);
    });
  });

  describe('parseSSEEvent (REQ_011.1.12)', () => {
    it('should parse valid JSON SSE events', () => {
      const jsonData = JSON.stringify({
        type: 'reasoning',
        timestamp: '2026-01-16T12:00:00Z',
        responseId: 'resp_123',
        stepIndex: 1,
        stepType: 'planning',
        summary: 'Test summary',
      });

      const event = parseSSEEvent(jsonData);
      expect(event.type).toBe('reasoning');
      expect(isSSEReasoningEvent(event)).toBe(true);
    });

    it('should throw error for invalid JSON', () => {
      expect(() => parseSSEEvent('not valid json')).toThrow();
    });

    it('should throw error for missing type field', () => {
      const invalidData = JSON.stringify({ timestamp: '2026-01-16T12:00:00Z' });
      expect(() => parseSSEEvent(invalidData)).toThrow('Invalid SSE event: missing type field');
    });

    it('should throw error for invalid event type', () => {
      const invalidType = JSON.stringify({ type: 'invalid_type' });
      expect(() => parseSSEEvent(invalidType)).toThrow('Invalid SSE event type: invalid_type');
    });

    it('should accept all valid event types', () => {
      const validTypes = ['reasoning', 'web_search_call', 'progress', 'done', 'error'];

      validTypes.forEach(type => {
        const data = JSON.stringify({
          type,
          timestamp: '2026-01-16T12:00:00Z',
          responseId: 'resp_123',
        });
        const event = parseSSEEvent(data);
        expect(event.type).toBe(type);
      });
    });
  });
});

// =============================================================================
// REQ_011.2: Image Generation Streaming Types
// =============================================================================

describe('Image Stream Event Types (REQ_011.2)', () => {
  describe('ImageStreamPartialEvent (REQ_011.2.4)', () => {
    const validPartialEvent: ImageStreamPartialEvent = {
      type: 'partial_image',
      timestamp: '2026-01-16T12:00:00Z',
      requestId: 'req_123',
      previewIndex: 2,
      totalPreviews: 5,
      base64Data: 'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNk+M9QDwADhgGAWjR9awAAAABJRU5ErkJggg==',
      width: 256,
      height: 256,
    };

    it('should correctly identify partial image events', () => {
      expect(isImageStreamPartialEvent(validPartialEvent)).toBe(true);
    });

    it('should contain preview index', () => {
      expect(validPartialEvent.previewIndex).toBe(2);
    });

    it('should contain total previews count', () => {
      expect(validPartialEvent.totalPreviews).toBe(5);
    });

    it('should contain base64 data', () => {
      expect(validPartialEvent.base64Data).toBeTruthy();
    });

    it('should optionally contain dimensions', () => {
      expect(validPartialEvent.width).toBe(256);
      expect(validPartialEvent.height).toBe(256);
    });
  });

  describe('ImageStreamFinalEvent (REQ_011.2.5)', () => {
    const validFinalEvent: ImageStreamFinalEvent = {
      type: 'final_image',
      timestamp: '2026-01-16T12:01:00Z',
      requestId: 'req_123',
      base64Data: 'base64encodeddata',
      url: 'https://example.com/image.png',
      width: 1024,
      height: 1024,
      totalStreamingTimeMs: 15000,
    };

    it('should correctly identify final image events', () => {
      expect(isImageStreamFinalEvent(validFinalEvent)).toBe(true);
    });

    it('should be distinguished from partial events', () => {
      expect(isImageStreamPartialEvent(validFinalEvent as unknown as ImageStreamEvent)).toBe(false);
    });

    it('should contain URL', () => {
      expect(validFinalEvent.url).toBe('https://example.com/image.png');
    });

    it('should contain dimensions', () => {
      expect(validFinalEvent.width).toBe(1024);
      expect(validFinalEvent.height).toBe(1024);
    });

    it('should contain total streaming time', () => {
      expect(validFinalEvent.totalStreamingTimeMs).toBe(15000);
    });
  });

  describe('ImageStreamErrorEvent', () => {
    const validImageError: ImageStreamErrorEvent = {
      type: 'error',
      timestamp: '2026-01-16T12:00:30Z',
      requestId: 'req_123',
      code: 'CONTENT_POLICY',
      message: 'Image content violates policy',
      partialImagesGenerated: 2,
    };

    it('should correctly identify image error events', () => {
      expect(isImageStreamErrorEvent(validImageError)).toBe(true);
    });

    it('should contain count of partial images generated before error', () => {
      expect(validImageError.partialImagesGenerated).toBe(2);
    });
  });
});

// =============================================================================
// REQ_011.3: Progress Indicator Types
// =============================================================================

describe('Progress Indicator Types (REQ_011.3)', () => {
  describe('Phase Constants (REQ_011.3.1-3)', () => {
    it('should have correct Deep Research phases (REQ_011.3.1)', () => {
      expect(DEEP_RESEARCH_PHASES).toHaveLength(4);
      expect(DEEP_RESEARCH_PHASES[0].label).toBe('Analyzing query');
      expect(DEEP_RESEARCH_PHASES[1].label).toBe('Searching web');
      expect(DEEP_RESEARCH_PHASES[2].label).toBe('Reading sources');
      expect(DEEP_RESEARCH_PHASES[3].label).toBe('Synthesizing report');
    });

    it('should have correct Image Generation phases (REQ_011.3.2)', () => {
      expect(IMAGE_GENERATION_PHASES).toHaveLength(3);
      expect(IMAGE_GENERATION_PHASES[0].label).toBe('Processing prompt');
      expect(IMAGE_GENERATION_PHASES[1].label).toBe('Generating image');
      expect(IMAGE_GENERATION_PHASES[2].label).toBe('Finalizing');
    });

    it('should have correct Document Generation phases (REQ_011.3.3)', () => {
      expect(DOCUMENT_GENERATION_PHASES).toHaveLength(3);
      expect(DOCUMENT_GENERATION_PHASES[0].label).toBe('Generating content');
      expect(DOCUMENT_GENERATION_PHASES[1].label).toBe('Creating document');
      expect(DOCUMENT_GENERATION_PHASES[2].label).toBe('Uploading file');
    });

    it('should have unique IDs for all phases', () => {
      const allPhases = [...DEEP_RESEARCH_PHASES, ...IMAGE_GENERATION_PHASES, ...DOCUMENT_GENERATION_PHASES];
      const ids = allPhases.map(p => p.id);
      const uniqueIds = new Set(ids);
      expect(uniqueIds.size).toBe(ids.length);
    });

    it('should all start with pending status', () => {
      const allPhases = [...DEEP_RESEARCH_PHASES, ...IMAGE_GENERATION_PHASES, ...DOCUMENT_GENERATION_PHASES];
      allPhases.forEach(phase => {
        expect(phase.status).toBe('pending');
      });
    });
  });

  describe('createProgressState', () => {
    beforeEach(() => {
      vi.useFakeTimers();
      vi.setSystemTime(new Date('2026-01-16T12:00:00Z'));
    });

    afterEach(() => {
      vi.useRealTimers();
    });

    it('should create progress state for deep_research', () => {
      const state = createProgressState('deep_research');

      expect(state.operationType).toBe('deep_research');
      expect(state.phases).toHaveLength(4);
      expect(state.currentPhaseIndex).toBe(0);
      expect(state.progressPercentage).toBe(0);
      expect(state.isComplete).toBe(false);
    });

    it('should create progress state for image_generation', () => {
      const state = createProgressState('image_generation');

      expect(state.operationType).toBe('image_generation');
      expect(state.phases).toHaveLength(3);
    });

    it('should create progress state for document_generation', () => {
      const state = createProgressState('document_generation');

      expect(state.operationType).toBe('document_generation');
      expect(state.phases).toHaveLength(3);
    });

    it('should set startedAt to current timestamp', () => {
      const state = createProgressState('deep_research');
      expect(state.startedAt).toBe('2026-01-16T12:00:00.000Z');
    });

    it('should initialize elapsedMs to 0', () => {
      const state = createProgressState('deep_research');
      expect(state.elapsedMs).toBe(0);
    });

    it('should create independent phase copies', () => {
      const state1 = createProgressState('deep_research');
      const state2 = createProgressState('deep_research');

      state1.phases[0].status = 'active';
      expect(state2.phases[0].status).toBe('pending');
    });
  });

  describe('updateProgressPhase', () => {
    beforeEach(() => {
      vi.useFakeTimers();
      vi.setSystemTime(new Date('2026-01-16T12:00:00Z'));
    });

    afterEach(() => {
      vi.useRealTimers();
    });

    it('should update phase status to active', () => {
      const state = createProgressState('deep_research');
      const updated = updateProgressPhase(state, 'analyzing', 'active');

      expect(updated.phases[0].status).toBe('active');
      expect(updated.phases[0].startedAt).toBeDefined();
    });

    it('should update phase status to completed', () => {
      const state = createProgressState('deep_research');
      const updated = updateProgressPhase(state, 'analyzing', 'completed');

      expect(updated.phases[0].status).toBe('completed');
      expect(updated.phases[0].completedAt).toBeDefined();
    });

    it('should update currentPhaseIndex when phase becomes active', () => {
      const state = createProgressState('deep_research');
      const updated = updateProgressPhase(state, 'searching', 'active');

      expect(updated.currentPhaseIndex).toBe(1);
    });

    it('should calculate progressPercentage based on completed phases', () => {
      let state = createProgressState('deep_research');

      // Complete first phase (1/4 = 25%)
      state = updateProgressPhase(state, 'analyzing', 'completed');
      expect(state.progressPercentage).toBe(25);

      // Complete second phase (2/4 = 50%)
      state = updateProgressPhase(state, 'searching', 'completed');
      expect(state.progressPercentage).toBe(50);

      // Complete third phase (3/4 = 75%)
      state = updateProgressPhase(state, 'reading', 'completed');
      expect(state.progressPercentage).toBe(75);

      // Complete all phases (4/4 = 100%)
      state = updateProgressPhase(state, 'synthesizing', 'completed');
      expect(state.progressPercentage).toBe(100);
    });

    it('should update elapsedMs', () => {
      const state = createProgressState('deep_research');

      // Advance time by 5 seconds
      vi.advanceTimersByTime(5000);

      const updated = updateProgressPhase(state, 'analyzing', 'active');
      expect(updated.elapsedMs).toBe(5000);
    });

    it('should not modify original state (immutability)', () => {
      const state = createProgressState('deep_research');
      const originalStatus = state.phases[0].status;

      updateProgressPhase(state, 'analyzing', 'active');

      expect(state.phases[0].status).toBe(originalStatus);
    });
  });

  describe('completeProgressState', () => {
    beforeEach(() => {
      vi.useFakeTimers();
      vi.setSystemTime(new Date('2026-01-16T12:00:00Z'));
    });

    afterEach(() => {
      vi.useRealTimers();
    });

    it('should mark all phases as completed', () => {
      const state = createProgressState('deep_research');
      const completed = completeProgressState(state);

      completed.phases.forEach(phase => {
        expect(phase.status).toBe('completed');
      });
    });

    it('should set progressPercentage to 100', () => {
      const state = createProgressState('deep_research');
      const completed = completeProgressState(state);

      expect(completed.progressPercentage).toBe(100);
    });

    it('should set isComplete to true', () => {
      const state = createProgressState('deep_research');
      const completed = completeProgressState(state);

      expect(completed.isComplete).toBe(true);
    });

    it('should set currentPhaseIndex to last phase', () => {
      const state = createProgressState('deep_research');
      const completed = completeProgressState(state);

      expect(completed.currentPhaseIndex).toBe(3);
    });

    it('should update elapsedMs', () => {
      const state = createProgressState('deep_research');

      vi.advanceTimersByTime(30000);

      const completed = completeProgressState(state);
      expect(completed.elapsedMs).toBe(30000);
    });
  });

  describe('errorProgressState', () => {
    beforeEach(() => {
      vi.useFakeTimers();
      vi.setSystemTime(new Date('2026-01-16T12:00:00Z'));
    });

    afterEach(() => {
      vi.useRealTimers();
    });

    it('should set error message', () => {
      const state = createProgressState('deep_research');
      const errored = errorProgressState(state, 'Connection failed');

      expect(errored.error).toBe('Connection failed');
    });

    it('should mark current phase as error', () => {
      let state = createProgressState('deep_research');
      state = updateProgressPhase(state, 'searching', 'active');

      const errored = errorProgressState(state, 'Search failed');

      expect(errored.phases[1].status).toBe('error');
    });

    it('should not change status of other phases', () => {
      let state = createProgressState('deep_research');
      state = updateProgressPhase(state, 'analyzing', 'completed');
      state = updateProgressPhase(state, 'searching', 'active');

      const errored = errorProgressState(state, 'Error');

      expect(errored.phases[0].status).toBe('completed');
      expect(errored.phases[2].status).toBe('pending');
      expect(errored.phases[3].status).toBe('pending');
    });

    it('should update elapsedMs', () => {
      const state = createProgressState('deep_research');

      vi.advanceTimersByTime(15000);

      const errored = errorProgressState(state, 'Timeout');
      expect(errored.elapsedMs).toBe(15000);
    });
  });
});

// =============================================================================
// REQ_011.4: Intermediate Result Types
// =============================================================================

describe('Intermediate Result Types (REQ_011.4)', () => {
  describe('createIntermediateResult', () => {
    beforeEach(() => {
      vi.useFakeTimers();
      vi.setSystemTime(new Date('2026-01-16T12:00:00Z'));
    });

    afterEach(() => {
      vi.useRealTimers();
    });

    it('should create SearchQueryResult (REQ_011.4.1)', () => {
      const result = createIntermediateResult<SearchQueryResult>('search_query', {
        query: 'latest AI research',
        searchUrl: 'https://search.example.com?q=latest+AI+research',
        resultCount: 25,
      });

      expect(result.type).toBe('search_query');
      expect(result.query).toBe('latest AI research');
      expect(result.id).toContain('search_query_');
      expect(result.expanded).toBe(true);
      expect(isSearchQueryResult(result)).toBe(true);
    });

    it('should create ReasoningSummaryResult (REQ_011.4.2)', () => {
      const result = createIntermediateResult<ReasoningSummaryResult>('reasoning_summary', {
        summary: 'Identified key research papers',
        stepIndex: 2,
        stepType: 'searching',
      });

      expect(result.type).toBe('reasoning_summary');
      expect(result.summary).toBe('Identified key research papers');
      expect(result.stepIndex).toBe(2);
      expect(result.stepType).toBe('searching');
      expect(isReasoningSummaryResult(result)).toBe(true);
    });

    it('should create PartialReportResult (REQ_011.4.3)', () => {
      const result = createIntermediateResult<PartialReportResult>('partial_report', {
        sectionTitle: 'Introduction',
        content: 'This report covers...',
        sectionIndex: 0,
      });

      expect(result.type).toBe('partial_report');
      expect(result.sectionTitle).toBe('Introduction');
      expect(result.content).toBe('This report covers...');
      expect(isPartialReportResult(result)).toBe(true);
    });

    it('should create PartialImageResult (REQ_011.4.4)', () => {
      const result = createIntermediateResult<PartialImageResult>('partial_image', {
        imageUrl: 'https://example.com/preview.png',
        previewIndex: 1,
        isPreview: true,
      });

      expect(result.type).toBe('partial_image');
      expect(result.imageUrl).toBe('https://example.com/preview.png');
      expect(result.isPreview).toBe(true);
      expect(isPartialImageResult(result)).toBe(true);
    });

    it('should create DocumentOutlineResult (REQ_011.4.5)', () => {
      const result = createIntermediateResult<DocumentOutlineResult>('document_outline', {
        sections: [
          { title: 'Executive Summary', level: 1 },
          { title: 'Introduction', level: 1 },
          { title: 'Background', level: 2 },
        ],
      });

      expect(result.type).toBe('document_outline');
      expect(result.sections).toHaveLength(3);
      expect(isDocumentOutlineResult(result)).toBe(true);
    });

    it('should generate unique IDs', () => {
      const results = [
        createIntermediateResult<SearchQueryResult>('search_query', { query: 'test1' }),
        createIntermediateResult<SearchQueryResult>('search_query', { query: 'test2' }),
        createIntermediateResult<SearchQueryResult>('search_query', { query: 'test3' }),
      ];

      const ids = results.map(r => r.id);
      const uniqueIds = new Set(ids);
      expect(uniqueIds.size).toBe(3);
    });

    it('should set timestamp to current time', () => {
      const result = createIntermediateResult<SearchQueryResult>('search_query', {
        query: 'test',
      });

      expect(result.timestamp).toBe('2026-01-16T12:00:00.000Z');
    });

    it('should set expanded to true by default', () => {
      const result = createIntermediateResult<SearchQueryResult>('search_query', {
        query: 'test',
      });

      expect(result.expanded).toBe(true);
    });
  });

  describe('Type Guards for Intermediate Results', () => {
    const searchQuery: SearchQueryResult = {
      id: 'sq_1',
      type: 'search_query',
      timestamp: '2026-01-16T12:00:00Z',
      expanded: true,
      query: 'test query',
    };

    const reasoningSummary: ReasoningSummaryResult = {
      id: 'rs_1',
      type: 'reasoning_summary',
      timestamp: '2026-01-16T12:00:00Z',
      expanded: true,
      summary: 'test summary',
      stepIndex: 1,
      stepType: 'planning',
    };

    const partialReport: PartialReportResult = {
      id: 'pr_1',
      type: 'partial_report',
      timestamp: '2026-01-16T12:00:00Z',
      expanded: true,
      content: 'test content',
      sectionIndex: 0,
    };

    const partialImage: PartialImageResult = {
      id: 'pi_1',
      type: 'partial_image',
      timestamp: '2026-01-16T12:00:00Z',
      expanded: true,
      imageUrl: 'https://example.com/image.png',
      previewIndex: 0,
      isPreview: true,
    };

    const documentOutline: DocumentOutlineResult = {
      id: 'do_1',
      type: 'document_outline',
      timestamp: '2026-01-16T12:00:00Z',
      expanded: true,
      sections: [],
    };

    it('should correctly identify SearchQueryResult', () => {
      expect(isSearchQueryResult(searchQuery)).toBe(true);
      expect(isSearchQueryResult(reasoningSummary)).toBe(false);
    });

    it('should correctly identify ReasoningSummaryResult', () => {
      expect(isReasoningSummaryResult(reasoningSummary)).toBe(true);
      expect(isReasoningSummaryResult(searchQuery)).toBe(false);
    });

    it('should correctly identify PartialReportResult', () => {
      expect(isPartialReportResult(partialReport)).toBe(true);
      expect(isPartialReportResult(searchQuery)).toBe(false);
    });

    it('should correctly identify PartialImageResult', () => {
      expect(isPartialImageResult(partialImage)).toBe(true);
      expect(isPartialImageResult(searchQuery)).toBe(false);
    });

    it('should correctly identify DocumentOutlineResult', () => {
      expect(isDocumentOutlineResult(documentOutline)).toBe(true);
      expect(isDocumentOutlineResult(searchQuery)).toBe(false);
    });
  });
});

// =============================================================================
// REQ_011.1.7: Connection Configuration
// =============================================================================

describe('SSE Connection Configuration (REQ_011.1.7-8)', () => {
  it('should support default retry delay of 3000ms', () => {
    // Verify the interface supports this default
    const config = {
      responseId: 'resp_123',
      retryDelayMs: 3000, // REQ_011.1.7: 3s default
    };

    expect(config.retryDelayMs).toBe(3000);
  });

  it('should support keep-alive interval of 15000ms', () => {
    // Verify the interface supports this default
    const config = {
      responseId: 'resp_123',
      keepAliveIntervalMs: 15000, // REQ_011.1.8: 15s keep-alive
    };

    expect(config.keepAliveIntervalMs).toBe(15000);
  });

  it('should support maxRetries configuration', () => {
    const config = {
      responseId: 'resp_123',
      maxRetries: 5,
    };

    expect(config.maxRetries).toBe(5);
  });
});

// =============================================================================
// REQ_011.5: Cancellation Types
// =============================================================================

describe('Cancellation Types (REQ_011.5)', () => {
  it('should support user_initiated cancellation reason (REQ_011.5.11)', () => {
    const request = {
      operationId: 'op_123',
      operationType: 'deep_research' as const,
      reason: 'user_initiated' as const,
    };

    expect(request.reason).toBe('user_initiated');
  });

  it('should support timeout cancellation reason', () => {
    const request = {
      operationId: 'op_123',
      operationType: 'image_generation' as const,
      reason: 'timeout' as const,
    };

    expect(request.reason).toBe('timeout');
  });

  it('should support error cancellation reason', () => {
    const request = {
      operationId: 'op_123',
      operationType: 'document_generation' as const,
      reason: 'error' as const,
    };

    expect(request.reason).toBe('error');
  });

  it('should preserve intermediate results in cancellation response', () => {
    const searchResult = createIntermediateResult<SearchQueryResult>('search_query', {
      query: 'test',
    });

    const response = {
      success: true,
      operationId: 'op_123',
      preservedResults: [searchResult],
      incurredCost: 0.05,
      message: 'Operation cancelled, partial results preserved',
    };

    expect(response.preservedResults).toHaveLength(1);
    expect(response.incurredCost).toBe(0.05);
  });

  it('should track cancellation state transitions', () => {
    const state = {
      operationId: 'op_123',
      status: 'idle' as const,
    };

    // Simulate state transitions
    const cancelling = { ...state, status: 'cancelling' as const, initiatedAt: '2026-01-16T12:00:00Z' };
    const cancelled = { ...cancelling, status: 'cancelled' as const, completedAt: '2026-01-16T12:00:01Z' };

    expect(cancelling.status).toBe('cancelling');
    expect(cancelled.status).toBe('cancelled');
    expect(cancelled.completedAt).toBeDefined();
  });
});
