/**
 * Intermediate Results Module (REQ_011.4)
 *
 * Manages display of intermediate results during long-running operations.
 */

import type {
  IntermediateResult,
  IntermediateResultType,
  SearchQueryResult,
  ReasoningSummaryResult,
  PartialReportResult,
  PartialImageResult,
  DocumentOutlineResult,
  ReasoningStepType,
} from './streaming-types';

// =============================================================================
// Constants
// =============================================================================

/** Animation duration for fade-in (ms) REQ_011.4.7 */
export const FADE_IN_DURATION_MS = 300;

/** Maximum results to keep in memory */
export const MAX_RESULTS_IN_MEMORY = 100;

/** Result type display order */
export const RESULT_TYPE_ORDER: IntermediateResultType[] = [
  'search_query',
  'reasoning_summary',
  'partial_report',
  'partial_image',
  'document_outline',
];

// =============================================================================
// Types
// =============================================================================

/**
 * Intermediate results state
 */
export interface IntermediateResultsState {
  /** All results by ID */
  results: Map<string, IntermediateResult>;
  /** Results in display order */
  orderedIds: string[];
  /** Collapsed result IDs */
  collapsedIds: Set<string>;
  /** Current expected result type (for skeleton) REQ_011.4.11 */
  expectedNextType: IntermediateResultType | null;
  /** Final result available flag REQ_011.4.9 */
  hasFinalResult: boolean;
  /** Error results (non-blocking) REQ_011.4.12 */
  errors: Map<string, string>;
}

/**
 * Event handlers for intermediate results
 */
export interface IntermediateResultsHandlers {
  onResultAdded?: (result: IntermediateResult) => void;
  onResultUpdated?: (result: IntermediateResult) => void;
  onExpandCollapse?: (resultId: string, expanded: boolean) => void;
  onFinalResultAvailable?: () => void;
}

// =============================================================================
// State Management
// =============================================================================

/**
 * Create initial state
 */
export function createIntermediateResultsState(): IntermediateResultsState {
  return {
    results: new Map(),
    orderedIds: [],
    collapsedIds: new Set(),
    expectedNextType: null,
    hasFinalResult: false,
    errors: new Map(),
  };
}

/**
 * Add an intermediate result
 * REQ_011.4.6: Timestamped results
 */
export function addIntermediateResult(
  state: IntermediateResultsState,
  result: IntermediateResult
): IntermediateResultsState {
  const newResults = new Map(state.results);
  newResults.set(result.id, result);

  // Maintain order (newest last)
  const newOrderedIds = [...state.orderedIds, result.id];

  // Prune if over limit
  if (newOrderedIds.length > MAX_RESULTS_IN_MEMORY) {
    const toRemove = newOrderedIds.shift();
    if (toRemove) {
      newResults.delete(toRemove);
    }
  }

  return {
    ...state,
    results: newResults,
    orderedIds: newOrderedIds,
  };
}

/**
 * Update expected next result type
 * REQ_011.4.11: Loading skeleton for next type
 */
export function setExpectedNextType(
  state: IntermediateResultsState,
  type: IntermediateResultType | null
): IntermediateResultsState {
  return {
    ...state,
    expectedNextType: type,
  };
}

/**
 * Toggle expand/collapse for a result
 * REQ_011.4.8: Expand/collapse sections
 */
export function toggleResultExpanded(
  state: IntermediateResultsState,
  resultId: string
): IntermediateResultsState {
  const newCollapsed = new Set(state.collapsedIds);

  if (newCollapsed.has(resultId)) {
    newCollapsed.delete(resultId);
  } else {
    newCollapsed.add(resultId);
  }

  return {
    ...state,
    collapsedIds: newCollapsed,
  };
}

/**
 * Set result as expanded
 */
export function expandResult(
  state: IntermediateResultsState,
  resultId: string
): IntermediateResultsState {
  const newCollapsed = new Set(state.collapsedIds);
  newCollapsed.delete(resultId);
  return { ...state, collapsedIds: newCollapsed };
}

/**
 * Set result as collapsed
 */
export function collapseResult(
  state: IntermediateResultsState,
  resultId: string
): IntermediateResultsState {
  const newCollapsed = new Set(state.collapsedIds);
  newCollapsed.add(resultId);
  return { ...state, collapsedIds: newCollapsed };
}

/**
 * Collapse all results
 * REQ_011.4.10: Intermediate results collapsible after final
 */
export function collapseAllResults(
  state: IntermediateResultsState
): IntermediateResultsState {
  return {
    ...state,
    collapsedIds: new Set(state.orderedIds),
  };
}

/**
 * Mark final result as available
 * REQ_011.4.9: Distinguish final from intermediate
 */
export function markFinalResultAvailable(
  state: IntermediateResultsState
): IntermediateResultsState {
  return {
    ...state,
    hasFinalResult: true,
    expectedNextType: null,
  };
}

/**
 * Record an error for a result (non-blocking)
 * REQ_011.4.12: Errors don't block subsequent results
 */
export function recordResultError(
  state: IntermediateResultsState,
  resultId: string,
  error: string
): IntermediateResultsState {
  const newErrors = new Map(state.errors);
  newErrors.set(resultId, error);
  return { ...state, errors: newErrors };
}

// =============================================================================
// Result Creation Helpers
// =============================================================================

/**
 * Generate unique result ID
 */
function generateResultId(type: IntermediateResultType): string {
  return `${type}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

/**
 * Create a search query result
 * REQ_011.4.1: Display web search queries
 */
export function createSearchQueryResult(
  query: string,
  searchUrl?: string,
  resultCount?: number
): SearchQueryResult {
  return {
    id: generateResultId('search_query'),
    type: 'search_query',
    timestamp: new Date().toISOString(),
    expanded: true,
    query,
    searchUrl,
    resultCount,
  };
}

/**
 * Create a reasoning summary result
 * REQ_011.4.2: Display reasoning summaries (accordion)
 */
export function createReasoningSummaryResult(
  summary: string,
  stepIndex: number,
  stepType: ReasoningStepType
): ReasoningSummaryResult {
  return {
    id: generateResultId('reasoning_summary'),
    type: 'reasoning_summary',
    timestamp: new Date().toISOString(),
    expanded: true, // Start expanded
    summary,
    stepIndex,
    stepType,
  };
}

/**
 * Create a partial report result
 * REQ_011.4.3: Display partial report sections
 */
export function createPartialReportResult(
  content: string,
  sectionIndex: number,
  sectionTitle?: string
): PartialReportResult {
  return {
    id: generateResultId('partial_report'),
    type: 'partial_report',
    timestamp: new Date().toISOString(),
    expanded: true,
    content,
    sectionIndex,
    sectionTitle,
  };
}

/**
 * Create a partial image result
 * REQ_011.4.4: Display preview images with badge
 */
export function createPartialImageResult(
  imageUrl: string,
  previewIndex: number
): PartialImageResult {
  return {
    id: generateResultId('partial_image'),
    type: 'partial_image',
    timestamp: new Date().toISOString(),
    expanded: true,
    imageUrl,
    previewIndex,
    isPreview: true,
  };
}

/**
 * Create a document outline result
 * REQ_011.4.5: Display outline before full document
 */
export function createDocumentOutlineResult(
  sections: Array<{ title: string; level: number }>
): DocumentOutlineResult {
  return {
    id: generateResultId('document_outline'),
    type: 'document_outline',
    timestamp: new Date().toISOString(),
    expanded: true,
    sections,
  };
}

// =============================================================================
// Query Helpers
// =============================================================================

/**
 * Get results by type
 */
export function getResultsByType(
  state: IntermediateResultsState,
  type: IntermediateResultType
): IntermediateResult[] {
  return state.orderedIds
    .map(id => state.results.get(id))
    .filter((r): r is IntermediateResult => r !== undefined && r.type === type);
}

/**
 * Get all results in order
 */
export function getAllResults(state: IntermediateResultsState): IntermediateResult[] {
  return state.orderedIds
    .map(id => state.results.get(id))
    .filter((r): r is IntermediateResult => r !== undefined);
}

/**
 * Check if a result is expanded
 */
export function isResultExpanded(
  state: IntermediateResultsState,
  resultId: string
): boolean {
  return !state.collapsedIds.has(resultId);
}

/**
 * Get the count of results by type
 */
export function getResultCounts(
  state: IntermediateResultsState
): Record<IntermediateResultType, number> {
  const counts: Record<IntermediateResultType, number> = {
    search_query: 0,
    reasoning_summary: 0,
    partial_report: 0,
    partial_image: 0,
    document_outline: 0,
  };

  for (const id of state.orderedIds) {
    const result = state.results.get(id);
    if (result) {
      counts[result.type]++;
    }
  }

  return counts;
}

// =============================================================================
// Formatting Helpers
// =============================================================================

/**
 * Format timestamp for display
 * REQ_011.4.6: Timestamped results
 */
export function formatResultTimestamp(timestamp: string): string {
  const date = new Date(timestamp);
  return date.toLocaleTimeString('en-US', {
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
  });
}

/**
 * Get relative time (e.g., "2s ago")
 */
export function getRelativeTime(timestamp: string): string {
  const ms = Date.now() - new Date(timestamp).getTime();

  if (ms < 1000) return 'just now';
  if (ms < 60000) return `${Math.floor(ms / 1000)}s ago`;
  if (ms < 3600000) return `${Math.floor(ms / 60000)}m ago`;
  return formatResultTimestamp(timestamp);
}

/**
 * Get display label for result type
 */
export function getResultTypeLabel(type: IntermediateResultType): string {
  const labels: Record<IntermediateResultType, string> = {
    search_query: 'Web Search',
    reasoning_summary: 'Reasoning',
    partial_report: 'Report Section',
    partial_image: 'Preview Image',
    document_outline: 'Document Outline',
  };
  return labels[type];
}

/**
 * Get icon for result type
 */
export function getResultTypeIcon(type: IntermediateResultType): string {
  const icons: Record<IntermediateResultType, string> = {
    search_query: 'search',
    reasoning_summary: 'brain',
    partial_report: 'file-text',
    partial_image: 'image',
    document_outline: 'list',
  };
  return icons[type];
}

// =============================================================================
// Animation Helpers (REQ_011.4.7)
// =============================================================================

/**
 * Get CSS classes for fade-in animation
 * REQ_011.4.7: Fade-in transition
 */
export function getFadeInClasses(isNew: boolean): string {
  return isNew
    ? 'opacity-0 animate-fade-in'
    : 'opacity-100';
}

/**
 * CSS keyframes for fade-in (for style injection)
 */
export const FADE_IN_KEYFRAMES = `
@keyframes fadeIn {
  from { opacity: 0; transform: translateY(10px); }
  to { opacity: 1; transform: translateY(0); }
}

.animate-fade-in {
  animation: fadeIn ${FADE_IN_DURATION_MS}ms ease-out forwards;
}
`;

// =============================================================================
// Intermediate Results Manager
// =============================================================================

/**
 * Manager for intermediate results with event handling
 */
export class IntermediateResultsManager {
  private state: IntermediateResultsState;
  private handlers: IntermediateResultsHandlers;
  private newResultIds: Set<string> = new Set();

  constructor(handlers: IntermediateResultsHandlers = {}) {
    this.state = createIntermediateResultsState();
    this.handlers = handlers;
  }

  /**
   * Add a result
   */
  addResult(result: IntermediateResult): void {
    this.state = addIntermediateResult(this.state, result);
    this.newResultIds.add(result.id);
    this.handlers.onResultAdded?.(result);

    // Clear "new" flag after animation
    setTimeout(() => {
      this.newResultIds.delete(result.id);
    }, FADE_IN_DURATION_MS);
  }

  /**
   * Create and add a search query result
   * REQ_011.4.1
   */
  addSearchQuery(query: string, searchUrl?: string): SearchQueryResult {
    const result = createSearchQueryResult(query, searchUrl);
    this.addResult(result);
    return result;
  }

  /**
   * Create and add a reasoning summary
   * REQ_011.4.2
   */
  addReasoningSummary(
    summary: string,
    stepIndex: number,
    stepType: ReasoningStepType
  ): ReasoningSummaryResult {
    const result = createReasoningSummaryResult(summary, stepIndex, stepType);
    this.addResult(result);
    return result;
  }

  /**
   * Create and add a partial report section
   * REQ_011.4.3
   */
  addPartialReport(
    content: string,
    sectionIndex: number,
    sectionTitle?: string
  ): PartialReportResult {
    const result = createPartialReportResult(content, sectionIndex, sectionTitle);
    this.addResult(result);
    return result;
  }

  /**
   * Create and add a partial image
   * REQ_011.4.4
   */
  addPartialImage(imageUrl: string, previewIndex: number): PartialImageResult {
    const result = createPartialImageResult(imageUrl, previewIndex);
    this.addResult(result);
    return result;
  }

  /**
   * Create and add a document outline
   * REQ_011.4.5
   */
  addDocumentOutline(
    sections: Array<{ title: string; level: number }>
  ): DocumentOutlineResult {
    const result = createDocumentOutlineResult(sections);
    this.addResult(result);
    return result;
  }

  /**
   * Toggle result expansion
   * REQ_011.4.8
   */
  toggleExpanded(resultId: string): void {
    const wasExpanded = isResultExpanded(this.state, resultId);
    this.state = toggleResultExpanded(this.state, resultId);
    this.handlers.onExpandCollapse?.(resultId, !wasExpanded);
  }

  /**
   * Set expected next type
   * REQ_011.4.11
   */
  setExpectedNext(type: IntermediateResultType | null): void {
    this.state = setExpectedNextType(this.state, type);
  }

  /**
   * Mark final result available
   * REQ_011.4.9
   */
  markFinalAvailable(): void {
    this.state = markFinalResultAvailable(this.state);
    this.handlers.onFinalResultAvailable?.();
  }

  /**
   * Record error for a result
   * REQ_011.4.12
   */
  recordError(resultId: string, error: string): void {
    this.state = recordResultError(this.state, resultId, error);
  }

  /**
   * Collapse all results (useful after final result)
   * REQ_011.4.10
   */
  collapseAll(): void {
    this.state = collapseAllResults(this.state);
  }

  /**
   * Check if result is new (for animation)
   */
  isNew(resultId: string): boolean {
    return this.newResultIds.has(resultId);
  }

  /**
   * Get current state
   */
  getState(): IntermediateResultsState {
    return this.state;
  }

  /**
   * Get all results
   */
  getResults(): IntermediateResult[] {
    return getAllResults(this.state);
  }

  /**
   * Clear all results
   */
  clear(): void {
    this.state = createIntermediateResultsState();
    this.newResultIds.clear();
  }
}
