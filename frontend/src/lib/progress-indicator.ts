/**
 * Progress Indicator Module (REQ_011.3)
 *
 * Real-time progress tracking for long-running operations.
 */

import type {
  ProgressPhase,
  ProgressIndicatorState,
} from './streaming-types';

// =============================================================================
// Constants
// =============================================================================

/** Minimum progress update interval (ms) REQ_011.3.7 */
export const MIN_PROGRESS_UPDATE_INTERVAL_MS = 5000;

/** Typical durations for operations (ms) - used for estimates */
export const TYPICAL_DURATIONS = {
  deep_research_quick: 120000, // 2 minutes
  deep_research_thorough: 600000, // 10 minutes
  image_generation_low: 10000, // 10 seconds
  image_generation_medium: 20000, // 20 seconds
  image_generation_high: 45000, // 45 seconds
  document_generation: 30000, // 30 seconds
} as const;

/** Phase weights for progress calculation (sum to 100) */
export const PHASE_WEIGHTS: Record<string, Record<string, number>> = {
  deep_research: {
    analyzing: 10,
    searching: 40,
    reading: 30,
    synthesizing: 20,
  },
  image_generation: {
    processing: 10,
    generating: 80,
    finalizing: 10,
  },
  document_generation: {
    content: 50,
    creating: 30,
    uploading: 20,
  },
};

/** Tool-specific icons REQ_011.3.11 */
export const TOOL_ICONS: Record<string, string> = {
  deep_research: 'search', // Magnifying glass
  image_generation: 'palette', // Palette/brush
  document_generation: 'file-text', // Document
};

// =============================================================================
// Types
// =============================================================================

/**
 * Progress update event
 */
export interface ProgressUpdateEvent {
  operationId: string;
  phase: string;
  phaseProgress: number; // 0-100 within phase
  overallProgress: number; // 0-100 overall
  elapsedMs: number;
  estimatedRemainingMs?: number;
  message?: string;
}

/**
 * Progress persistence data
 * REQ_011.3.12: Persist across navigation
 */
export interface PersistedProgress {
  operationId: string;
  operationType: ProgressIndicatorState['operationType'];
  state: ProgressIndicatorState;
  lastUpdated: string;
}

// =============================================================================
// Progress Calculator
// =============================================================================

/**
 * Calculate overall progress from phase progress
 * REQ_011.3.10: Proportional progress
 */
export function calculateOverallProgress(
  operationType: ProgressIndicatorState['operationType'],
  currentPhaseId: string,
  phaseProgress: number,
  completedPhases: string[]
): number {
  const weights = PHASE_WEIGHTS[operationType];
  if (!weights) return 0;

  let totalProgress = 0;

  // Add completed phases
  for (const phaseId of completedPhases) {
    totalProgress += weights[phaseId] || 0;
  }

  // Add current phase progress
  const currentWeight = weights[currentPhaseId] || 0;
  totalProgress += (currentWeight * phaseProgress) / 100;

  return Math.min(Math.round(totalProgress), 100);
}

/**
 * Estimate remaining time based on elapsed time and progress
 * REQ_011.3.9: Estimated time remaining
 */
export function estimateRemainingTime(
  operationType: string,
  elapsedMs: number,
  progressPercentage: number,
  variant?: string
): number | undefined {
  if (progressPercentage === 0 || progressPercentage >= 100) {
    return undefined;
  }

  // Use typical duration as baseline
  let typicalDuration: number;
  if (operationType === 'deep_research') {
    typicalDuration =
      variant === 'thorough'
        ? TYPICAL_DURATIONS.deep_research_thorough
        : TYPICAL_DURATIONS.deep_research_quick;
  } else if (operationType === 'image_generation') {
    typicalDuration =
      variant === 'high'
        ? TYPICAL_DURATIONS.image_generation_high
        : variant === 'medium'
          ? TYPICAL_DURATIONS.image_generation_medium
          : TYPICAL_DURATIONS.image_generation_low;
  } else {
    typicalDuration = TYPICAL_DURATIONS.document_generation;
  }

  // Calculate based on current rate and typical duration
  const rateBasedEstimate =
    (elapsedMs / progressPercentage) * (100 - progressPercentage);
  const typicalBasedEstimate = typicalDuration * (1 - progressPercentage / 100);

  // Weighted average (favor rate-based as progress increases)
  const weight = Math.min(progressPercentage / 50, 1); // 0-1 based on progress
  const estimate =
    rateBasedEstimate * weight + typicalBasedEstimate * (1 - weight);

  return Math.round(estimate);
}

// =============================================================================
// Time Formatting
// =============================================================================

/**
 * Format elapsed time as MM:SS
 * REQ_011.3.8: MM:SS format
 */
export function formatElapsedTime(ms: number): string {
  const totalSeconds = Math.floor(ms / 1000);
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = totalSeconds % 60;
  return `${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`;
}

/**
 * Format remaining time in human-readable format
 */
export function formatRemainingTime(ms: number | undefined): string {
  if (ms === undefined) return '';

  if (ms < 60000) {
    return `~${Math.ceil(ms / 1000)}s remaining`;
  }

  const minutes = Math.ceil(ms / 60000);
  return `~${minutes}m remaining`;
}

// =============================================================================
// Progress State Management
// =============================================================================

/**
 * Create initial progress state
 */
export function createInitialProgressState(
  operationType: ProgressIndicatorState['operationType']
): ProgressIndicatorState {
  const phasesMap = {
    deep_research: [
      { id: 'analyzing', label: 'Analyzing query', status: 'pending' as const },
      { id: 'searching', label: 'Searching web', status: 'pending' as const },
      { id: 'reading', label: 'Reading sources', status: 'pending' as const },
      {
        id: 'synthesizing',
        label: 'Synthesizing report',
        status: 'pending' as const,
      },
    ],
    image_generation: [
      {
        id: 'processing',
        label: 'Processing prompt',
        status: 'pending' as const,
      },
      {
        id: 'generating',
        label: 'Generating image',
        status: 'pending' as const,
      },
      { id: 'finalizing', label: 'Finalizing', status: 'pending' as const },
    ],
    document_generation: [
      {
        id: 'content',
        label: 'Generating content',
        status: 'pending' as const,
      },
      {
        id: 'creating',
        label: 'Creating document',
        status: 'pending' as const,
      },
      { id: 'uploading', label: 'Uploading file', status: 'pending' as const },
    ],
  };

  return {
    operationType,
    phases: phasesMap[operationType],
    currentPhaseIndex: 0,
    progressPercentage: 0,
    startedAt: new Date().toISOString(),
    elapsedMs: 0,
    isComplete: false,
  };
}

/**
 * Update progress state with new phase status
 */
export function updatePhaseStatus(
  state: ProgressIndicatorState,
  phaseId: string,
  status: ProgressPhase['status']
): ProgressIndicatorState {
  const phases = state.phases.map((phase) => {
    if (phase.id === phaseId) {
      const now = new Date().toISOString();
      return {
        ...phase,
        status,
        startedAt: status === 'active' ? now : phase.startedAt,
        completedAt: status === 'completed' ? now : phase.completedAt,
      };
    }
    return phase;
  });

  // Find new current phase index
  const activeIndex = phases.findIndex((p) => p.status === 'active');
  const currentPhaseIndex =
    activeIndex >= 0 ? activeIndex : state.currentPhaseIndex;

  // Calculate progress
  const completedPhases = phases
    .filter((p) => p.status === 'completed')
    .map((p) => p.id);
  const currentPhase = phases[currentPhaseIndex];
  const progressPercentage = calculateOverallProgress(
    state.operationType,
    currentPhase?.id || '',
    status === 'active' ? 50 : 0,
    completedPhases
  );

  const elapsedMs = Date.now() - new Date(state.startedAt).getTime();
  const estimatedRemainingMs = estimateRemainingTime(
    state.operationType,
    elapsedMs,
    progressPercentage
  );

  return {
    ...state,
    phases,
    currentPhaseIndex,
    progressPercentage,
    elapsedMs,
    estimatedRemainingMs,
  };
}

/**
 * Update progress within current phase
 */
export function updatePhaseProgress(
  state: ProgressIndicatorState,
  phaseProgress: number
): ProgressIndicatorState {
  const currentPhase = state.phases[state.currentPhaseIndex];
  if (!currentPhase) return state;

  const completedPhases = state.phases
    .filter((p) => p.status === 'completed')
    .map((p) => p.id);

  const progressPercentage = calculateOverallProgress(
    state.operationType,
    currentPhase.id,
    phaseProgress,
    completedPhases
  );

  const elapsedMs = Date.now() - new Date(state.startedAt).getTime();
  const estimatedRemainingMs = estimateRemainingTime(
    state.operationType,
    elapsedMs,
    progressPercentage
  );

  return {
    ...state,
    progressPercentage,
    elapsedMs,
    estimatedRemainingMs,
  };
}

/**
 * Mark progress as complete
 */
export function completeProgress(
  state: ProgressIndicatorState
): ProgressIndicatorState {
  return {
    ...state,
    phases: state.phases.map((p) => ({
      ...p,
      status: 'completed' as const,
      completedAt: p.completedAt || new Date().toISOString(),
    })),
    currentPhaseIndex: state.phases.length - 1,
    progressPercentage: 100,
    elapsedMs: Date.now() - new Date(state.startedAt).getTime(),
    estimatedRemainingMs: undefined,
    isComplete: true,
  };
}

/**
 * Mark progress as errored
 */
export function errorProgress(
  state: ProgressIndicatorState,
  error: string
): ProgressIndicatorState {
  return {
    ...state,
    phases: state.phases.map((p, i) =>
      i === state.currentPhaseIndex ? { ...p, status: 'error' as const } : p
    ),
    error,
    elapsedMs: Date.now() - new Date(state.startedAt).getTime(),
  };
}

// =============================================================================
// Persistence (REQ_011.3.12)
// =============================================================================

const PROGRESS_STORAGE_KEY = 'silmari_progress_state';

/**
 * Save progress state to sessionStorage
 */
export function persistProgress(
  operationId: string,
  state: ProgressIndicatorState
): void {
  try {
    const data: PersistedProgress = {
      operationId,
      operationType: state.operationType,
      state,
      lastUpdated: new Date().toISOString(),
    };

    // Use sessionStorage for tab-specific persistence
    if (typeof window !== 'undefined' && window.sessionStorage) {
      const stored = window.sessionStorage.getItem(PROGRESS_STORAGE_KEY);
      const all: Record<string, PersistedProgress> = stored
        ? JSON.parse(stored)
        : {};
      all[operationId] = data;
      window.sessionStorage.setItem(PROGRESS_STORAGE_KEY, JSON.stringify(all));
    }
  } catch (error) {
    console.warn('[ProgressIndicator] Failed to persist progress:', error);
  }
}

/**
 * Load persisted progress state
 */
export function loadPersistedProgress(
  operationId: string
): ProgressIndicatorState | null {
  try {
    if (typeof window !== 'undefined' && window.sessionStorage) {
      const stored = window.sessionStorage.getItem(PROGRESS_STORAGE_KEY);
      if (stored) {
        const all: Record<string, PersistedProgress> = JSON.parse(stored);
        const data = all[operationId];
        if (data) {
          // Update elapsed time
          const elapsed = Date.now() - new Date(data.state.startedAt).getTime();
          return { ...data.state, elapsedMs: elapsed };
        }
      }
    }
  } catch (error) {
    console.warn(
      '[ProgressIndicator] Failed to load persisted progress:',
      error
    );
  }
  return null;
}

/**
 * Clear persisted progress for an operation
 */
export function clearPersistedProgress(operationId: string): void {
  try {
    if (typeof window !== 'undefined' && window.sessionStorage) {
      const stored = window.sessionStorage.getItem(PROGRESS_STORAGE_KEY);
      if (stored) {
        const all: Record<string, PersistedProgress> = JSON.parse(stored);
        delete all[operationId];
        window.sessionStorage.setItem(PROGRESS_STORAGE_KEY, JSON.stringify(all));
      }
    }
  } catch (error) {
    console.warn(
      '[ProgressIndicator] Failed to clear persisted progress:',
      error
    );
  }
}

/**
 * Clear all persisted progress (cleanup old entries)
 */
export function clearAllPersistedProgress(): void {
  try {
    if (typeof window !== 'undefined' && window.sessionStorage) {
      window.sessionStorage.removeItem(PROGRESS_STORAGE_KEY);
    }
  } catch (error) {
    console.warn(
      '[ProgressIndicator] Failed to clear all persisted progress:',
      error
    );
  }
}

// =============================================================================
// Accessibility (REQ_011.3.13)
// =============================================================================

/**
 * Generate accessible announcement for phase change
 * REQ_011.3.13: Screen reader support
 */
export function generateProgressAnnouncement(
  state: ProgressIndicatorState,
  previousPhase?: string
): string {
  const currentPhase = state.phases[state.currentPhaseIndex];

  if (state.isComplete) {
    return `Operation complete. Total time: ${formatElapsedTime(state.elapsedMs)}`;
  }

  if (state.error) {
    return `Operation failed: ${state.error}`;
  }

  if (!currentPhase) {
    return `Progress: ${state.progressPercentage}%`;
  }

  if (previousPhase && previousPhase !== currentPhase.id) {
    return `Now ${currentPhase.label}. ${state.progressPercentage}% complete.`;
  }

  return `${currentPhase.label}. ${state.progressPercentage}% complete.`;
}

/**
 * Get ARIA attributes for progress element
 */
export function getProgressAriaAttributes(state: ProgressIndicatorState): {
  'aria-valuenow': number;
  'aria-valuemin': number;
  'aria-valuemax': number;
  'aria-valuetext': string;
  role: string;
} {
  const currentPhase = state.phases[state.currentPhaseIndex];
  const valueText = state.isComplete
    ? 'Complete'
    : state.error
      ? `Error: ${state.error}`
      : `${state.progressPercentage}%, ${currentPhase?.label || 'In progress'}`;

  return {
    'aria-valuenow': state.progressPercentage,
    'aria-valuemin': 0,
    'aria-valuemax': 100,
    'aria-valuetext': valueText,
    role: 'progressbar',
  };
}

// =============================================================================
// Progress Timer
// =============================================================================

/**
 * Create a progress timer for regular updates
 * REQ_011.3.7: Updates at least every 5 seconds
 */
export function createProgressTimer(
  onTick: (elapsedMs: number) => void,
  intervalMs: number = MIN_PROGRESS_UPDATE_INTERVAL_MS
): { start: () => void; stop: () => void } {
  let intervalId: ReturnType<typeof setInterval> | null = null;
  const startTime = Date.now();

  return {
    start: () => {
      if (intervalId) return;
      intervalId = setInterval(() => {
        onTick(Date.now() - startTime);
      }, intervalMs);
    },
    stop: () => {
      if (intervalId) {
        clearInterval(intervalId);
        intervalId = null;
      }
    },
  };
}

// =============================================================================
// Exports for UI Components
// =============================================================================

/**
 * Get icon name for operation type
 * REQ_011.3.11: Tool-specific icons
 */
export function getToolIcon(operationType: string): string {
  return TOOL_ICONS[operationType] || 'loader';
}

/**
 * Get phase status icon
 * REQ_011.3.4-6: Visual indicators
 */
export function getPhaseStatusIcon(status: ProgressPhase['status']): string {
  switch (status) {
    case 'completed':
      return 'check'; // REQ_011.3.5: Checkmark
    case 'active':
      return 'loader'; // REQ_011.3.4: Spinner/pulsing
    case 'error':
      return 'x';
    case 'pending':
    default:
      return 'circle'; // REQ_011.3.6: Empty circle
  }
}
