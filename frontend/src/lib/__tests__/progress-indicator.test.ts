/**
 * Unit tests for Progress Indicator utilities
 * REQ_011.3: Progress indicator for long-running operations
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

import {
  MIN_PROGRESS_UPDATE_INTERVAL_MS,
  TYPICAL_DURATIONS,
  PHASE_WEIGHTS,
  TOOL_ICONS,
  calculateOverallProgress,
  estimateRemainingTime,
  formatElapsedTime,
  formatRemainingTime,
  createInitialProgressState,
  updatePhaseStatus,
  updatePhaseProgress,
  completeProgress,
  errorProgress,
  persistProgress,
  loadPersistedProgress,
  clearPersistedProgress,
  clearAllPersistedProgress,
  generateProgressAnnouncement,
  getProgressAriaAttributes,
  createProgressTimer,
  getToolIcon,
  getPhaseStatusIcon,
} from '../progress-indicator';

import type { ProgressIndicatorState } from '../streaming-types';

// Mock sessionStorage
const mockSessionStorage: Record<string, string> = {};
const mockStorage = {
  getItem: vi.fn((key: string) => mockSessionStorage[key] || null),
  setItem: vi.fn((key: string, value: string) => {
    mockSessionStorage[key] = value;
  }),
  removeItem: vi.fn((key: string) => {
    delete mockSessionStorage[key];
  }),
};

describe('Progress Indicator Utilities (REQ_011.3)', () => {
  beforeEach(() => {
    vi.resetAllMocks();
    vi.useFakeTimers();
    Object.keys(mockSessionStorage).forEach(
      (key) => delete mockSessionStorage[key]
    );

    // Mock window.sessionStorage
    Object.defineProperty(global, 'window', {
      value: { sessionStorage: mockStorage },
      writable: true,
    });
  });

  afterEach(() => {
    vi.restoreAllMocks();
    vi.useRealTimers();
  });

  describe('Constants (REQ_011.3)', () => {
    it('should have minimum progress update interval of 5 seconds (REQ_011.3.7)', () => {
      expect(MIN_PROGRESS_UPDATE_INTERVAL_MS).toBe(5000);
    });

    it('should have typical durations defined', () => {
      expect(TYPICAL_DURATIONS.deep_research_quick).toBe(120000);
      expect(TYPICAL_DURATIONS.deep_research_thorough).toBe(600000);
      expect(TYPICAL_DURATIONS.image_generation_low).toBe(10000);
      expect(TYPICAL_DURATIONS.image_generation_medium).toBe(20000);
      expect(TYPICAL_DURATIONS.image_generation_high).toBe(45000);
      expect(TYPICAL_DURATIONS.document_generation).toBe(30000);
    });

    it('should have phase weights that sum to 100 for each operation type', () => {
      for (const [operationType, weights] of Object.entries(PHASE_WEIGHTS)) {
        const sum = Object.values(weights).reduce((a, b) => a + b, 0);
        expect(sum).toBe(100);
      }
    });

    it('should have tool-specific icons defined (REQ_011.3.11)', () => {
      expect(TOOL_ICONS.deep_research).toBe('search');
      expect(TOOL_ICONS.image_generation).toBe('palette');
      expect(TOOL_ICONS.document_generation).toBe('file-text');
    });
  });

  describe('calculateOverallProgress (REQ_011.3.10)', () => {
    it('should return 0 for unknown operation type', () => {
      const result = calculateOverallProgress(
        'unknown' as unknown as Parameters<typeof calculateOverallProgress>[0],
        'phase1',
        50,
        []
      );
      expect(result).toBe(0);
    });

    it('should calculate progress with no completed phases', () => {
      const result = calculateOverallProgress('deep_research', 'analyzing', 50, []);
      // analyzing has weight 10, 50% of 10 = 5
      expect(result).toBe(5);
    });

    it('should calculate progress with completed phases', () => {
      const result = calculateOverallProgress(
        'deep_research',
        'searching',
        50,
        ['analyzing']
      );
      // analyzing (10) completed + 50% of searching (40) = 10 + 20 = 30
      expect(result).toBe(30);
    });

    it('should cap progress at 100', () => {
      const result = calculateOverallProgress(
        'deep_research',
        'synthesizing',
        100,
        ['analyzing', 'searching', 'reading']
      );
      expect(result).toBe(100);
    });

    it('should handle image_generation phases', () => {
      const result = calculateOverallProgress(
        'image_generation',
        'generating',
        50,
        ['processing']
      );
      // processing (10) + 50% of generating (80) = 10 + 40 = 50
      expect(result).toBe(50);
    });

    it('should handle document_generation phases', () => {
      const result = calculateOverallProgress(
        'document_generation',
        'creating',
        100,
        ['content']
      );
      // content (50) + 100% of creating (30) = 80
      expect(result).toBe(80);
    });
  });

  describe('estimateRemainingTime (REQ_011.3.9)', () => {
    it('should return undefined when progress is 0', () => {
      const result = estimateRemainingTime('deep_research', 10000, 0);
      expect(result).toBeUndefined();
    });

    it('should return undefined when progress is 100', () => {
      const result = estimateRemainingTime('deep_research', 120000, 100);
      expect(result).toBeUndefined();
    });

    it('should estimate time for deep research quick', () => {
      const result = estimateRemainingTime('deep_research', 60000, 50);
      expect(result).toBeDefined();
      expect(typeof result).toBe('number');
      expect(result).toBeGreaterThan(0);
    });

    it('should estimate time for deep research thorough', () => {
      const result = estimateRemainingTime('deep_research', 60000, 10, 'thorough');
      expect(result).toBeDefined();
      expect(result).toBeGreaterThan(0);
    });

    it('should estimate time for image generation variants', () => {
      const lowResult = estimateRemainingTime('image_generation', 5000, 50, 'low');
      const mediumResult = estimateRemainingTime('image_generation', 10000, 50, 'medium');
      const highResult = estimateRemainingTime('image_generation', 22500, 50, 'high');

      expect(lowResult).toBeDefined();
      expect(mediumResult).toBeDefined();
      expect(highResult).toBeDefined();
    });

    it('should estimate time for document generation', () => {
      const result = estimateRemainingTime('document_generation', 15000, 50);
      expect(result).toBeDefined();
      expect(result).toBeGreaterThan(0);
    });
  });

  describe('formatElapsedTime (REQ_011.3.8)', () => {
    it('should format 0ms as 00:00', () => {
      expect(formatElapsedTime(0)).toBe('00:00');
    });

    it('should format seconds correctly', () => {
      expect(formatElapsedTime(5000)).toBe('00:05');
      expect(formatElapsedTime(45000)).toBe('00:45');
    });

    it('should format minutes correctly', () => {
      expect(formatElapsedTime(60000)).toBe('01:00');
      expect(formatElapsedTime(125000)).toBe('02:05');
    });

    it('should handle large values', () => {
      expect(formatElapsedTime(600000)).toBe('10:00');
      expect(formatElapsedTime(3599000)).toBe('59:59');
    });
  });

  describe('formatRemainingTime', () => {
    it('should return empty string for undefined', () => {
      expect(formatRemainingTime(undefined)).toBe('');
    });

    it('should format seconds for values under 1 minute', () => {
      expect(formatRemainingTime(5000)).toBe('~5s remaining');
      expect(formatRemainingTime(45000)).toBe('~45s remaining');
    });

    it('should format minutes for values over 1 minute', () => {
      expect(formatRemainingTime(60000)).toBe('~1m remaining');
      expect(formatRemainingTime(120000)).toBe('~2m remaining');
      expect(formatRemainingTime(90000)).toBe('~2m remaining'); // Rounds up
    });
  });

  describe('createInitialProgressState', () => {
    it('should create initial state for deep_research (REQ_011.3.1)', () => {
      const state = createInitialProgressState('deep_research');

      expect(state.operationType).toBe('deep_research');
      expect(state.phases).toHaveLength(4);
      expect(state.phases[0].label).toBe('Analyzing query');
      expect(state.phases[1].label).toBe('Searching web');
      expect(state.phases[2].label).toBe('Reading sources');
      expect(state.phases[3].label).toBe('Synthesizing report');
      expect(state.phases.every((p) => p.status === 'pending')).toBe(true);
      expect(state.currentPhaseIndex).toBe(0);
      expect(state.progressPercentage).toBe(0);
      expect(state.isComplete).toBe(false);
    });

    it('should create initial state for image_generation (REQ_011.3.2)', () => {
      const state = createInitialProgressState('image_generation');

      expect(state.operationType).toBe('image_generation');
      expect(state.phases).toHaveLength(3);
      expect(state.phases[0].label).toBe('Processing prompt');
      expect(state.phases[1].label).toBe('Generating image');
      expect(state.phases[2].label).toBe('Finalizing');
    });

    it('should create initial state for document_generation (REQ_011.3.3)', () => {
      const state = createInitialProgressState('document_generation');

      expect(state.operationType).toBe('document_generation');
      expect(state.phases).toHaveLength(3);
      expect(state.phases[0].label).toBe('Generating content');
      expect(state.phases[1].label).toBe('Creating document');
      expect(state.phases[2].label).toBe('Uploading file');
    });

    it('should set startedAt timestamp', () => {
      const before = new Date().toISOString();
      const state = createInitialProgressState('deep_research');
      const after = new Date().toISOString();

      expect(state.startedAt >= before).toBe(true);
      expect(state.startedAt <= after).toBe(true);
    });
  });

  describe('updatePhaseStatus (REQ_011.3.4-6)', () => {
    let initialState: ProgressIndicatorState;

    beforeEach(() => {
      initialState = createInitialProgressState('deep_research');
    });

    it('should update phase to active (REQ_011.3.4)', () => {
      const updated = updatePhaseStatus(initialState, 'analyzing', 'active');

      expect(updated.phases[0].status).toBe('active');
      expect(updated.phases[0].startedAt).toBeDefined();
      expect(updated.currentPhaseIndex).toBe(0);
    });

    it('should update phase to completed (REQ_011.3.5)', () => {
      const activeState = updatePhaseStatus(initialState, 'analyzing', 'active');
      const updated = updatePhaseStatus(activeState, 'analyzing', 'completed');

      expect(updated.phases[0].status).toBe('completed');
      expect(updated.phases[0].completedAt).toBeDefined();
    });

    it('should calculate progress when phases complete', () => {
      const state1 = updatePhaseStatus(initialState, 'analyzing', 'completed');
      const state2 = updatePhaseStatus(state1, 'searching', 'active');

      // analyzing (10) completed + 50% of searching during active = 30
      expect(state2.progressPercentage).toBe(30);
    });

    it('should update estimatedRemainingMs when phase changes', () => {
      vi.setSystemTime(Date.now() + 30000); // Advance 30 seconds
      const updated = updatePhaseStatus(initialState, 'analyzing', 'active');

      expect(updated.estimatedRemainingMs).toBeDefined();
    });
  });

  describe('updatePhaseProgress', () => {
    it('should update progress within current phase', () => {
      let state = createInitialProgressState('image_generation');
      state = updatePhaseStatus(state, 'processing', 'completed');
      state = updatePhaseStatus(state, 'generating', 'active');

      const updated = updatePhaseProgress(state, 50);

      // processing (10) + 50% of generating (80) = 50
      expect(updated.progressPercentage).toBe(50);
    });

    it('should return unchanged state if no current phase', () => {
      const state = createInitialProgressState('deep_research');
      const modifiedState = { ...state, currentPhaseIndex: 10 }; // Out of bounds

      const updated = updatePhaseProgress(modifiedState, 50);

      expect(updated).toEqual(modifiedState);
    });
  });

  describe('completeProgress', () => {
    it('should mark all phases as completed', () => {
      const state = createInitialProgressState('deep_research');
      const completed = completeProgress(state);

      expect(completed.phases.every((p) => p.status === 'completed')).toBe(true);
      expect(completed.progressPercentage).toBe(100);
      expect(completed.isComplete).toBe(true);
      expect(completed.estimatedRemainingMs).toBeUndefined();
    });

    it('should set completedAt for phases without it', () => {
      const state = createInitialProgressState('image_generation');
      const completed = completeProgress(state);

      expect(completed.phases.every((p) => p.completedAt !== undefined)).toBe(
        true
      );
    });
  });

  describe('errorProgress', () => {
    it('should mark current phase as error', () => {
      let state = createInitialProgressState('deep_research');
      state = updatePhaseStatus(state, 'analyzing', 'completed');
      state = updatePhaseStatus(state, 'searching', 'active');

      const errored = errorProgress(state, 'Network error');

      expect(errored.phases[1].status).toBe('error');
      expect(errored.error).toBe('Network error');
    });
  });

  describe('Persistence (REQ_011.3.12)', () => {
    describe('persistProgress', () => {
      it('should save progress to sessionStorage', () => {
        const state = createInitialProgressState('deep_research');
        persistProgress('op-123', state);

        expect(mockStorage.setItem).toHaveBeenCalledWith(
          'silmari_progress_state',
          expect.any(String)
        );

        const savedData = JSON.parse(
          mockStorage.setItem.mock.calls[0][1] as string
        );
        expect(savedData['op-123']).toBeDefined();
        expect(savedData['op-123'].operationId).toBe('op-123');
        expect(savedData['op-123'].operationType).toBe('deep_research');
      });

      it('should preserve existing persisted progress', () => {
        // First save
        const state1 = createInitialProgressState('deep_research');
        persistProgress('op-123', state1);

        // Second save
        const state2 = createInitialProgressState('image_generation');
        persistProgress('op-456', state2);

        const savedData = JSON.parse(mockSessionStorage['silmari_progress_state']);
        expect(savedData['op-123']).toBeDefined();
        expect(savedData['op-456']).toBeDefined();
      });
    });

    describe('loadPersistedProgress', () => {
      it('should load persisted progress', () => {
        const state = createInitialProgressState('deep_research');
        const persistedData = {
          'op-123': {
            operationId: 'op-123',
            operationType: 'deep_research',
            state,
            lastUpdated: new Date().toISOString(),
          },
        };
        mockSessionStorage['silmari_progress_state'] = JSON.stringify(persistedData);

        const loaded = loadPersistedProgress('op-123');

        expect(loaded).not.toBeNull();
        expect(loaded?.operationType).toBe('deep_research');
      });

      it('should return null for non-existent operation', () => {
        const loaded = loadPersistedProgress('non-existent');

        expect(loaded).toBeNull();
      });

      it('should update elapsed time when loading', () => {
        const startedAt = new Date(Date.now() - 30000).toISOString(); // 30 seconds ago
        const state: ProgressIndicatorState = {
          operationType: 'deep_research',
          phases: [],
          currentPhaseIndex: 0,
          progressPercentage: 50,
          startedAt,
          elapsedMs: 0,
          isComplete: false,
        };

        const persistedData = {
          'op-123': {
            operationId: 'op-123',
            operationType: 'deep_research',
            state,
            lastUpdated: new Date().toISOString(),
          },
        };
        mockSessionStorage['silmari_progress_state'] = JSON.stringify(persistedData);

        const loaded = loadPersistedProgress('op-123');

        expect(loaded?.elapsedMs).toBeGreaterThanOrEqual(30000);
      });
    });

    describe('clearPersistedProgress', () => {
      it('should clear specific operation', () => {
        const persistedData = {
          'op-123': { operationId: 'op-123' },
          'op-456': { operationId: 'op-456' },
        };
        mockSessionStorage['silmari_progress_state'] = JSON.stringify(persistedData);

        clearPersistedProgress('op-123');

        const remaining = JSON.parse(mockSessionStorage['silmari_progress_state']);
        expect(remaining['op-123']).toBeUndefined();
        expect(remaining['op-456']).toBeDefined();
      });
    });

    describe('clearAllPersistedProgress', () => {
      it('should remove all persisted progress', () => {
        mockSessionStorage['silmari_progress_state'] = JSON.stringify({
          'op-123': {},
        });

        clearAllPersistedProgress();

        expect(mockStorage.removeItem).toHaveBeenCalledWith('silmari_progress_state');
      });
    });
  });

  describe('Accessibility (REQ_011.3.13)', () => {
    describe('generateProgressAnnouncement', () => {
      it('should announce completion', () => {
        const state = completeProgress(createInitialProgressState('deep_research'));
        const announcement = generateProgressAnnouncement(state);

        expect(announcement).toContain('Operation complete');
        expect(announcement).toContain('Total time:');
      });

      it('should announce error', () => {
        let state = createInitialProgressState('deep_research');
        state = errorProgress(state, 'Network error');

        const announcement = generateProgressAnnouncement(state);

        expect(announcement).toContain('Operation failed');
        expect(announcement).toContain('Network error');
      });

      it('should announce phase change', () => {
        let state = createInitialProgressState('deep_research');
        state = updatePhaseStatus(state, 'analyzing', 'completed');
        state = updatePhaseStatus(state, 'searching', 'active');

        const announcement = generateProgressAnnouncement(state, 'analyzing');

        expect(announcement).toContain('Now Searching web');
        expect(announcement).toContain('% complete');
      });

      it('should announce current phase without change', () => {
        let state = createInitialProgressState('image_generation');
        state = updatePhaseStatus(state, 'processing', 'active');

        const announcement = generateProgressAnnouncement(state);

        expect(announcement).toContain('Processing prompt');
        expect(announcement).toContain('% complete');
      });

      it('should handle empty phases gracefully', () => {
        const state: ProgressIndicatorState = {
          operationType: 'deep_research',
          phases: [],
          currentPhaseIndex: 0,
          progressPercentage: 50,
          startedAt: new Date().toISOString(),
          elapsedMs: 0,
          isComplete: false,
        };

        const announcement = generateProgressAnnouncement(state);

        expect(announcement).toContain('Progress: 50%');
      });
    });

    describe('getProgressAriaAttributes', () => {
      it('should return correct attributes for in-progress state', () => {
        let state = createInitialProgressState('deep_research');
        state = updatePhaseStatus(state, 'analyzing', 'active');

        const attrs = getProgressAriaAttributes(state);

        expect(attrs.role).toBe('progressbar');
        expect(attrs['aria-valuemin']).toBe(0);
        expect(attrs['aria-valuemax']).toBe(100);
        expect(attrs['aria-valuenow']).toBe(state.progressPercentage);
        expect(attrs['aria-valuetext']).toContain('Analyzing query');
      });

      it('should return complete text for completed state', () => {
        const state = completeProgress(createInitialProgressState('deep_research'));

        const attrs = getProgressAriaAttributes(state);

        expect(attrs['aria-valuetext']).toBe('Complete');
      });

      it('should return error text for errored state', () => {
        let state = createInitialProgressState('deep_research');
        state = errorProgress(state, 'Test error');

        const attrs = getProgressAriaAttributes(state);

        expect(attrs['aria-valuetext']).toContain('Error: Test error');
      });
    });
  });

  describe('createProgressTimer (REQ_011.3.7)', () => {
    it('should call onTick at specified interval', () => {
      const onTick = vi.fn();
      const timer = createProgressTimer(onTick, 1000);

      timer.start();

      vi.advanceTimersByTime(3000);

      expect(onTick).toHaveBeenCalledTimes(3);
      expect(onTick).toHaveBeenCalledWith(expect.any(Number));

      timer.stop();
    });

    it('should not start multiple intervals', () => {
      const onTick = vi.fn();
      const timer = createProgressTimer(onTick, 1000);

      timer.start();
      timer.start(); // Should not create another interval

      vi.advanceTimersByTime(2000);

      expect(onTick).toHaveBeenCalledTimes(2);

      timer.stop();
    });

    it('should stop when stop is called', () => {
      const onTick = vi.fn();
      const timer = createProgressTimer(onTick, 1000);

      timer.start();
      vi.advanceTimersByTime(2000);
      timer.stop();
      vi.advanceTimersByTime(2000);

      expect(onTick).toHaveBeenCalledTimes(2);
    });

    it('should use default interval of MIN_PROGRESS_UPDATE_INTERVAL_MS', () => {
      const onTick = vi.fn();
      const timer = createProgressTimer(onTick);

      timer.start();

      vi.advanceTimersByTime(MIN_PROGRESS_UPDATE_INTERVAL_MS);

      expect(onTick).toHaveBeenCalledTimes(1);

      timer.stop();
    });
  });

  describe('getToolIcon (REQ_011.3.11)', () => {
    it('should return correct icon for deep_research', () => {
      expect(getToolIcon('deep_research')).toBe('search');
    });

    it('should return correct icon for image_generation', () => {
      expect(getToolIcon('image_generation')).toBe('palette');
    });

    it('should return correct icon for document_generation', () => {
      expect(getToolIcon('document_generation')).toBe('file-text');
    });

    it('should return default loader icon for unknown type', () => {
      expect(getToolIcon('unknown')).toBe('loader');
    });
  });

  describe('getPhaseStatusIcon (REQ_011.3.4-6)', () => {
    it('should return check for completed (REQ_011.3.5)', () => {
      expect(getPhaseStatusIcon('completed')).toBe('check');
    });

    it('should return loader for active (REQ_011.3.4)', () => {
      expect(getPhaseStatusIcon('active')).toBe('loader');
    });

    it('should return x for error', () => {
      expect(getPhaseStatusIcon('error')).toBe('x');
    });

    it('should return circle for pending (REQ_011.3.6)', () => {
      expect(getPhaseStatusIcon('pending')).toBe('circle');
    });
  });
});
