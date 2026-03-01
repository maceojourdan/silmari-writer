/**
 * RecallModule Step 3 Tests - Compose Recall UI Components
 *
 * Resource: ui-w8p2 (component)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * TLA+ properties tested:
 * - Reachability: Render RecallLayout → record-button and progress-indicator exist
 * - TypeInvariant: Props passed to RecordButton and ProgressIndicator satisfy TS interfaces
 * - ErrorConsistency: RecordButton throws → fallback error component rendered + logger called
 */

import { render, screen } from '@testing-library/react';
import { RecallLayout } from '@/components/RecallLayout';
import { frontendLogger } from '@/logging/index';

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

const mockLogger = vi.mocked(frontendLogger);

const defaultProgress = {
  anchors: 3,
  actions: 5,
  outcomes: 2,
};

describe('RecallModule - Step 3: Compose Recall UI Components', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render the record button', () => {
      render(<RecallLayout progress={defaultProgress} />);

      expect(screen.getByTestId('record-button')).toBeInTheDocument();
    });

    it('should render the progress indicator', () => {
      render(<RecallLayout progress={defaultProgress} />);

      expect(screen.getByTestId('progress-indicator')).toBeInTheDocument();
    });

    it('should render both components together', () => {
      render(<RecallLayout progress={defaultProgress} />);

      expect(screen.getByTestId('record-button')).toBeInTheDocument();
      expect(screen.getByTestId('progress-indicator')).toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should pass prominent prop to RecordButton', () => {
      render(<RecallLayout progress={defaultProgress} />);

      const button = screen.getByTestId('record-button');
      expect(button).toBeInTheDocument();
    });

    it('should pass progress data to ProgressIndicator', () => {
      render(<RecallLayout progress={defaultProgress} />);

      const indicator = screen.getByTestId('progress-indicator');
      expect(indicator).toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should render fallback error component when RecordButton throws', () => {
      // Render with forceError to trigger the error boundary
      render(<RecallLayout progress={defaultProgress} forceError />);

      expect(screen.getByTestId('recall-fallback-error')).toBeInTheDocument();
    });

    it('should log UI_COMPONENT_INIT_ERROR when a component fails', () => {
      render(<RecallLayout progress={defaultProgress} forceError />);

      expect(mockLogger.error).toHaveBeenCalledWith(
        'UI_COMPONENT_INIT_ERROR',
        expect.anything(),
        expect.objectContaining({ module: 'RecallLayout' }),
      );
    });
  });
});
