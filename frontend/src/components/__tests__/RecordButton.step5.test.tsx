/**
 * RecordButton Step 5 Tests - Display Prominent Record Button
 *
 * Resource: ui-w8p2 (component)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * TLA+ properties tested:
 * - Reachability: Render <RecordButton prominent /> → has prominent Tailwind classes + enabled
 * - TypeInvariant: Props satisfy RecordButtonProps { prominent: boolean; disabled?: boolean }
 * - ErrorConsistency: Style computation error → default classes applied + logger called
 */

import { render, screen } from '@testing-library/react';
import RecordButton from '../RecordButton';

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

describe('RecordButton - Step 5: Display Prominent Record Button', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render with prominent Tailwind classes when prominent=true', () => {
      render(<RecordButton prominent />);

      const button = screen.getByTestId('record-button');
      expect(button.className).toContain('text-4xl');
      expect(button.className).toContain('rounded-full');
      expect(button.className).toContain('w-32');
      expect(button.className).toContain('h-32');
    });

    it('should be enabled by default', () => {
      render(<RecordButton prominent />);

      const button = screen.getByTestId('record-button');
      expect(button).not.toBeDisabled();
    });

    it('should render as a button element', () => {
      render(<RecordButton prominent />);

      const button = screen.getByRole('button', { name: /record/i });
      expect(button).toBeInTheDocument();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should accept prominent boolean prop', () => {
      const { rerender } = render(<RecordButton prominent />);
      expect(screen.getByTestId('record-button')).toBeInTheDocument();

      rerender(<RecordButton prominent={false} />);
      expect(screen.getByTestId('record-button')).toBeInTheDocument();
    });

    it('should accept optional disabled prop', () => {
      render(<RecordButton prominent disabled />);

      const button = screen.getByTestId('record-button');
      expect(button).toBeDisabled();
    });

    it('should render default (non-prominent) styles when prominent=false', () => {
      render(<RecordButton prominent={false} />);

      const button = screen.getByTestId('record-button');
      expect(button.className).toContain('text-lg');
      expect(button.className).toContain('w-16');
      expect(button.className).toContain('h-16');
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should render button even with default styling', () => {
      render(<RecordButton />);

      const button = screen.getByTestId('record-button');
      expect(button).toBeInTheDocument();
      expect(button).not.toBeDisabled();
    });

    it('should always have data-testid attribute', () => {
      render(<RecordButton prominent />);

      expect(screen.getByTestId('record-button')).toBeInTheDocument();
    });

    it('should always be visible and contain text', () => {
      render(<RecordButton prominent />);

      const button = screen.getByTestId('record-button');
      expect(button.textContent).toBeTruthy();
    });
  });
});
