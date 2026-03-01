/**
 * BehavioralQuestionForm Tests
 *
 * Resource: ui-w8p2 (component)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: render → simulate typing → assert module state updated
 * - TypeInvariant: state matches BehavioralQuestionDraft interface
 * - ErrorConsistency: malformed input → verifier flags field → error shown, submit disabled
 */

import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import BehavioralQuestionForm from '../BehavioralQuestionForm';
import { evaluateBehavioralQuestion } from '@/api_contracts/evaluateBehavioralQuestion';

vi.mock('@/api_contracts/evaluateBehavioralQuestion', () => ({
  evaluateBehavioralQuestion: vi.fn(),
}));

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

const mockEvaluate = vi.mocked(evaluateBehavioralQuestion);

describe('BehavioralQuestionForm', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: render → simulate typing → module state updated', () => {
    it('should render the form with all required fields', () => {
      render(<BehavioralQuestionForm sessionId="session-001" />);

      expect(screen.getByLabelText(/objective/i)).toBeInTheDocument();
      expect(screen.getByLabelText(/outcome/i)).toBeInTheDocument();
      expect(screen.getByLabelText(/role clarity/i)).toBeInTheDocument();
      expect(screen.getByRole('button', { name: /submit/i })).toBeInTheDocument();
    });

    it('should update state when user types in objective field', async () => {
      render(<BehavioralQuestionForm sessionId="session-001" />);

      const objectiveInput = screen.getByLabelText(/objective/i);
      await userEvent.type(objectiveInput, 'Led a team');

      expect(objectiveInput).toHaveValue('Led a team');
    });

    it('should call API and show VERIFY badge on successful submission', async () => {
      mockEvaluate.mockResolvedValueOnce({
        eligible: true,
        questionId: 'bq-001',
        status: 'VERIFY',
        updatedAt: '2026-02-28T12:00:00.000Z',
      });

      render(<BehavioralQuestionForm sessionId="session-001" />);

      // Fill in all fields
      await userEvent.type(screen.getByLabelText(/objective/i), 'Led a team to migrate systems');
      await userEvent.type(screen.getByLabelText(/outcome/i), 'Zero downtime migration');
      await userEvent.type(screen.getByLabelText(/role clarity/i), 'Technical lead');

      // Add 3 actions
      const addActionBtn = screen.getByRole('button', { name: /add action/i });
      await userEvent.click(addActionBtn);
      await userEvent.click(addActionBtn);
      await userEvent.click(addActionBtn);

      const actionInputs = screen.getAllByPlaceholderText(/action/i);
      await userEvent.type(actionInputs[0], 'Gathered requirements');
      await userEvent.type(actionInputs[1], 'Created migration plan');
      await userEvent.type(actionInputs[2], 'Coordinated teams');

      // Add 1 obstacle
      const addObstacleBtn = screen.getByRole('button', { name: /add obstacle/i });
      await userEvent.click(addObstacleBtn);

      const obstacleInputs = screen.getAllByPlaceholderText(/obstacle/i);
      await userEvent.type(obstacleInputs[0], 'Undocumented dependencies');

      // Submit
      const submitBtn = screen.getByRole('button', { name: /submit/i });
      await userEvent.click(submitBtn);

      await waitFor(() => {
        expect(screen.getByTestId('status-badge')).toHaveTextContent('VERIFY');
      });
    });
  });

  describe('TypeInvariant: form maintains correct data shape', () => {
    it('should send structured payload matching BehavioralQuestionDraft to API', async () => {
      mockEvaluate.mockResolvedValueOnce({
        eligible: true,
        questionId: 'bq-001',
        status: 'VERIFY',
        updatedAt: '2026-02-28T12:00:00.000Z',
      });

      render(<BehavioralQuestionForm sessionId="session-001" />);

      // Fill in all fields
      await userEvent.type(screen.getByLabelText(/objective/i), 'Led a team');
      await userEvent.type(screen.getByLabelText(/outcome/i), 'Success');
      await userEvent.type(screen.getByLabelText(/role clarity/i), 'Lead');

      // Add actions
      for (let i = 0; i < 3; i++) {
        await userEvent.click(screen.getByRole('button', { name: /add action/i }));
      }
      const actionInputs = screen.getAllByPlaceholderText(/action/i);
      await userEvent.type(actionInputs[0], 'Action 1');
      await userEvent.type(actionInputs[1], 'Action 2');
      await userEvent.type(actionInputs[2], 'Action 3');

      // Add obstacle
      await userEvent.click(screen.getByRole('button', { name: /add obstacle/i }));
      const obstacleInputs = screen.getAllByPlaceholderText(/obstacle/i);
      await userEvent.type(obstacleInputs[0], 'Obstacle 1');

      // Submit
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(mockEvaluate).toHaveBeenCalledTimes(1);
        const calledWith = mockEvaluate.mock.calls[0][0];
        expect(calledWith).toHaveProperty('sessionId', 'session-001');
        expect(calledWith).toHaveProperty('objective');
        expect(calledWith).toHaveProperty('actions');
        expect(calledWith).toHaveProperty('obstacles');
        expect(calledWith).toHaveProperty('outcome');
        expect(calledWith).toHaveProperty('roleClarity');
        expect(Array.isArray(calledWith.actions)).toBe(true);
        expect(Array.isArray(calledWith.obstacles)).toBe(true);
      });
    });
  });

  describe('ErrorConsistency: validation errors prevent submission', () => {
    it('should show validation errors when submitting with empty fields', async () => {
      render(<BehavioralQuestionForm sessionId="session-001" />);

      // Submit without filling anything
      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByText(/objective is required/i)).toBeInTheDocument();
      });

      expect(mockEvaluate).not.toHaveBeenCalled();
    });

    it('should display API error when backend call fails', async () => {
      mockEvaluate.mockRejectedValueOnce(new Error('Server error'));

      render(<BehavioralQuestionForm sessionId="session-001" />);

      // Fill in all required fields
      await userEvent.type(screen.getByLabelText(/objective/i), 'Led a team');
      await userEvent.type(screen.getByLabelText(/outcome/i), 'Success');
      await userEvent.type(screen.getByLabelText(/role clarity/i), 'Lead');

      for (let i = 0; i < 3; i++) {
        await userEvent.click(screen.getByRole('button', { name: /add action/i }));
      }
      const actionInputs = screen.getAllByPlaceholderText(/action/i);
      await userEvent.type(actionInputs[0], 'A1');
      await userEvent.type(actionInputs[1], 'A2');
      await userEvent.type(actionInputs[2], 'A3');

      await userEvent.click(screen.getByRole('button', { name: /add obstacle/i }));
      const obstacleInputs = screen.getAllByPlaceholderText(/obstacle/i);
      await userEvent.type(obstacleInputs[0], 'O1');

      await userEvent.click(screen.getByRole('button', { name: /submit/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });
    });

    it('should show DRAFT status badge when not yet submitted', () => {
      render(<BehavioralQuestionForm sessionId="session-001" />);

      expect(screen.getByTestId('status-badge')).toHaveTextContent('DRAFT');
    });
  });
});
