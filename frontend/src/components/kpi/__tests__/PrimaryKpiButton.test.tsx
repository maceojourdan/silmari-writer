/**
 * PrimaryKpiButton.test.tsx - Step 1 test for path 339-record-primary-kpi-analytics-event.
 *
 * Reachability: simulate valid click → assert recordPrimaryKpi() called with structured payload
 * TypeInvariant: assert payload matches RecordPrimaryKpiRequest TypeScript type
 * ErrorConsistency: simulate invalid input → assert verifier returns error and API contract not called
 */

import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { describe, it, expect, vi, beforeEach } from 'vitest';
import PrimaryKpiButton from '../PrimaryKpiButton';

vi.mock('../../../api_contracts/recordPrimaryKpi', () => ({
  recordPrimaryKpi: vi.fn(),
}));

import { recordPrimaryKpi } from '../../../api_contracts/recordPrimaryKpi';

const mockedRecordPrimaryKpi = vi.mocked(recordPrimaryKpi);

const defaultProps = {
  userId: 'user-001',
  actionType: 'purchase',
  metadata: { amount: 99.99 },
  onRecorded: vi.fn(),
};

describe('PrimaryKpiButton', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockedRecordPrimaryKpi.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      status: 'recorded',
      analyticsEmitted: true,
    });
  });

  // Reachability: render button → click → assert recordPrimaryKpi called with { userId, actionType, metadata }
  it('calls recordPrimaryKpi with correct payload on valid click', async () => {
    const user = userEvent.setup();
    render(<PrimaryKpiButton {...defaultProps} />);

    const button = screen.getByTestId('kpi-button');
    await user.click(button);

    await waitFor(() => {
      expect(mockedRecordPrimaryKpi).toHaveBeenCalledTimes(1);
      expect(mockedRecordPrimaryKpi).toHaveBeenCalledWith({
        userId: 'user-001',
        actionType: 'purchase',
        metadata: { amount: 99.99 },
      });
    });
  });

  // Reachability: render → click → on success → assert onRecorded callback called
  it('invokes onRecorded callback on successful API response', async () => {
    const user = userEvent.setup();
    render(<PrimaryKpiButton {...defaultProps} />);

    const button = screen.getByTestId('kpi-button');
    await user.click(button);

    await waitFor(() => {
      expect(defaultProps.onRecorded).toHaveBeenCalledTimes(1);
      expect(defaultProps.onRecorded).toHaveBeenCalledWith({
        id: '550e8400-e29b-41d4-a716-446655440000',
        status: 'recorded',
        analyticsEmitted: true,
      });
    });
  });

  // TypeInvariant: inspect call args — payload has userId (string), actionType (string), metadata (object)
  it('sends payload with correct types: userId string, actionType string, metadata object', async () => {
    const user = userEvent.setup();
    render(<PrimaryKpiButton {...defaultProps} />);

    const button = screen.getByTestId('kpi-button');
    await user.click(button);

    await waitFor(() => {
      expect(mockedRecordPrimaryKpi).toHaveBeenCalledTimes(1);
    });

    const callArgs = mockedRecordPrimaryKpi.mock.calls[0][0];
    expect(typeof callArgs.userId).toBe('string');
    expect(typeof callArgs.actionType).toBe('string');
    expect(typeof callArgs.metadata).toBe('object');
    expect(callArgs.metadata).not.toBeNull();
  });

  // ErrorConsistency: render with empty userId → click → assert error displayed, recordPrimaryKpi NOT called
  it('displays error and does not call API when userId is empty', async () => {
    const user = userEvent.setup();
    render(<PrimaryKpiButton {...defaultProps} userId="" />);

    const button = screen.getByTestId('kpi-button');
    await user.click(button);

    await waitFor(() => {
      const errorEl = screen.getByTestId('kpi-error');
      expect(errorEl).toBeInTheDocument();
      expect(errorEl.textContent).toContain('User ID is required');
    });

    expect(mockedRecordPrimaryKpi).not.toHaveBeenCalled();
  });

  // ErrorConsistency: render with empty actionType → click → assert error displayed, recordPrimaryKpi NOT called
  it('displays error and does not call API when actionType is empty', async () => {
    const user = userEvent.setup();
    render(<PrimaryKpiButton {...defaultProps} actionType="" />);

    const button = screen.getByTestId('kpi-button');
    await user.click(button);

    await waitFor(() => {
      const errorEl = screen.getByTestId('kpi-error');
      expect(errorEl).toBeInTheDocument();
      expect(errorEl.textContent).toContain('Action type is required');
    });

    expect(mockedRecordPrimaryKpi).not.toHaveBeenCalled();
  });

  // ErrorConsistency: mock recordPrimaryKpi to throw → assert error message shown
  it('displays error message when recordPrimaryKpi throws', async () => {
    mockedRecordPrimaryKpi.mockRejectedValueOnce(new Error('Network failure'));

    const user = userEvent.setup();
    render(<PrimaryKpiButton {...defaultProps} />);

    const button = screen.getByTestId('kpi-button');
    await user.click(button);

    await waitFor(() => {
      const errorEl = screen.getByTestId('kpi-error');
      expect(errorEl).toBeInTheDocument();
      expect(errorEl.textContent).toContain('Network failure');
    });
  });
});
