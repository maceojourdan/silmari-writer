/**
 * Step 5 Tests: Render timeout state in drafting UI
 *
 * Resource: ui-w8p2 (component), ui-v3n6 (module)
 * Path: 324-verification-timeout-keeps-claims-unverified-and-drafting-on-hold
 *
 * TLA+ Properties tested:
 * - Reachability: Unverified + On Hold + Verification Timed Out visible
 * - TypeInvariant: props typed via ClaimStatusResponse
 * - ErrorConsistency: error UI rendered; missing status → "Status Unavailable"
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';
import React from 'react';

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

vi.mock('@/data_loaders/useClaimStatus', () => ({
  useClaimStatus: vi.fn(),
}));

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { useClaimStatus } from '@/data_loaders/useClaimStatus';
import { frontendLogger } from '@/logging/index';
import { DraftingModule } from '@/modules/drafting/DraftingModule';
import { ClaimStatusPanel } from '@/components/ClaimStatusPanel';

const mockUseClaimStatus = vi.mocked(useClaimStatus);
const mockFrontendLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('ClaimStatusPanel', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -----------------------------------------------------------------------
  // Reachability
  // -----------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render Unverified and On Hold and Verification Timed Out', () => {
      mockUseClaimStatus.mockReturnValue({
        data: {
          claimStatus: 'UNVERIFIED',
          draftingStatus: 'On Hold',
          timedOut: true,
        },
        loading: false,
        error: null,
      });

      render(<DraftingModule claimId="claim-001" />);

      expect(screen.getByText('Unverified')).toBeDefined();
      expect(screen.getByText('On Hold')).toBeDefined();
      expect(screen.getByText('Verification Timed Out')).toBeDefined();
    });

    it('should render claim status panel via DraftingModule', () => {
      mockUseClaimStatus.mockReturnValue({
        data: {
          claimStatus: 'UNVERIFIED',
          draftingStatus: 'On Hold',
          timedOut: true,
        },
        loading: false,
        error: null,
      });

      render(<DraftingModule claimId="claim-001" />);

      expect(screen.getByTestId('drafting-module')).toBeDefined();
      expect(screen.getByTestId('claim-status-panel')).toBeDefined();
    });

    it('should not show timeout badge when not timed out', () => {
      mockUseClaimStatus.mockReturnValue({
        data: {
          claimStatus: 'CONFIRMED',
          draftingStatus: 'Ready',
          timedOut: false,
        },
        loading: false,
        error: null,
      });

      render(<DraftingModule claimId="claim-001" />);

      expect(screen.queryByTestId('timeout-badge')).toBeNull();
    });
  });

  // -----------------------------------------------------------------------
  // TypeInvariant
  // -----------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should render correctly with typed ClaimStatusResponse props', () => {
      render(
        <ClaimStatusPanel
          data={{
            claimStatus: 'UNVERIFIED',
            draftingStatus: 'On Hold',
            timedOut: true,
          }}
          loading={false}
          error={null}
        />,
      );

      expect(screen.getByTestId('claim-status-panel')).toBeDefined();
    });
  });

  // -----------------------------------------------------------------------
  // ErrorConsistency
  // -----------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should render error UI when hook returns an error', () => {
      mockUseClaimStatus.mockReturnValue({
        data: null,
        loading: false,
        error: new Error('Network failure'),
      });

      render(<DraftingModule claimId="claim-001" />);

      expect(screen.getByTestId('claim-status-error')).toBeDefined();
      expect(screen.getByText('Error loading claim status')).toBeDefined();
    });

    it('should render Status Unavailable when status values are missing', () => {
      mockUseClaimStatus.mockReturnValue({
        data: { claimStatus: '', draftingStatus: '' },
        loading: false,
        error: null,
      });

      render(<DraftingModule claimId="claim-001" />);

      expect(screen.getByText('Status Unavailable')).toBeDefined();
    });

    it('should render Status Unavailable when data is null', () => {
      mockUseClaimStatus.mockReturnValue({
        data: null,
        loading: false,
        error: null,
      });

      render(<DraftingModule claimId="claim-001" />);

      expect(screen.getByText('Status Unavailable')).toBeDefined();
    });

    it('should show loading state', () => {
      mockUseClaimStatus.mockReturnValue({
        data: null,
        loading: true,
        error: null,
      });

      render(<DraftingModule claimId="claim-001" />);

      expect(screen.getByTestId('claim-status-loading')).toBeDefined();
    });
  });
});
