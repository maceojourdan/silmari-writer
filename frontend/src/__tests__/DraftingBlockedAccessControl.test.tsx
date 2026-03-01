/**
 * DraftingBlockedAccessControl.test.tsx - Tests for the drafting access control guard.
 *
 * Step 5 of Path 322: Enforce drafting access restriction in UI.
 *
 * TLA+ properties:
 * - Reachability: With blocked status → drafting component renders blocked message.
 * - TypeInvariant: Props typed with CaseStateResponse.
 * - ErrorConsistency: If guard missing config → render fallback error boundary.
 *
 * Resource: ui-y5t3 (access_control)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { describe, it, expect, vi } from 'vitest';
import { render, screen } from '@testing-library/react';
import React from 'react';

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Imports (after mocks)
// ---------------------------------------------------------------------------

import { DraftingBlockedAccessControl } from '@/access_controls/DraftingBlockedAccessControl';
import { frontendLogger } from '@/logging/index';
import type { CaseStateResponse } from '@/server/data_structures/Case';

const mockLogger = vi.mocked(frontendLogger);

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

const blockedState: CaseStateResponse = {
  caseId: 'case-001',
  drafting_status: 'blocked_due_to_unverified_claims',
  blocked: true,
  message: 'Drafting is blocked due to disputed claims that are not verified.',
};

const allowedState: CaseStateResponse = {
  caseId: 'case-001',
  drafting_status: 'drafting_allowed',
  blocked: false,
};

function DraftingContent() {
  return <div>Drafting Interface</div>;
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('DraftingBlockedAccessControl — Step 5', () => {
  // =========================================================================
  // Reachability
  // =========================================================================

  describe('Reachability', () => {
    it('should render blocked message when drafting status is blocked', () => {
      render(
        <DraftingBlockedAccessControl caseState={blockedState}>
          <DraftingContent />
        </DraftingBlockedAccessControl>,
      );

      expect(screen.getByTestId('drafting-blocked')).toBeTruthy();
      expect(screen.getByText('Drafting Blocked')).toBeTruthy();
      expect(screen.queryByText('Drafting Interface')).toBeNull();
    });

    it('should render children when drafting status is allowed', () => {
      render(
        <DraftingBlockedAccessControl caseState={allowedState}>
          <DraftingContent />
        </DraftingBlockedAccessControl>,
      );

      expect(screen.getByText('Drafting Interface')).toBeTruthy();
    });

    it('should display the blocked message from case state', () => {
      render(
        <DraftingBlockedAccessControl caseState={blockedState}>
          <DraftingContent />
        </DraftingBlockedAccessControl>,
      );

      expect(
        screen.getByText('Drafting is blocked due to disputed claims that are not verified.'),
      ).toBeTruthy();
    });
  });

  // =========================================================================
  // TypeInvariant
  // =========================================================================

  describe('TypeInvariant', () => {
    it('should accept CaseStateResponse typed props', () => {
      const { container } = render(
        <DraftingBlockedAccessControl caseState={allowedState}>
          <DraftingContent />
        </DraftingBlockedAccessControl>,
      );

      // If it renders without error, type checking passed
      expect(container).toBeTruthy();
    });
  });

  // =========================================================================
  // ErrorConsistency
  // =========================================================================

  describe('ErrorConsistency', () => {
    it('should render fallback error state when caseState is null', () => {
      render(
        <DraftingBlockedAccessControl caseState={null}>
          <DraftingContent />
        </DraftingBlockedAccessControl>,
      );

      expect(screen.getByText(/unable to determine drafting status/i)).toBeTruthy();
      expect(screen.queryByText('Drafting Interface')).toBeNull();
    });

    it('should log warning when caseState is null', () => {
      render(
        <DraftingBlockedAccessControl caseState={null}>
          <DraftingContent />
        </DraftingBlockedAccessControl>,
      );

      expect(mockLogger.warn).toHaveBeenCalledWith(
        expect.stringContaining('missing'),
        expect.objectContaining({
          module: 'DraftingBlockedAccessControl',
        }),
      );
    });
  });
});
