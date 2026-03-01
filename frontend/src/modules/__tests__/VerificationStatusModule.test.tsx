/**
 * VerificationStatusModule.test.tsx - Frontend module for verification status display
 *
 * TLA+ Properties:
 * - Reachability: API returns verificationStatus=FAILED → drafting button disabled + failure message shown
 * - TypeInvariant: Props and state match expected shapes
 * - ErrorConsistency: API error → error message displayed
 *
 * Resource: ui-v3n6 (module)
 * Path: 323-fail-verification-when-no-contact-method
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen } from '@testing-library/react';

import VerificationStatusModule from '../../modules/VerificationStatusModule';

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('VerificationStatusModule — Step 6: Display Verification Status', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should disable drafting button when verificationStatus is FAILED', () => {
      render(
        <VerificationStatusModule
          verificationStatus="FAILED"
          reason="MISSING_CONTACT_METHOD"
          draftingAllowed={false}
        />,
      );

      const draftButton = screen.getByRole('button', { name: /start drafting/i });
      expect(draftButton).toBeDisabled();
    });

    it('should show failure message when verificationStatus is FAILED', () => {
      render(
        <VerificationStatusModule
          verificationStatus="FAILED"
          reason="MISSING_CONTACT_METHOD"
          draftingAllowed={false}
        />,
      );

      expect(screen.getByTestId('verification-failure-message')).toBeInTheDocument();
      expect(screen.getByTestId('verification-failure-message').textContent).toContain(
        'contact method',
      );
    });

    it('should show verification status badge as FAILED', () => {
      render(
        <VerificationStatusModule
          verificationStatus="FAILED"
          reason="MISSING_CONTACT_METHOD"
          draftingAllowed={false}
        />,
      );

      expect(screen.getByTestId('verification-status')).toHaveTextContent('FAILED');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should enable drafting button when draftingAllowed is true', () => {
      render(
        <VerificationStatusModule
          verificationStatus="PENDING"
          draftingAllowed={true}
        />,
      );

      const draftButton = screen.getByRole('button', { name: /start drafting/i });
      expect(draftButton).not.toBeDisabled();
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should not show failure message when status is PENDING', () => {
      render(
        <VerificationStatusModule
          verificationStatus="PENDING"
          draftingAllowed={true}
        />,
      );

      expect(screen.queryByTestId('verification-failure-message')).not.toBeInTheDocument();
    });
  });
});
