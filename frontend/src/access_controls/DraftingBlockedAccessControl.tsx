/**
 * DraftingBlockedAccessControl - Guard component that prevents access
 * to the drafting interface when claims are disputed and unverified.
 *
 * Resource: ui-y5t3 (access_control)
 * Path: 322-handle-disputed-claims-and-block-drafting
 *
 * Usage:
 *   <DraftingBlockedAccessControl caseState={caseState}>
 *     <DraftingInterface />
 *   </DraftingBlockedAccessControl>
 */

'use client';

import type { CaseStateResponse } from '@/server/data_structures/Case';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface DraftingBlockedAccessControlProps {
  caseState: CaseStateResponse | null;
  children: React.ReactNode;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export function DraftingBlockedAccessControl({
  caseState,
  children,
}: DraftingBlockedAccessControlProps) {
  // Missing config / null state → render fallback error boundary
  if (!caseState) {
    frontendLogger.warn(
      'DraftingBlockedAccessControl: case state config missing',
      {
        module: 'DraftingBlockedAccessControl',
        action: 'render',
      },
    );

    return (
      <div role="alert" data-testid="drafting-error">
        <p>Unable to determine drafting status. Please try again later.</p>
      </div>
    );
  }

  // Blocked state → render blocked message
  if (caseState.blocked) {
    return (
      <div role="alert" data-testid="drafting-blocked">
        <h2>Drafting Blocked</h2>
        <p>
          {caseState.message ||
            'Drafting is blocked due to unverified claims. Please resolve disputed claims before continuing.'}
        </p>
      </div>
    );
  }

  // Allowed → render children
  return <>{children}</>;
}
