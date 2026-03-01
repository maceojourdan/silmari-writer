/**
 * RecallAccessControl - Verifies user authorization for the RECALL state interface.
 *
 * Resource: ui-x1r9 (access_control)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * Validates:
 * - Application state is RECALL
 * - User has the view:recall permission
 * Logs denial via frontendLogger (cfg-r3d7) with UI_RECALL_ACCESS_DENIED.
 */

import { frontendLogger } from '@/logging/index';
import { UiErrors } from '@/server/error_definitions/UiErrors';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface RecallUser {
  id: string;
  role: string;
  permissions: string[];
}

export interface RecallAccessInput {
  state: string;
  user: RecallUser;
}

export interface AccessResult {
  authorized: boolean;
  redirect?: string;
}

// ---------------------------------------------------------------------------
// Implementation
// ---------------------------------------------------------------------------

const REQUIRED_PERMISSION = 'view:recall';
const DENY_REDIRECT = '/dashboard';

/**
 * Validates whether the user is permitted to view the RECALL interface.
 *
 * - State must be 'RECALL'
 * - User must have 'view:recall' permission
 *
 * On denial: logs UI_RECALL_ACCESS_DENIED and returns redirect to /dashboard.
 */
export function validateRecallAccess(input: RecallAccessInput): AccessResult {
  if (input.state !== 'RECALL') {
    frontendLogger.error(
      'UI_RECALL_ACCESS_DENIED',
      UiErrors.RecallAccessDenied(`State is ${input.state}, not RECALL`),
      { module: 'RecallAccessControl', action: 'validateState', userId: input.user.id },
    );
    return { authorized: false, redirect: DENY_REDIRECT };
  }

  if (!input.user.permissions.includes(REQUIRED_PERMISSION)) {
    frontendLogger.error(
      'UI_RECALL_ACCESS_DENIED',
      UiErrors.RecallAccessDenied(`User ${input.user.id} lacks ${REQUIRED_PERMISSION} permission`),
      { module: 'RecallAccessControl', action: 'validatePermission', userId: input.user.id },
    );
    return { authorized: false, redirect: DENY_REDIRECT };
  }

  return { authorized: true };
}
