/**
 * RequireAuth - Access control component that ensures only authenticated
 * users can access wrapped content. Redirects to login if unauthenticated.
 *
 * Resource: ui-x1r9 (access_control)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Usage:
 *   <RequireAuth user={user} onUnauthenticated={() => router.push('/login')}>
 *     <ProtectedContent />
 *   </RequireAuth>
 */

'use client';

import { useEffect } from 'react';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface AuthUser {
  id: string;
}

export interface RequireAuthProps {
  user: AuthUser | null | undefined;
  onUnauthenticated: () => void;
  children: React.ReactNode;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export function RequireAuth({ user, onUnauthenticated, children }: RequireAuthProps) {
  useEffect(() => {
    if (!user) {
      frontendLogger.warn('RequireAuth: unauthenticated access attempt', {
        module: 'RequireAuth',
        action: 'redirect',
      });
      onUnauthenticated();
    }
  }, [user, onUnauthenticated]);

  if (!user) {
    return null;
  }

  return <>{children}</>;
}
