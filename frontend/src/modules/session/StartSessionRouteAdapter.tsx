'use client';

import { useRouter } from 'next/navigation';
import StartVoiceSessionModule from '@/modules/session/StartVoiceSessionModule';
import type { AuthUser } from '@/access_controls/RequireAuth';

export interface RouteAuthContext {
  user: AuthUser | null;
  authToken: string | null;
}

function toAuthUser(token: string | null): AuthUser | null {
  if (!token) return null;
  return { id: `user-${token.slice(0, 8)}` };
}

export function resolveRouteAuthContext(): RouteAuthContext {
  if (typeof window === 'undefined') {
    return { user: null, authToken: null };
  }

  const storageCandidate = window.localStorage as unknown as {
    getItem?: (_key: string) => string | null;
  };
  const storedToken =
    typeof storageCandidate?.getItem === 'function'
      ? storageCandidate.getItem('authToken')?.trim() ?? null
      : null;
  const authToken = storedToken && storedToken.length > 0 ? storedToken : 'dev-session-token';

  return {
    user: toAuthUser(authToken),
    authToken,
  };
}

export interface StartSessionRouteAdapterProps {
  authContext?: RouteAuthContext;
}

export function StartSessionRouteAdapter({ authContext }: StartSessionRouteAdapterProps) {
  const router = useRouter();
  const routeAuth = authContext ?? resolveRouteAuthContext();

  return (
    <StartVoiceSessionModule
      user={routeAuth.user}
      authToken={routeAuth.authToken}
      onNavigate={(path) => router.push(path)}
    />
  );
}
