'use client';

import { use, useCallback, useEffect, useState } from 'react';
import { getSession } from '@/api_contracts/getSession';
import { SessionWorkflowShell } from '@/modules/session/SessionWorkflowShell';
import type { SessionView } from '@/server/data_structures/SessionView';

interface SessionRouteParams {
  sessionId: string;
}

export interface SessionPageProps {
  params: Promise<SessionRouteParams>;
}

export default function SessionPage({ params }: SessionPageProps) {
  const paramsInput = params as Promise<SessionRouteParams> | SessionRouteParams;
  const resolvedParams =
    typeof (paramsInput as Promise<SessionRouteParams>)?.then === 'function'
      ? use(paramsInput as Promise<SessionRouteParams>)
      : (paramsInput as SessionRouteParams);
  const sessionId = resolvedParams?.sessionId;

  const [session, setSession] = useState<SessionView | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  const refreshSession = useCallback(async () => {
    if (!sessionId || sessionId.trim() === '') {
      return;
    }

    try {
      const nextSession = await getSession(sessionId);
      setSession(nextSession);
      setError(null);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'Failed to refresh session.';
      setError(message);
    }
  }, [sessionId]);

  useEffect(() => {
    let cancelled = false;

    if (!sessionId || sessionId.trim() === '') {
      setSession(null);
      setError('Session ID must be a valid UUID');
      setLoading(false);
      return () => {
        cancelled = true;
      };
    }

    const load = async () => {
      setLoading(true);
      setError(null);

      try {
        const result = await getSession(sessionId);
        if (!cancelled) {
          setSession(result);
        }
      } catch (err) {
        if (!cancelled) {
          const message =
            err instanceof Error ? err.message : 'Failed to load session.';
          setError(message);
          setSession(null);
        }
      } finally {
        if (!cancelled) {
          setLoading(false);
        }
      }
    };

    void load();

    return () => {
      cancelled = true;
    };
  }, [sessionId]);

  if (loading) {
    return (
      <main data-testid="session-page-loading" className="p-6">
        <p className="text-sm text-muted-foreground">Loading session...</p>
      </main>
    );
  }

  if (error || !session) {
    return (
      <main data-testid="session-page-error" className="p-6" role="alert">
        <p className="text-sm text-red-600">{error ?? 'Session not found.'}</p>
      </main>
    );
  }

  return (
    <main data-testid="session-page" className="mx-auto w-full max-w-4xl p-6">
      <SessionWorkflowShell
        session={session}
        onVoiceResponseSaved={refreshSession}
      />
    </main>
  );
}
