'use client';

import { useEffect, useState } from 'react';
import { getSession } from '@/api_contracts/getSession';
import { SessionWorkflowShell } from '@/modules/session/SessionWorkflowShell';
import type { SessionView } from '@/server/data_structures/SessionView';

export interface SessionPageProps {
  params: {
    sessionId: string;
  };
}

export default function SessionPage({ params }: SessionPageProps) {
  const [session, setSession] = useState<SessionView | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    let cancelled = false;

    const load = async () => {
      setLoading(true);
      setError(null);

      try {
        const result = await getSession(params.sessionId);
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
  }, [params.sessionId]);

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
      <SessionWorkflowShell session={session} />
    </main>
  );
}

