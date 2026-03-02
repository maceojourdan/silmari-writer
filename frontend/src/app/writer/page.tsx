'use client';

import { StartSessionRouteAdapter } from '@/modules/session/StartSessionRouteAdapter';

export default function WriterPage() {
  return (
    <main className="mx-auto flex w-full max-w-2xl flex-col gap-6 p-6" data-testid="workflow-entry">
      <header className="space-y-1">
        <h1 className="text-2xl font-semibold">Writer Workflow</h1>
        <p className="text-sm text-muted-foreground">
          Start a voice-assisted session and continue through the workflow.
        </p>
      </header>

      <StartSessionRouteAdapter />
    </main>
  );
}

