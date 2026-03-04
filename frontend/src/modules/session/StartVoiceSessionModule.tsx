/**
 * StartVoiceSessionModule - Frontend module for initiating a voice-assisted
 * answer session. Wraps in RequireAuth and calls URL-ingestion API contract.
 *
 * Resource: ui-v3n6 (module)
 * Path: 306-initiate-voice-assisted-answer-session
 *
 * Flow:
 *   1. RequireAuth ensures user is authenticated (redirects to /login if not)
 *   2. User submits a job URL
 *   3. Calls startSessionFromUrl() API contract
 *   4. On success → navigates to /session/[id] with initialized state
 *   5. On failure → displays error message
 */

'use client';

import { useState, useCallback, createContext, useContext } from 'react';
import { CheckCircle2, Loader2, Mic, TriangleAlert } from 'lucide-react';
import { RequireAuth, type AuthUser } from '@/access_controls/RequireAuth';
import { startSessionFromUrl } from '@/api_contracts/startSessionFromUrl';
import { startSessionFromUpload } from '@/api_contracts/startSessionFromUpload';
import { startSessionDefaultQuestions } from '@/api_contracts/startSessionDefaultQuestions';
import { Badge } from '@/components/ui/badge';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardDescription } from '@/components/ui/card';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type VoiceSessionState = 'idle' | 'loading' | 'success' | 'error';
export type InputMode = 'url' | 'file_upload' | 'default_questions';

export interface VoiceSessionContext {
  sessionId: string | null;
  state: 'initialized' | null;
}

export interface StartVoiceSessionModuleProps {
  user: AuthUser | null;
  authToken: string | null;
  // eslint-disable-next-line no-unused-vars
  onNavigate(path: string): void;
}

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

const SessionContext = createContext<VoiceSessionContext>({
  sessionId: null,
  state: null,
});

export function useVoiceSession(): VoiceSessionContext {
  return useContext(SessionContext);
}

function isStartSessionAlreadyActiveError(error: unknown): boolean {
  if (!error || typeof error !== 'object') {
    return false;
  }

  const candidate = error as { code?: unknown; statusCode?: unknown; name?: unknown };
  return (
    candidate.code === 'SESSION_ALREADY_ACTIVE'
    || candidate.statusCode === 409
    || candidate.name === 'StartSessionAlreadyActiveError'
  );
}

function mapStartSessionErrorToUiMessage(error: unknown): string {
  if (isStartSessionAlreadyActiveError(error)) {
    return 'You already have an active session. Please finalize or end it before starting a new one.';
  }

  if (error instanceof Error) {
    return error.message;
  }

  return 'An unexpected error occurred';
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function StartVoiceSessionModule({
  user,
  authToken,
  onNavigate,
}: StartVoiceSessionModuleProps) {
  const [inputMode, setInputMode] = useState<InputMode>('url');
  const [sourceUrl, setSourceUrl] = useState('');
  const [files, setFiles] = useState<File[]>([]);
  const [uiState, setUIState] = useState<VoiceSessionState>('idle');
  const [error, setError] = useState<string | null>(null);
  const [sessionContext, setSessionContext] = useState<VoiceSessionContext>({
    sessionId: null,
    state: null,
  });

  const handleUnauthenticated = useCallback(() => {
    onNavigate('/login');
  }, [onNavigate]);

  const handleStartSession = async () => {
    if (!authToken) {
      onNavigate('/login');
      return;
    }

    try {
      setUIState('loading');
      setError(null);

      let result: { sessionId: string; state: 'initialized' };

      if (inputMode === 'url') {
        const trimmedUrl = sourceUrl.trim();
        if (trimmedUrl.length === 0) {
          setError('Paste a job URL to continue.');
          setUIState('error');
          return;
        }

        result = await startSessionFromUrl(authToken, trimmedUrl);
      } else if (inputMode === 'file_upload') {
        if (files.length === 0) {
          setError('Upload at least one resume or screenshot file to continue.');
          setUIState('error');
          return;
        }

        result = await startSessionFromUpload(authToken, files);
      } else {
        result = await startSessionDefaultQuestions(authToken);
      }

      const newContext: VoiceSessionContext = {
        sessionId: result.sessionId,
        state: result.state,
      };

      setSessionContext(newContext);
      setUIState('success');
      onNavigate(`/session/${result.sessionId}`);
    } catch (err) {
      const message = mapStartSessionErrorToUiMessage(err);
      frontendLogger.error(
        'VOICE_SESSION_START_FAILED',
        err instanceof Error ? err : new Error(String(err)),
        { module: 'StartVoiceSessionModule', action: 'handleStartSession' },
      );
      setError(message);
      setUIState('error');
    }
  };

  return (
    <RequireAuth user={user} onUnauthenticated={handleUnauthenticated}>
      <SessionContext.Provider value={sessionContext}>
        <Card data-testid="start-voice-session-module" className="border-border/70 bg-card/80">
          <CardContent className="space-y-4 p-5">
            <CardDescription className="flex items-center gap-2 text-sm">
              <Mic className="h-4 w-4 text-primary" />
              {inputMode === 'url'
                ? 'Paste a job URL to initialize session context before continuing the voice workflow.'
                : inputMode === 'file_upload'
                  ? 'Upload resume or job screenshot to initialize context.'
                  : 'Use default recall questions without URL or file input.'}
            </CardDescription>

            <div className="flex flex-wrap gap-2" role="group" aria-label="Start input mode">
              <Button
                type="button"
                variant={inputMode === 'url' ? 'default' : 'outline'}
                size="sm"
                data-testid="input-mode-url"
                aria-pressed={inputMode === 'url'}
                onClick={() => {
                  setInputMode('url');
                  setError(null);
                  setUIState('idle');
                }}
              >
                URL
              </Button>
              <Button
                type="button"
                variant={inputMode === 'file_upload' ? 'default' : 'outline'}
                size="sm"
                data-testid="input-mode-file_upload"
                aria-pressed={inputMode === 'file_upload'}
                onClick={() => {
                  setInputMode('file_upload');
                  setError(null);
                  setUIState('idle');
                }}
              >
                File Upload
              </Button>
              <Button
                type="button"
                variant={inputMode === 'default_questions' ? 'default' : 'outline'}
                size="sm"
                data-testid="input-mode-default_questions"
                aria-pressed={inputMode === 'default_questions'}
                onClick={() => {
                  setInputMode('default_questions');
                  setError(null);
                  setUIState('idle');
                }}
              >
                Default Questions
              </Button>
            </div>

            {inputMode === 'url' && (
              <div className="space-y-2">
                <label htmlFor="source-url" className="text-sm font-medium">
                  Job Posting URL
                </label>
                <input
                  id="source-url"
                  type="url"
                  inputMode="url"
                  placeholder="https://example.greenhouse.io/job/123"
                  className="w-full rounded-md border border-input bg-background px-3 py-2 text-sm shadow-sm transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring disabled:cursor-not-allowed disabled:opacity-50"
                  value={sourceUrl}
                  onChange={(event) => setSourceUrl(event.target.value)}
                />
                <p className="text-xs text-muted-foreground">
                  Same ingestion pipeline used for URL paste and channel ingestion (email/SMS).
                </p>
              </div>
            )}

            {inputMode === 'file_upload' && (
              <div
                data-testid="input-mode-panel-file_upload"
                className="space-y-2 rounded-md border border-border/60 bg-muted/30 p-3 text-sm text-muted-foreground"
              >
                <label htmlFor="file-upload-input" className="text-sm font-medium text-foreground">
                  Upload resume or screenshot
                </label>
                <input
                  id="file-upload-input"
                  data-testid="file-upload-input"
                  type="file"
                  multiple
                  accept=".docx,.doc,.pdf,.txt,.md,.png,.jpg,.jpeg,.webp"
                  className="w-full rounded-md border border-input bg-background px-3 py-2 text-sm text-foreground"
                  onChange={(event) => {
                    setFiles(Array.from(event.target.files ?? []));
                    setError(null);
                    setUIState('idle');
                  }}
                />
                <p className="text-xs text-muted-foreground">
                  Accepted: docx, doc, pdf, txt, md, png, jpg, jpeg, webp.
                </p>
              </div>
            )}

            {inputMode === 'default_questions' && (
              <div
                data-testid="input-mode-panel-default_questions"
                className="rounded-md border border-border/60 bg-muted/30 p-3 text-sm text-muted-foreground"
              >
                Use default recall questions without URL or file input.
              </div>
            )}

            <Button
              onClick={handleStartSession}
              aria-label="Start Voice-Assisted Session"
              className="w-full sm:w-auto"
              disabled={uiState === 'loading'}
            >
              Start Voice-Assisted Session
            </Button>

            {uiState === 'loading' && (
              <div data-testid="loading-indicator" className="inline-flex items-center gap-2 rounded-md border bg-muted/50 px-3 py-2">
                <Loader2 className="h-4 w-4 animate-spin text-primary" />
                <span className="text-sm">
                  {inputMode === 'url'
                    ? 'Initializing from URL...'
                    : inputMode === 'file_upload'
                      ? 'Initializing from uploaded files...'
                      : 'Initializing with default questions...'}
                </span>
              </div>
            )}

            {uiState === 'success' && (
              <div data-testid="session-init" className="inline-flex items-center gap-2 text-green-700">
                <CheckCircle2 className="h-4 w-4" />
                <Badge variant="outline" className="border-green-600/30 bg-green-500/10 text-green-700">
                  Session initialized: {sessionContext.state}
                </Badge>
              </div>
            )}

            {uiState === 'error' && (
              <div
                data-testid="session-error"
                role="alert"
                className="flex items-start gap-2 rounded-md border border-destructive/30 bg-destructive/10 px-3 py-2 text-destructive"
              >
                <TriangleAlert className="mt-0.5 h-4 w-4 shrink-0" />
                <span>{error || 'An unexpected error occurred'}</span>
              </div>
            )}
          </CardContent>
        </Card>
      </SessionContext.Provider>
    </RequireAuth>
  );
}
