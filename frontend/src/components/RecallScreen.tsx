/**
 * RecallScreen - Recall step UI for the writing flow.
 *
 * Resource: ui-w8p2 (component)
 * Path: 331-return-to-recall-from-review
 *
 * Renders the Recall interface with RecordButton and ProgressIndicator.
 * Wraps content in an error boundary for resilient rendering.
 */

'use client';

import { useEffect, useMemo, useRef, useState } from 'react';
import RecordButton from './RecordButton';
import ProgressIndicator from './ProgressIndicator';
import { NEUTRAL_PROGRESS } from '@/data_loaders/RecallProgressLoader';
import type { RecallProgress } from '@/data_loaders/RecallProgressLoader';
import type { Story } from '@/server/data_structures/ConfirmStory';
import { useRealtimeSession } from '@/hooks/useRealtimeSession';
import { VOICE_MODES } from '@/lib/voice-types';
import { submitVoiceResponse } from '@/api_contracts/submitVoiceResponse';
import { extractFinalTranscriptEvent } from '@/lib/realtime-transcript';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface RecallScreenProps {
  progress?: RecallProgress;
  selectedStory?: Story | null;
  sessionId?: string;
  onVoiceResponseSaved?: () => Promise<void> | void;
}

type VoiceSubmitStatus = 'idle' | 'listening' | 'submitting' | 'saved' | 'error';

function buildRecallInstructions(selectedStory: Story | null | undefined): string {
  const storyContext = selectedStory
    ? `Selected story:\nTitle: ${selectedStory.title}\nSummary: ${selectedStory.summary}`
    : 'No story context is available yet.';

  return `You are a recall interview coach. Guide the user to provide concrete details for anchors, actions, and outcomes in a concise way.

${storyContext}

Begin by asking one short question that helps the user start describing this story.`;
}

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function RecallScreen({
  progress = NEUTRAL_PROGRESS,
  selectedStory = null,
  sessionId,
  onVoiceResponseSaved,
}: RecallScreenProps) {
  const { connect, disconnect, sessionState, setOnEvent } = useRealtimeSession();
  const [voiceError, setVoiceError] = useState<string | null>(null);
  const [submitStatus, setSubmitStatus] = useState<VoiceSubmitStatus>('idle');
  const submittedKeysRef = useRef<Set<string>>(new Set());
  const isSubmittingRef = useRef(false);
  const lastSavedTranscriptRef = useRef<string | null>(null);

  const isConnecting = sessionState === 'connecting';
  const isConnected = sessionState === 'connected';

  const recordLabel = useMemo(() => {
    if (isConnecting) return 'Connecting...';
    if (isConnected) return 'Stop';
    return 'Record';
  }, [isConnected, isConnecting]);

  const handleRecord = async () => {
    setVoiceError(null);

    if (isConnected) {
      disconnect();
      setSubmitStatus('idle');
      return;
    }

    submittedKeysRef.current.clear();
    isSubmittingRef.current = false;
    lastSavedTranscriptRef.current = null;
    setSubmitStatus('idle');

    const connected = await connect(VOICE_MODES.VOICE_EDIT, {
      instructions: buildRecallInstructions(selectedStory),
    });

    if (!connected) {
      setVoiceError('Unable to start voice model session. Please try again.');
      setSubmitStatus('error');
    }
  };

  useEffect(() => {
    if (sessionState === 'connected' && !isSubmittingRef.current) {
      setSubmitStatus((current) => (current === 'saved' ? current : 'listening'));
      return;
    }

    if (sessionState !== 'connected' && sessionState !== 'connecting') {
      setSubmitStatus('idle');
    }
  }, [sessionState]);

  useEffect(() => {
    if (!isConnected || !sessionId) {
      setOnEvent(null);
      return;
    }

    setOnEvent((event) => {
      const finalTranscriptEvent = extractFinalTranscriptEvent(event);
      if (!finalTranscriptEvent) {
        return;
      }

      if (submittedKeysRef.current.has(finalTranscriptEvent.dedupeKey)) {
        return;
      }

      if (isSubmittingRef.current) {
        return;
      }

      isSubmittingRef.current = true;
      submittedKeysRef.current.add(finalTranscriptEvent.dedupeKey);
      setSubmitStatus('submitting');

      void (async () => {
        try {
          await submitVoiceResponse({
            sessionId,
            transcript: finalTranscriptEvent.transcript,
          });

          lastSavedTranscriptRef.current = finalTranscriptEvent.transcript;
          setSubmitStatus('saved');
          await onVoiceResponseSaved?.();
        } catch {
          submittedKeysRef.current.delete(finalTranscriptEvent.dedupeKey);
          setSubmitStatus('error');
        } finally {
          isSubmittingRef.current = false;
        }
      })();
    });

    return () => {
      setOnEvent(null);
    };
  }, [isConnected, onVoiceResponseSaved, sessionId, setOnEvent]);

  const submitStatusMessage = useMemo(() => {
    if (submitStatus === 'submitting') return 'Saving your response...';
    if (submitStatus === 'saved') return 'Response saved.';
    if (submitStatus === 'error') return 'Could not save response. Please try speaking again.';
    if (isConnected) return 'Listening for your response...';
    return 'Voice response auto-save is idle.';
  }, [isConnected, submitStatus]);

  return (
    <div data-testid="recall-screen" className="flex flex-col items-center gap-8 p-6">
      <h2 className="text-xl font-semibold">Recall</h2>

      {selectedStory && (
        <section
          data-testid="selected-story"
          className="w-full max-w-2xl rounded-md border border-border bg-card p-4"
        >
          <p className="text-xs uppercase tracking-wide text-muted-foreground">Selected Story</p>
          <h3 className="text-base font-semibold">{selectedStory.title}</h3>
          <p className="mt-1 text-sm text-muted-foreground">{selectedStory.summary}</p>
        </section>
      )}

      <RecordButton
        prominent
        onClick={() => {
          void handleRecord();
        }}
        disabled={isConnecting}
        label={recordLabel}
        ariaLabel={isConnected ? 'Stop recording' : 'Record'}
      />

      <p
        data-testid="voice-model-status"
        className="text-sm text-muted-foreground"
      >
        {isConnected ? 'Voice model connected. Speak now.' : 'Voice model idle.'}
      </p>

      <p
        data-testid="voice-submit-status"
        className="text-sm text-muted-foreground"
      >
        {submitStatusMessage}
      </p>

      {voiceError && (
        <p data-testid="voice-model-error" role="alert" className="text-sm text-red-600">
          {voiceError}
        </p>
      )}

      <ProgressIndicator progress={progress} />
    </div>
  );
}
