'use client';

/**
 * ReviewScreen - Captures user Approve action for reviewed content.
 *
 * Resource: ui-w8p2 (component)
 * Paths:
 *   - 329-approve-reviewed-content-and-advance-workflow
 *   - 331-return-to-recall-from-review
 *   - 332-voice-edit-no-input-error-on-review-screen
 *
 * On click:
 *   1. Run reviewApprovalVerifier.validateSelection(contentId)
 *   2. If valid → call approveContent API contract
 *   3. If invalid → set local validation error state
 *
 * Return to Recall (Path 331):
 *   - Button with data-testid="return-to-recall"
 *   - Click → emit NavigationIntent { targetStep: 'RECALL' } via onNavigate
 *   - Guards against unmounted state via useEffect cleanup flag
 *
 * Edit by Voice (Path 332):
 *   - Button triggers voice capture session initialization
 *   - On empty/unintelligible input → VoiceInputErrors displayed, screen preserved
 *   - VoiceSession { status, attempts } tracks capture state
 */

import { useState, useEffect, useRef } from 'react';
import { reviewApprovalVerifier } from '@/verifiers/reviewApprovalVerifier';
import { approveContent } from '@/api_contracts/approveContent';
import type { ApproveContentResponse } from '@/api_contracts/approveContent';
import type { NavigationIntent } from '@/modules/writingFlow';
import { frontendLogger } from '@/logging/index';
import { VoiceInputErrors } from '@/server/error_definitions/VoiceErrors';
import type { VoiceErrorDef } from '@/server/error_definitions/VoiceErrors';
import { validateVoiceInput } from '@/verifiers/VoiceInputVerifier';

// ---------------------------------------------------------------------------
// Voice Session Types (Path 332)
// ---------------------------------------------------------------------------

export type VoiceSession = {
  status: 'capturing' | 'idle' | 'error';
  attempts: number;
};

export interface ReviewScreenProps {
  selectedContentId?: string;
  onApproved?: (response: ApproveContentResponse) => void;
  onError?: (error: Error) => void;
  onNavigate?: (intent: NavigationIntent) => void;
  /** Path 332: Called when voice session state changes */
  onVoiceSessionChange?: (session: VoiceSession) => void;
  /**
   * Path 332: Show inline voice capture controls.
   * Set to false when EditByVoiceComponent is rendered separately (e.g., in ReviewWorkflowModule).
   * Defaults to true for standalone use.
   */
  showVoiceCapture?: boolean;
  /** Test-only: force voice initialization to fail */
  __testForceVoiceInitError?: boolean;
}

export default function ReviewScreen({
  selectedContentId,
  onApproved,
  onError,
  onNavigate,
  onVoiceSessionChange,
  showVoiceCapture = true,
  __testForceVoiceInitError,
}: ReviewScreenProps) {
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isApproved, setIsApproved] = useState(false);

  // Path 332: Voice session state
  const [voiceSession, setVoiceSession] = useState<VoiceSession | null>(null);
  const [voiceError, setVoiceError] = useState<VoiceErrorDef | null>(null);
  const [voiceTranscript, setVoiceTranscript] = useState('');

  // Track mounted state for Return to Recall guard (Path 331)
  const isMountedRef = useRef(true);

  useEffect(() => {
    isMountedRef.current = true;
    return () => {
      isMountedRef.current = false;
    };
  }, []);

  const handleApprove = async () => {
    setError(null);

    // Step 1: Validate selection via verifier
    const validation = reviewApprovalVerifier.validateSelection(selectedContentId);

    if (!validation.success) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 2: Call API contract
    setIsSubmitting(true);
    try {
      const result = await approveContent(validation.data.contentId);
      setIsApproved(true);
      onApproved?.(result);
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
      onError?.(err instanceof Error ? err : new Error(message));
    } finally {
      setIsSubmitting(false);
    }
  };

  // Path 331: Handle Return to Recall navigation
  const handleReturnToRecall = () => {
    if (!isMountedRef.current) {
      frontendLogger.error(
        'ReturnToRecall: component unmounted',
        new Error('Cannot navigate: ReviewScreen is unmounted'),
        { component: 'ReviewScreen', action: 'handleReturnToRecall' },
      );
      return;
    }

    onNavigate?.({ targetStep: 'RECALL' });
  };

  // Path 332: Initialize voice capture session
  // Preserves attempt count from previous session if it exists
  const initializeVoiceSession = (currentAttempts: number): VoiceSession => {
    if (__testForceVoiceInitError) {
      throw new Error('Voice initialization forced failure');
    }
    return { status: 'capturing', attempts: currentAttempts };
  };

  const handleEditByVoice = () => {
    setVoiceError(null);
    try {
      const currentAttempts = voiceSession?.attempts ?? 0;
      const session = initializeVoiceSession(currentAttempts);
      setVoiceSession(session);
      onVoiceSessionChange?.(session);
    } catch (err) {
      frontendLogger.error(
        'Voice session initialization failed',
        err instanceof Error ? err : new Error('Unknown error'),
        { component: 'ReviewScreen', action: 'handleEditByVoice' },
      );
      setVoiceError(VoiceInputErrors.VOICE_INIT_FAILED);
      const errorSession: VoiceSession = {
        status: 'error',
        attempts: voiceSession?.attempts ?? 0,
      };
      setVoiceSession(errorSession);
    }
  };

  // Path 332: Handle voice transcript submission
  const handleVoiceSubmit = () => {
    if (!voiceSession) return;

    const result = validateVoiceInput(voiceTranscript, 0);

    if (!result.valid) {
      const newAttempts = voiceSession.attempts + 1;
      const updatedSession: VoiceSession = {
        status: 'idle',
        attempts: newAttempts,
      };
      setVoiceSession(updatedSession);
      onVoiceSessionChange?.(updatedSession);
      setVoiceError(result.error);
      setVoiceTranscript('');
      return;
    }

    // Valid input - reset voice mode
    setVoiceSession(null);
    setVoiceError(null);
    setVoiceTranscript('');
  };

  // Path 332: Render error with fallback protection
  const renderVoiceError = () => {
    if (!voiceError) return null;
    try {
      return (
        <div className="text-sm text-red-600" role="alert" data-testid="voice-error">
          {voiceError.message}
        </div>
      );
    } catch {
      return (
        <div className="text-sm text-red-600" role="alert" data-testid="voice-error-fallback">
          {VoiceInputErrors.GENERIC_VOICE_ERROR.message}
        </div>
      );
    }
  };

  if (isApproved) {
    return (
      <div className="flex items-center gap-2 text-green-600" data-testid="approve-success">
        <span>Content approved successfully.</span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2" data-testid="review-screen">
      <button
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors disabled:opacity-50 disabled:cursor-not-allowed"
        onClick={handleApprove}
        disabled={isSubmitting}
        aria-label={isSubmitting ? 'Approving...' : 'Approve'}
      >
        {isSubmitting ? 'Approving...' : 'Approve'}
      </button>

      {/* Path 331: Return to Recall button */}
      <button
        data-testid="return-to-recall"
        className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md border border-gray-300 text-gray-700 hover:bg-gray-50 transition-colors"
        onClick={handleReturnToRecall}
        aria-label="Return to Recall"
      >
        Return to Recall
      </button>

      {/* Path 332: Edit by Voice controls (shown when showVoiceCapture=true) */}
      {showVoiceCapture && (
        <>
          <button
            data-testid="edit-by-voice-btn"
            className="flex items-center gap-1 px-4 py-2 text-sm font-medium rounded-md bg-blue-600 text-white hover:bg-blue-700 transition-colors"
            onClick={handleEditByVoice}
            aria-label="Edit by Voice"
          >
            Edit by Voice
          </button>

          {/* Path 332: Voice capture form */}
          {voiceSession?.status === 'capturing' && (
            <div data-testid="voice-capture-active" className="flex flex-col gap-2">
              <input
                type="text"
                className="px-3 py-2 border rounded-md text-sm"
                placeholder="Enter voice instruction..."
                value={voiceTranscript}
                onChange={(e) => setVoiceTranscript(e.target.value)}
                data-testid="voice-transcript-input"
              />
              <button
                className="px-4 py-2 text-sm font-medium rounded-md bg-green-600 text-white hover:bg-green-700 transition-colors"
                onClick={handleVoiceSubmit}
                aria-label="Submit Voice Input"
                data-testid="voice-submit-btn"
              >
                Submit Voice Input
              </button>
            </div>
          )}

          {/* Path 332: Voice error display */}
          {renderVoiceError()}
        </>
      )}

      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
