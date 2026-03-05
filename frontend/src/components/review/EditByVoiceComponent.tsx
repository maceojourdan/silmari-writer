'use client';

/**
 * EditByVoiceComponent - Captures voice instruction for editing content from review screen.
 *
 * Resource: ui-w8p2 (component)
 * Path: 330-edit-content-by-voice-from-review-screen
 *
 * On click:
 *   1. Activate voice capture mode (text input fallback for testing)
 *   2. Collect spoken instruction and convert to text
 *   3. Emit structured EditByVoicePayload { contentId, instructionText }
 *   4. On failure, display SharedErrors.VOICE_CAPTURE_FAILED with retry (max 3)
 */

import { useState } from 'react';
import { Button } from '@/components/ui/button';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface EditByVoicePayload {
  contentId: string;
  instructionText: string;
}

export interface EditByVoiceComponentProps {
  contentId: string;
  onVoiceInstruction?: (payload: EditByVoicePayload) => void;
  onError?: (error: Error) => void;
}

const MAX_RETRIES = 3;

// ---------------------------------------------------------------------------
// Component
// ---------------------------------------------------------------------------

export default function EditByVoiceComponent({
  contentId,
  onVoiceInstruction,
  onError,
}: EditByVoiceComponentProps) {
  const [isCapturing, setIsCapturing] = useState(false);
  const [instructionText, setInstructionText] = useState('');
  const [retryCount, setRetryCount] = useState(0);
  const [error, setError] = useState<string | null>(null);
  const [isBlocked, setIsBlocked] = useState(false);

  const handleStartCapture = () => {
    if (isBlocked) return;
    setIsCapturing(true);
    setError(null);
  };

  const handleSubmit = () => {
    // Validate instruction text
    if (!instructionText.trim()) {
      const newRetryCount = retryCount + 1;
      setRetryCount(newRetryCount);

      const errorMessage =
        newRetryCount >= MAX_RETRIES
          ? 'Voice capture failed: Maximum retries exceeded'
          : `Voice capture or transcription failed (attempt ${newRetryCount} of ${MAX_RETRIES})`;

      setError(errorMessage);

      if (newRetryCount >= MAX_RETRIES) {
        setIsBlocked(true);
        setIsCapturing(false);
      }

      const captureError = new Error(errorMessage);
      (captureError as any).code = 'VOICE_CAPTURE_FAILED';
      onError?.(captureError);
      return;
    }

    // Emit structured payload
    const payload: EditByVoicePayload = {
      contentId,
      instructionText: instructionText.trim(),
    };

    onVoiceInstruction?.(payload);

    // Reset state
    setInstructionText('');
    setIsCapturing(false);
    setError(null);
  };

  return (
    <div className="flex flex-col gap-2" data-testid="edit-by-voice">
      <Button
        onClick={handleStartCapture}
        disabled={isBlocked}
        aria-label="Edit by Voice"
      >
        Edit by Voice
      </Button>

      {isCapturing && (
        <div className="flex flex-col gap-2" data-testid="voice-capture-form">
          <input
            type="text"
            className="rounded-md border border-input bg-background px-3 py-2 text-sm"
            placeholder="Enter voice instruction..."
            value={instructionText}
            onChange={(e) => setInstructionText(e.target.value)}
          />
          <Button
            onClick={handleSubmit}
            aria-label="Submit"
          >
            Submit
          </Button>
        </div>
      )}

      {error && (
        <div className="text-sm text-destructive" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
