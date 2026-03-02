'use client';

/**
 * AnswerEditor - Editable textarea for answer content with save functionality.
 * Prevents editing of locked (finalized) answers by handling LOCKED_ANSWER_MODIFICATION_FORBIDDEN errors.
 *
 * Resource: ui-w8p2 (component)
 * Path: 337-prevent-edit-of-locked-answer
 *
 * On Save:
 *   1. Clear error
 *   2. Validate via validateAnswerUpdate(answerId, content)
 *   3. If invalid → display validation errors, do NOT call API
 *   4. If valid → call updateAnswer({ id, content })
 *   5. On success → invoke onSaved callback
 *   6. On LOCKED_ANSWER_MODIFICATION_FORBIDDEN → display locked message, restore original content
 *   7. On any other error → display generic error, restore original content
 */

import { useState } from 'react';
import { updateAnswer, UpdateAnswerApiError } from '@/api_contracts/updateAnswer';
import type { UpdateAnswerResponse } from '@/api_contracts/updateAnswer';
import { validateAnswerUpdate } from '@/verifiers/answerUpdateVerifier';

export interface AnswerEditorProps {
  answerId: string;
  initialContent: string;
  onSaved?: (response: UpdateAnswerResponse) => void;
}

export default function AnswerEditor({
  answerId,
  initialContent,
  onSaved,
}: AnswerEditorProps) {
  const [content, setContent] = useState(initialContent);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleSave = async () => {
    // Step 1: Clear error
    setError(null);

    // Step 2: Validate
    const validation = validateAnswerUpdate(answerId, content);

    // Step 3: If invalid, display errors and return
    if (!validation.valid) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 4: Call API
    setIsLoading(true);
    try {
      const result = await updateAnswer({ id: answerId, content });

      // Step 5: On success, invoke callback
      onSaved?.(result);
    } catch (err) {
      // Step 6 & 7: Handle errors and restore original content
      if (
        err instanceof UpdateAnswerApiError &&
        err.code === 'LOCKED_ANSWER_MODIFICATION_FORBIDDEN'
      ) {
        setError('This answer has been finalized and cannot be modified.');
      } else {
        setError('An unexpected error occurred. Please try again.');
      }
      // Restore original content on any error
      setContent(initialContent);
    } finally {
      // Step 8: Reset loading state
      setIsLoading(false);
    }
  };

  return (
    <div className="flex flex-col gap-2">
      <textarea
        className="w-full min-h-[120px] p-3 border border-gray-300 rounded-md resize-y focus:outline-none focus:ring-2 focus:ring-primary"
        value={content}
        onChange={(e) => setContent(e.target.value)}
        data-testid="answer-content-input"
        aria-label="Answer content"
        disabled={isLoading}
      />

      <button
        className={`px-4 py-2 text-sm font-medium rounded-md transition-colors ${
          isLoading
            ? 'opacity-50 cursor-not-allowed bg-primary text-primary-foreground'
            : 'bg-primary text-primary-foreground hover:bg-primary/90'
        }`}
        onClick={handleSave}
        disabled={isLoading}
        aria-label="Save"
      >
        {isLoading ? 'Saving...' : 'Save'}
      </button>

      {error && (
        <div
          className="text-sm text-red-600"
          role="alert"
          data-testid="answer-editor-error"
        >
          {error}
        </div>
      )}
    </div>
  );
}
