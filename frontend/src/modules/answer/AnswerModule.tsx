'use client';

/**
 * AnswerModule - Frontend module managing answer state and finalization flow.
 *
 * Resource: ui-v3n6 (module)
 * Path: 333-finalize-answer-locks-editing
 *
 * Manages:
 * - Answer state (finalized, editable)
 * - Finalization flow via FinalizeAnswerButton
 * - Conditional rendering of editing controls
 * - Error display on failure
 */

import { useState } from 'react';
import FinalizeAnswerButton from '@/components/FinalizeAnswerButton';
import type { FinalizeAnswerResponse } from '@/api_contracts/finalizeAnswer';

export interface AnswerState {
  id: string;
  status: string;
  finalized: boolean;
  editable: boolean;
  content: string;
}

export interface AnswerModuleProps {
  answerId: string;
  initialAnswer: AnswerState;
}

export default function AnswerModule({
  answerId,
  initialAnswer,
}: AnswerModuleProps) {
  const [answer, setAnswer] = useState<AnswerState>(initialAnswer);
  const [error, setError] = useState<string | null>(null);

  const handleFinalized = (response: FinalizeAnswerResponse) => {
    // Update local state to reflect finalized status
    setAnswer((prev) => ({
      ...prev,
      finalized: true,
      editable: false,
      status: 'FINALIZED',
    }));
    setError(null);
  };

  return (
    <div className="flex flex-col gap-4">
      {/* Answer Status */}
      <div data-testid="answer-status" className="text-sm font-medium">
        {answer.finalized ? 'Finalized' : answer.status}
      </div>

      {/* Answer Content */}
      <div className="prose">
        {answer.content}
      </div>

      {/* Editing Controls — only when editable */}
      {answer.editable && (
        <div data-testid="editing-controls" className="flex gap-2">
          <button
            className="px-3 py-1 text-sm border rounded-md hover:bg-gray-50"
            aria-label="Edit Answer"
          >
            Edit
          </button>
        </div>
      )}

      {/* Finalize Button — only when not yet finalized */}
      {!answer.finalized && (
        <FinalizeAnswerButton
          answerId={answerId}
          editable={answer.editable}
          onFinalized={handleFinalized}
        />
      )}

      {/* Error Display */}
      {error && (
        <div className="text-sm text-red-600" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
