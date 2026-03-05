'use client';

/**
 * ExportCopyControls - Provides export and copy controls for finalized answers.
 *
 * Resource: ui-w8p2 (component)
 * Path: 334-export-or-copy-finalized-answer
 *
 * On click:
 *   1. If not finalized || not locked → set error from SharedErrors.ANSWER_NOT_FINALIZED
 *   2. If export → emit validated request with answerId + format
 *   3. If copy → emit copy request with answerId
 */

import { useState } from 'react';
import ArtifactCopyButton from '@/components/ArtifactCopyButton';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';
import type { ExportFormat } from '@/server/data_structures/ExportFormat';
import { Button } from '@/components/ui/button';

export interface ExportCopyControlsProps {
  answerId: string;
  finalized: boolean;
  locked: boolean;
  content: string;
  onExport: (request: { answerId: string; format: ExportFormat }) => void;
  onCopy: (request: { answerId: string }) => Promise<void> | void;
  onCopyResult?: (result: { success: boolean; errorMessage?: string }) => void;
}

export default function ExportCopyControls({
  answerId,
  finalized,
  locked,
  content,
  onExport,
  onCopy,
  onCopyResult,
}: ExportCopyControlsProps) {
  const [error, setError] = useState<string | null>(null);

  const validateState = (): boolean => {
    if (!finalized || !locked) {
      const sharedError = SharedErrors.AnswerNotFinalized();
      setError(sharedError.message);
      return false;
    }
    setError(null);
    return true;
  };

  const handleExport = (format: ExportFormat) => {
    if (!validateState()) return;
    onExport({ answerId, format });
  };

  const artifactStatus = finalized && locked ? 'completed' : 'draft';

  return (
    <div className="flex flex-col gap-2">
      <div className="flex gap-2">
        <Button
          size="sm"
          onClick={() => handleExport('markdown')}
          aria-label="Export Markdown"
        >
          Export Markdown
        </Button>

        <Button
          variant="outline"
          size="sm"
          onClick={() => handleExport('plain_text')}
          aria-label="Export Plain Text"
        >
          Export Plain Text
        </Button>

        <ArtifactCopyButton
          artifactType="answer"
          status={artifactStatus}
          content={content}
          sessionId={answerId}
          label="Copy to Clipboard"
          className="flex items-center gap-1 rounded-md border border-input bg-card px-3 py-1.5 text-sm font-medium shadow-xs hover:bg-accent hover:text-accent-foreground"
          copyHandler={async () => {
            if (!validateState()) {
              throw SharedErrors.AnswerNotFinalized();
            }

            await onCopy({ answerId });
          }}
          onCopyResult={onCopyResult}
        />
      </div>

      {error && (
        <div className="text-sm text-destructive" role="alert">
          {error}
        </div>
      )}
    </div>
  );
}
