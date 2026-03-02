/**
 * AnswerExportTransformer - Converts structured answer content into the
 * selected export format (markdown or plain text).
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 334-export-or-copy-finalized-answer
 *
 * Supported formats:
 * - plain_text: Raw text content
 * - markdown: Markdown-formatted content
 *
 * Throws SharedErrors.UnsupportedExportFormat for unsupported formats.
 */

import type { Answer } from '@/server/data_structures/Answer';
import type { ExportFormat } from '@/server/data_structures/ExportFormat';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';

export const AnswerExportTransformer = {
  /**
   * Transform answer content to the requested export format.
   *
   * @param answer - The finalized answer entity
   * @param format - The target export format
   * @returns Formatted content string
   * @throws SharedErrors.UnsupportedExportFormat if format is not supported
   */
  transform(answer: Answer, format: ExportFormat): string {
    switch (format) {
      case 'plain_text':
        return answer.content;

      case 'markdown':
        return `# Answer\n\n${answer.content}`;

      default: {
        // This should be unreachable due to Zod validation,
        // but provides defense-in-depth.
        const _exhaustive: never = format;
        throw SharedErrors.UnsupportedExportFormat(
          `Export format '${_exhaustive}' is not supported`,
        );
      }
    }
  },
} as const;
