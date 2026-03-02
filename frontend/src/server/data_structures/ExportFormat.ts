/**
 * ExportFormat - Defines the supported export formats for finalized answers.
 *
 * Resource: cfg-f7s8 (data_type)
 * Path: 334-export-or-copy-finalized-answer
 *
 * Serialization rules:
 * - plain_text: Raw text content with no formatting
 * - markdown: Content formatted as Markdown
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Export Format Enum
// ---------------------------------------------------------------------------

export const ExportFormat = {
  PLAIN_TEXT: 'plain_text',
  MARKDOWN: 'markdown',
} as const;

export type ExportFormat = (typeof ExportFormat)[keyof typeof ExportFormat];

// ---------------------------------------------------------------------------
// Zod Schema
// ---------------------------------------------------------------------------

export const ExportFormatSchema = z.enum(['plain_text', 'markdown']);

// ---------------------------------------------------------------------------
// Action Type: export vs copy
// ---------------------------------------------------------------------------

export const ExportAction = {
  EXPORT: 'export',
  COPY: 'copy',
} as const;

export type ExportAction = (typeof ExportAction)[keyof typeof ExportAction];

export const ExportActionSchema = z.enum(['export', 'copy']);
