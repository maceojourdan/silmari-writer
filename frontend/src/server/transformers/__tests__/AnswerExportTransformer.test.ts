/**
 * AnswerExportTransformer.test.ts - Step 3: Transform content to selected export format
 *
 * TLA+ Properties:
 * - Reachability: Input Answer + format='markdown' → returns markdown string
 * - TypeInvariant: Output is string for text formats; matches ExportFormat enum
 * - ErrorConsistency: format='pdf' (unsupported) → throws SharedErrors.UNSUPPORTED_EXPORT_FORMAT
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 334-export-or-copy-finalized-answer
 */

import { describe, it, expect } from 'vitest';
import { AnswerExportTransformer } from '../AnswerExportTransformer';
import { SharedError } from '@/server/error_definitions/SharedErrors';
import type { Answer } from '@/server/data_structures/Answer';

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';

const finalizedAnswer: Answer = {
  id: answerId,
  status: 'FINALIZED',
  finalized: true,
  editable: false,
  locked: true,
  content: 'I demonstrated leadership by coordinating a cross-functional team to deliver a critical project under tight deadlines.',
  userId: 'user-abc12345',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:01:00.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('AnswerExportTransformer.transform — Step 3: Transform content to export format', () => {
  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return markdown string when format is markdown', () => {
      const result = AnswerExportTransformer.transform(finalizedAnswer, 'markdown');

      expect(result).toContain('# Answer');
      expect(result).toContain(finalizedAnswer.content);
      expect(typeof result).toBe('string');
    });

    it('should return plain text when format is plain_text', () => {
      const result = AnswerExportTransformer.transform(finalizedAnswer, 'plain_text');

      expect(result).toBe(finalizedAnswer.content);
      expect(typeof result).toBe('string');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a string for markdown format', () => {
      const result = AnswerExportTransformer.transform(finalizedAnswer, 'markdown');
      expect(typeof result).toBe('string');
      expect(result.length).toBeGreaterThan(0);
    });

    it('should return a string for plain_text format', () => {
      const result = AnswerExportTransformer.transform(finalizedAnswer, 'plain_text');
      expect(typeof result).toBe('string');
      expect(result.length).toBeGreaterThan(0);
    });

    it('should preserve answer content in markdown output', () => {
      const result = AnswerExportTransformer.transform(finalizedAnswer, 'markdown');
      // Content should be included verbatim (not truncated or altered)
      expect(result).toContain(finalizedAnswer.content);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw UNSUPPORTED_EXPORT_FORMAT for pdf format', () => {
      try {
        // Force an unsupported format through type assertion
        AnswerExportTransformer.transform(finalizedAnswer, 'pdf' as any);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SharedError);
        expect((e as SharedError).code).toBe('UNSUPPORTED_EXPORT_FORMAT');
      }
    });

    it('should throw UNSUPPORTED_EXPORT_FORMAT for docx format', () => {
      try {
        AnswerExportTransformer.transform(finalizedAnswer, 'docx' as any);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(SharedError);
        expect((e as SharedError).code).toBe('UNSUPPORTED_EXPORT_FORMAT');
      }
    });
  });
});
