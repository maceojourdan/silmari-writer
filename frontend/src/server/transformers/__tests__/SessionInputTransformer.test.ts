/**
 * Tests for SessionInputTransformer
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 294-parse-and-store-session-input-objects
 *
 * TLA+ properties tested:
 * - Reachability: transform(validRaw) → { resume, job, question }
 * - TypeInvariant: output objects have correct field types
 * - ErrorConsistency: empty/invalid inputs throw descriptive errors
 */

import { describe, it, expect } from 'vitest';
import { SessionInputTransformer } from '../SessionInputTransformer';

describe('SessionInputTransformer', () => {
  describe('Reachability: valid raw input produces transformed objects', () => {
    it('should transform text-based job input', () => {
      const result = SessionInputTransformer.transform({
        resume: 'Experienced engineer with 10 years...',
        jobText: 'Senior Developer at Acme Corp',
        questionText: 'Tell me about a challenge.',
      });

      expect(result.resume.content).toBe('Experienced engineer with 10 years...');
      expect(result.resume.name).toBe('Uploaded Resume');
      expect(result.resume.wordCount).toBe(5);
      expect(result.job.sourceType).toBe('text');
      expect(result.job.title).toBe('Senior Developer at Acme Corp');
      expect(result.question.text).toBe('Tell me about a challenge.');
    });

    it('should transform link-based job input', () => {
      const result = SessionInputTransformer.transform({
        resume: 'My resume content',
        jobLink: 'https://example.com/job/123',
        questionText: 'What is your greatest strength?',
      });

      expect(result.job.sourceType).toBe('link');
      expect(result.job.sourceValue).toBe('https://example.com/job/123');
      expect(result.job.description).toContain('https://example.com/job/123');
    });

    it('should prefer link when both jobText and jobLink are provided', () => {
      const result = SessionInputTransformer.transform({
        resume: 'My resume content',
        jobText: 'Some job description',
        jobLink: 'https://example.com/job/456',
        questionText: 'Describe a project.',
      });

      expect(result.job.sourceType).toBe('link');
      expect(result.job.sourceValue).toBe('https://example.com/job/456');
    });
  });

  describe('TypeInvariant: output objects have correct fields', () => {
    it('should produce resume with wordCount as number', () => {
      const result = SessionInputTransformer.transform({
        resume: 'One two three four five',
        jobText: 'Job description',
        questionText: 'Question text',
      });

      expect(typeof result.resume.wordCount).toBe('number');
      expect(result.resume.wordCount).toBe(5);
    });

    it('should truncate long job titles to 80 characters', () => {
      const longJobText = 'A'.repeat(100);
      const result = SessionInputTransformer.transform({
        resume: 'My resume',
        jobText: longJobText,
        questionText: 'Question?',
      });

      expect(result.job.title.length).toBeLessThanOrEqual(80);
    });
  });

  describe('ErrorConsistency: invalid inputs throw', () => {
    it('should throw when resume is empty after trimming', () => {
      expect(() =>
        SessionInputTransformer.transform({
          resume: '   ',
          jobText: 'Job description',
          questionText: 'Question?',
        }),
      ).toThrow('Resume content is empty');
    });

    it('should throw when neither jobText nor jobLink is provided', () => {
      expect(() =>
        SessionInputTransformer.transform({
          resume: 'My resume',
          questionText: 'Question?',
        }),
      ).toThrow('Neither job text nor job link');
    });

    it('should throw when questionText is empty after trimming', () => {
      expect(() =>
        SessionInputTransformer.transform({
          resume: 'My resume',
          jobText: 'Job description',
          questionText: '   ',
        }),
      ).toThrow('Question text is empty');
    });
  });
});
