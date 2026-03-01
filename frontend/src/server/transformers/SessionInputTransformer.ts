/**
 * SessionInputTransformer - Transforms raw text/link input into normalized
 * structured data (ResumeObject, JobObject, QuestionObject).
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 294-parse-and-store-session-input-objects
 */

import type { ResumeObject, JobObject, QuestionObject } from '@/server/data_structures/SessionObjects';

export interface RawSessionInput {
  resume: string;
  jobText?: string;
  jobLink?: string;
  questionText: string;
}

export interface TransformedSessionInput {
  resume: ResumeObject;
  job: JobObject;
  question: QuestionObject;
}

export const SessionInputTransformer = {
  /**
   * Transform raw user inputs into structured, normalized objects.
   * Throws if critical parsing fails (e.g., empty resume after trim).
   */
  transform(raw: RawSessionInput): TransformedSessionInput {
    const resumeContent = raw.resume.trim();
    if (!resumeContent) {
      throw new Error('Resume content is empty after trimming');
    }

    const resume: ResumeObject = {
      content: resumeContent,
      name: 'Uploaded Resume',
      wordCount: resumeContent.split(/\s+/).filter(Boolean).length,
    };

    const jobDescription = raw.jobText?.trim() || '';
    const jobLink = raw.jobLink?.trim() || '';

    if (!jobDescription && !jobLink) {
      throw new Error('Neither job text nor job link provided');
    }

    const sourceType: 'link' | 'text' = jobLink ? 'link' : 'text';
    const sourceValue = jobLink || jobDescription;

    // Extract a rough title from the job description (first line or first N chars)
    const title = SessionInputTransformer.extractJobTitle(
      jobDescription || jobLink,
    );

    const job: JobObject = {
      title,
      description: jobDescription || `Job posting at: ${jobLink}`,
      sourceType,
      sourceValue,
    };

    const questionText = raw.questionText.trim();
    if (!questionText) {
      throw new Error('Question text is empty after trimming');
    }

    const question: QuestionObject = {
      text: questionText,
    };

    return { resume, job, question };
  },

  /**
   * Extract a job title from text. Uses the first line or first 80 characters.
   */
  extractJobTitle(text: string): string {
    const firstLine = text.split('\n')[0].trim();
    if (firstLine.length <= 80) {
      return firstLine;
    }
    return firstLine.substring(0, 77) + '...';
  },
} as const;
