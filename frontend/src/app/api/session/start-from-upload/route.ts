import { NextRequest, NextResponse } from 'next/server';
import {
  StartSessionFromUploadRequestSchema,
  StartSessionFromUploadResponseSchema,
} from '@/api_contracts/startSessionFromUpload';
import { InitializeSessionService } from '@/server/services/InitializeSessionService';
import { AuthAndValidationFilter } from '@/server/filters/AuthAndValidationFilter';
import { QuestionResolutionService } from '@/server/services/QuestionResolutionService';
import { StoryError, StoryErrors } from '@/server/error_definitions/StoryErrors';
import { SessionError } from '@/server/error_definitions/SessionErrors';

const RESUME_EXTENSIONS = new Set(['docx', 'doc', 'pdf', 'txt', 'md']);
const SCREENSHOT_EXTENSIONS = new Set(['png', 'jpg', 'jpeg', 'webp']);

function extensionFromFilename(filename: string): string {
  const parts = filename.toLowerCase().split('.');
  return parts.length > 1 ? parts.at(-1) ?? '' : '';
}

function classifyFile(filename: string): 'resume' | 'screenshot' | null {
  const ext = extensionFromFilename(filename);
  if (RESUME_EXTENSIONS.has(ext)) {
    return 'resume';
  }
  if (SCREENSHOT_EXTENSIONS.has(ext)) {
    return 'screenshot';
  }
  return null;
}

function wordCountFromText(text: string): number {
  return text.split(/\s+/).filter(Boolean).length;
}

export async function POST(request: NextRequest) {
  try {
    const auth = AuthAndValidationFilter.authenticate(request.headers.get('authorization'));

    const body = await request.json().catch(() => {
      throw StoryErrors.VALIDATION_ERROR('Invalid JSON payload');
    });

    const parsed = StartSessionFromUploadRequestSchema.safeParse(body);
    if (!parsed.success) {
      throw StoryErrors.VALIDATION_ERROR(
        `Invalid request payload: ${parsed.error.issues.map((issue) => issue.message).join(', ')}`,
      );
    }

    const classifiedFiles = parsed.data.files.map((file) => ({
      ...file,
      kind: classifyFile(file.filename),
    }));

    if (classifiedFiles.some((file) => file.kind === null)) {
      throw StoryErrors.VALIDATION_ERROR('Unsupported file type. Allowed: resume documents or screenshots.');
    }

    const resumeFiles = classifiedFiles.filter((file) => file.kind === 'resume');
    const screenshotFiles = classifiedFiles.filter((file) => file.kind === 'screenshot');

    const resumeContext = resumeFiles.length > 0
      ? `Uploaded resume files: ${resumeFiles.map((file) => file.filename).join(', ')}.`
      : 'No resume file uploaded; using screenshot-only context.';

    const screenshotContext = screenshotFiles.length > 0
      ? `Uploaded screenshot files: ${screenshotFiles.map((file) => file.url).join(', ')}.`
      : 'No screenshot files were uploaded.';

    const initialized = await InitializeSessionService.createSession({
      resume: {
        content: resumeContext,
        name: resumeFiles[0]?.filename ?? 'Uploaded Context',
        wordCount: wordCountFromText(resumeContext),
      },
      job: {
        title: screenshotFiles.length > 0 ? 'Imported role from uploaded screenshot' : 'Imported role from uploaded files',
        description: `${resumeContext} ${screenshotContext}`,
        sourceType: 'text',
        sourceValue: screenshotFiles[0]?.url ?? 'uploaded-files',
      },
      question: {
        text: 'Tell us about your favourite project you worked on in recent memory and why you loved working on it so much.',
      },
      userId: auth.userId,
    });

    const questions = QuestionResolutionService.resolveQuestionsForInputMode('file_upload');
    const questionProgress = QuestionResolutionService.initializeQuestionProgress(questions);

    const responsePayload = {
      sessionId: initialized.id,
      state: initialized.state,
      inputMode: 'file_upload' as const,
      resumeId: null,
      questions,
      questionProgress,
    };

    const responseValidation = StartSessionFromUploadResponseSchema.safeParse(responsePayload);
    if (!responseValidation.success) {
      throw new Error('Failed to construct valid file-upload session response');
    }

    return NextResponse.json(responseValidation.data, { status: 200 });
  } catch (error) {
    if (error instanceof StoryError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    if (error instanceof SessionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'Unexpected internal error' },
      { status: 500 },
    );
  }
}
