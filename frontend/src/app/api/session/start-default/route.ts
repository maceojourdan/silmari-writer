import { NextRequest, NextResponse } from 'next/server';
import {
  StartSessionDefaultQuestionsResponseSchema,
} from '@/api_contracts/startSessionDefaultQuestions';
import { InitializeSessionService } from '@/server/services/InitializeSessionService';
import { AuthAndValidationFilter } from '@/server/filters/AuthAndValidationFilter';
import { QuestionResolutionService } from '@/server/services/QuestionResolutionService';
import { StoryError, StoryErrors } from '@/server/error_definitions/StoryErrors';
import { SessionError } from '@/server/error_definitions/SessionErrors';

function wordCountFromText(text: string): number {
  return text.split(/\s+/).filter(Boolean).length;
}

export async function POST(request: NextRequest) {
  try {
    const auth = AuthAndValidationFilter.authenticate(request.headers.get('authorization'));

    await request.json().catch(() => {
      throw StoryErrors.VALIDATION_ERROR('Invalid JSON payload');
    });

    const questions = QuestionResolutionService.resolveQuestionsForInputMode('default_questions');
    const questionProgress = QuestionResolutionService.initializeQuestionProgress(questions);
    const firstQuestion = questions[0]?.text
      ?? 'Tell us about your favourite project you worked on in recent memory and why you loved working on it so much.';

    const resumeContext = 'No resume or upload source provided.';
    const jobContext = 'Default recall mode initialized without external source context.';

    const initialized = await InitializeSessionService.createSession({
      resume: {
        content: resumeContext,
        name: 'Default Recall Context',
        wordCount: wordCountFromText(resumeContext),
      },
      job: {
        title: 'General role context',
        description: jobContext,
        sourceType: 'text',
        sourceValue: 'default',
      },
      question: {
        text: firstQuestion,
      },
      userId: auth.userId,
    });

    const responsePayload = {
      sessionId: initialized.id,
      state: initialized.state,
      inputMode: 'default_questions' as const,
      questions,
      questionProgress,
    };

    const responseValidation = StartSessionDefaultQuestionsResponseSchema.safeParse(responsePayload);
    if (!responseValidation.success) {
      throw new Error('Failed to construct valid default-question session response');
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
