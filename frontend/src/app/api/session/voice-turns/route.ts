import { NextRequest, NextResponse } from 'next/server';
import { z } from 'zod';
import { SessionDAO } from '@/server/data_access_objects/SessionDAO';
import { SessionError } from '@/server/error_definitions/SessionErrors';
import {
  DEFAULT_RECALL_QUESTIONS,
  advanceQuestionProgress,
  initializeQuestionProgress,
  type QuestionProgressState,
} from '@/lib/recallQuestions';

const SessionIdSchema = z.string().uuid();
const DEFAULT_QUESTION_PROGRESS = initializeQuestionProgress(DEFAULT_RECALL_QUESTIONS);

const PostBodySchema = z.discriminatedUnion('action', [
  z.object({
    sessionId: z.string().uuid(),
    action: z.literal('update_working_answer'),
    content: z.string(),
  }),
  z.object({
    sessionId: z.string().uuid(),
    action: z.literal('reset_turns'),
  }),
  z.object({
    sessionId: z.string().uuid(),
    action: z.literal('advance_question'),
  }),
]);

function buildResponse(
  sessionId: string,
  workingAnswer: string,
  turns: string[],
  questionProgress: QuestionProgressState,
) {
  return {
    sessionId,
    workingAnswer,
    turns,
    questionProgress,
  };
}

function normalizeStoryRecordData(storyRecord: Awaited<ReturnType<typeof SessionDAO.findStoryRecordBySessionId>>) {
  return {
    workingAnswer: storyRecord?.content ?? '',
    turns: storyRecord?.responses ?? [],
    questionProgress: storyRecord?.questionProgress ?? DEFAULT_QUESTION_PROGRESS,
  };
}

export async function GET(request: NextRequest) {
  const url = new URL(request.url);
  const sessionIdParam = url.searchParams.get('sessionId');
  const parsedSessionId = SessionIdSchema.safeParse(sessionIdParam);

  if (!parsedSessionId.success) {
    return NextResponse.json(
      { code: 'INVALID_REQUEST', message: 'sessionId must be a valid UUID' },
      { status: 400 },
    );
  }

  try {
    const sessionId = parsedSessionId.data;
    const storyRecord = await SessionDAO.findStoryRecordBySessionId(sessionId);
    const {
      workingAnswer,
      turns,
      questionProgress,
    } = normalizeStoryRecordData(storyRecord);

    return NextResponse.json(
      buildResponse(sessionId, workingAnswer, turns, questionProgress),
      { status: 200 },
    );
  } catch (error) {
    if (error instanceof SessionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[session/voice-turns] Unexpected GET error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}

export async function POST(request: NextRequest) {
  try {
    const rawBody = await request.json();
    const parsedBody = PostBodySchema.safeParse(rawBody);

    if (!parsedBody.success) {
      return NextResponse.json(
        {
          code: 'INVALID_REQUEST',
          message: parsedBody.error.issues.map((issue) => `${issue.path.join('.')}: ${issue.message}`).join('; '),
        },
        { status: 400 },
      );
    }

    const body = parsedBody.data;

    if (body.action === 'update_working_answer') {
      const updated = await SessionDAO.updateStoryRecordWorkingAnswer(body.sessionId, body.content);
      const { turns, questionProgress } = normalizeStoryRecordData(updated);

      return NextResponse.json(
        buildResponse(body.sessionId, body.content, turns, questionProgress),
        { status: 200 },
      );
    }

    if (body.action === 'advance_question') {
      const existingStoryRecord = await SessionDAO.findStoryRecordBySessionId(body.sessionId);
      const {
        workingAnswer,
        turns,
        questionProgress,
      } = normalizeStoryRecordData(existingStoryRecord);
      const advancedQuestionProgress = advanceQuestionProgress(
        DEFAULT_RECALL_QUESTIONS,
        questionProgress,
      );

      const updatedStoryRecord = await SessionDAO.updateStoryRecordQuestionProgress(
        body.sessionId,
        advancedQuestionProgress,
      );
      const resolvedQuestionProgress = updatedStoryRecord?.questionProgress ?? advancedQuestionProgress;

      return NextResponse.json(
        buildResponse(body.sessionId, workingAnswer, turns, resolvedQuestionProgress),
        { status: 200 },
      );
    }

    const resetRecord = await SessionDAO.replaceStoryRecordResponses(body.sessionId, []);
    if (!resetRecord) {
      return NextResponse.json(
        buildResponse(body.sessionId, '', [], DEFAULT_QUESTION_PROGRESS),
        { status: 200 },
      );
    }

    const updated = await SessionDAO.updateStoryRecordWorkingAnswer(body.sessionId, '');
    const { workingAnswer, turns, questionProgress } = normalizeStoryRecordData(updated);

    return NextResponse.json(
      buildResponse(body.sessionId, workingAnswer, turns, questionProgress),
      { status: 200 },
    );
  } catch (error) {
    if (error instanceof SessionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[session/voice-turns] Unexpected POST error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
