import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import {
  StartSessionAlreadyActiveError,
  StartSessionFromUrlErrorSchema,
} from '@/api_contracts/startSessionFromUrl';

const RecallQuestionSchema = z.object({
  id: z.string().min(1),
  text: z.string().min(1),
  category: z.string().min(1),
  position: z.number().int().nonnegative(),
});

const QuestionProgressSchema = z.object({
  currentIndex: z.number().int().nonnegative(),
  total: z.number().int().nonnegative(),
  completed: z.array(z.string()),
  activeQuestionId: z.string().min(1).nullable(),
});

export const StartSessionDefaultQuestionsResponseSchema = z.object({
  sessionId: z.string().uuid(),
  state: z.literal('initialized'),
  inputMode: z.literal('default_questions'),
  questions: z.array(RecallQuestionSchema).min(1),
  questionProgress: QuestionProgressSchema,
});

export type StartSessionDefaultQuestionsResponse = z.infer<typeof StartSessionDefaultQuestionsResponseSchema>;

export async function startSessionDefaultQuestions(
  authToken: string,
): Promise<StartSessionDefaultQuestionsResponse> {
  try {
    const response = await fetch('/api/session/start-default', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${authToken}`,
      },
      body: JSON.stringify({}),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      const parsedError = StartSessionFromUrlErrorSchema.safeParse(errorBody);

      if (
        response.status === 409
        && parsedError.success
        && parsedError.data.code === 'SESSION_ALREADY_ACTIVE'
      ) {
        throw new StartSessionAlreadyActiveError(parsedError.data.message);
      }

      throw new Error(
        parsedError.success
          ? parsedError.data.message
          : `Default-question session initialization failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = StartSessionDefaultQuestionsResponseSchema.safeParse(data);
    if (!parsed.success) {
      throw new Error(
        `Invalid response from session/start-default: ${parsed.error.issues.map((issue) => issue.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Default-question session initialization request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'startSessionDefaultQuestions', module: 'api_contracts' },
    );
    throw error;
  }
}
