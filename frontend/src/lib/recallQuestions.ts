import { z } from 'zod';

export const RecallQuestionSchema = z.object({
  id: z.string().min(1),
  text: z.string().min(1),
  category: z.string().min(1),
  position: z.number().int().nonnegative(),
});

export type RecallQuestion = z.infer<typeof RecallQuestionSchema>;

export const QuestionProgressStateSchema = z.object({
  currentIndex: z.number().int().nonnegative(),
  total: z.number().int().nonnegative(),
  completed: z.array(z.string()),
  activeQuestionId: z.string().min(1).nullable(),
});

export type QuestionProgressState = z.infer<typeof QuestionProgressStateSchema>;

export const DEFAULT_RECALL_QUESTIONS: readonly RecallQuestion[] = [
  {
    id: 'q-default-1',
    text: 'Tell us about your favourite project you worked on in recent memory and why you loved working on it so much.',
    category: 'default',
    position: 0,
  },
  {
    id: 'q-default-2',
    text: 'What is the biggest change you have seen in your industry in the last year, and how have you changed your approach in response?',
    category: 'default',
    position: 1,
  },
  {
    id: 'q-default-3',
    text: 'What about this role are you most interested in or excited about?',
    category: 'default',
    position: 2,
  },
  {
    id: 'q-default-4',
    text: 'What recent update, industry change, or new industry opportunity are you most excited about right now?',
    category: 'default',
    position: 3,
  },
];

export function initializeQuestionProgress(
  questions: readonly RecallQuestion[],
): QuestionProgressState {
  if (questions.length === 0) {
    throw new Error('Question set cannot be empty');
  }

  return {
    currentIndex: 0,
    total: questions.length,
    completed: [],
    activeQuestionId: questions[0].id,
  };
}

export function getQuestionByProgress(
  questions: readonly RecallQuestion[],
  progress: QuestionProgressState,
): RecallQuestion | null {
  if (progress.currentIndex >= progress.total) {
    return null;
  }

  const byId = progress.activeQuestionId
    ? questions.find((question) => question.id === progress.activeQuestionId) ?? null
    : null;
  if (byId) {
    return byId;
  }

  return questions[progress.currentIndex] ?? null;
}

export function advanceQuestionProgress(
  questions: readonly RecallQuestion[],
  progress: QuestionProgressState,
): QuestionProgressState {
  if (progress.total === 0 || progress.currentIndex >= progress.total) {
    return progress;
  }

  const completedSet = new Set(progress.completed);
  if (progress.activeQuestionId) {
    completedSet.add(progress.activeQuestionId);
  }

  const completed = Array.from(completedSet);
  const isFinalQuestion = progress.currentIndex >= progress.total - 1;

  if (isFinalQuestion) {
    return {
      currentIndex: progress.total,
      total: progress.total,
      completed,
      activeQuestionId: null,
    };
  }

  const nextIndex = progress.currentIndex + 1;
  const fallbackNextQuestion = questions[nextIndex] ?? null;

  return {
    currentIndex: nextIndex,
    total: progress.total,
    completed,
    activeQuestionId: fallbackNextQuestion?.id ?? null,
  };
}
