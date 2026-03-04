import {
  DEFAULT_RECALL_QUESTIONS,
  initializeQuestionProgress,
  type QuestionProgressState,
  type RecallQuestion,
} from '@/lib/recallQuestions';

export { DEFAULT_RECALL_QUESTIONS } from '@/lib/recallQuestions';
export type { QuestionProgressState, RecallQuestion } from '@/lib/recallQuestions';

export const QuestionResolutionService = {
  resolveQuestionsForInputMode(_mode: 'url' | 'file_upload' | 'default_questions'): RecallQuestion[] {
    return [...DEFAULT_RECALL_QUESTIONS];
  },

  initializeQuestionProgress(questions: RecallQuestion[]): QuestionProgressState {
    return initializeQuestionProgress(questions);
  },
} as const;
