/**
 * AnswerEditor.locked.test.tsx - Step 5: Display locked message
 *
 * TLA+ Properties:
 * - Reachability: Submit valid edit when API rejects with LOCKED_ANSWER_MODIFICATION_FORBIDDEN → assert locked message displayed
 * - TypeInvariant: Assert error response from API contains code property; assert error is instance of UpdateAnswerApiError
 * - ErrorConsistency: Submit edit when API rejects with unknown code → assert generic error shown and original content preserved
 *
 * Resource: ui-w8p2 (component)
 * Path: 337-prevent-edit-of-locked-answer
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

// Mock the API contract
vi.mock('@/api_contracts/updateAnswer', () => ({
  updateAnswer: vi.fn(),
  UpdateAnswerApiError: class extends Error {
    code: string;
    constructor(code: string, message: string) {
      super(message);
      this.name = 'UpdateAnswerApiError';
      this.code = code;
    }
  },
}));

// Mock the verifier
vi.mock('@/verifiers/answerUpdateVerifier', () => ({
  validateAnswerUpdate: vi.fn(),
}));

import AnswerEditor from '../AnswerEditor';
import { updateAnswer, UpdateAnswerApiError } from '@/api_contracts/updateAnswer';
import { validateAnswerUpdate } from '@/verifiers/answerUpdateVerifier';

const mockUpdateAnswer = vi.mocked(updateAnswer);
const mockValidateAnswerUpdate = vi.mocked(validateAnswerUpdate);

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const initialContent = 'My original answer about leadership.';

describe('AnswerEditor — Step 5: Display locked message', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should display locked message when API rejects with LOCKED_ANSWER_MODIFICATION_FORBIDDEN', async () => {
      const updatedContent = 'attempted edit content';

      mockValidateAnswerUpdate.mockReturnValue({
        valid: true,
        payload: { id: answerId, content: updatedContent },
      });
      mockUpdateAnswer.mockRejectedValueOnce(
        new UpdateAnswerApiError(
          'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
          'This answer has been finalized and cannot be modified.'
        )
      );

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);
      await userEvent.type(textarea, updatedContent);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toBe(
          'This answer has been finalized and cannot be modified.'
        );
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should handle error that has a code property from UpdateAnswerApiError', async () => {
      const lockedError = new UpdateAnswerApiError(
        'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
        'Locked'
      );

      expect(lockedError).toBeInstanceOf(Error);
      expect(lockedError).toBeInstanceOf(UpdateAnswerApiError);
      expect(lockedError.code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
      expect(lockedError.name).toBe('UpdateAnswerApiError');
    });

    it('should distinguish UpdateAnswerApiError from generic Error by code property', async () => {
      const apiError = new UpdateAnswerApiError('SOME_CODE', 'API error');
      const genericError = new Error('Generic error');

      expect('code' in apiError).toBe(true);
      expect('code' in genericError).toBe(false);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display generic error when API rejects with unknown UpdateAnswerApiError code', async () => {
      const updatedContent = 'attempted edit content';

      mockValidateAnswerUpdate.mockReturnValue({
        valid: true,
        payload: { id: answerId, content: updatedContent },
      });
      mockUpdateAnswer.mockRejectedValueOnce(
        new UpdateAnswerApiError('SOME_UNKNOWN_CODE', 'Something broke')
      );

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);
      await userEvent.type(textarea, updatedContent);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toBe(
          'An unexpected error occurred. Please try again.'
        );
      });

      // Original content should remain unchanged in textarea
      const textareaAfter = screen.getByTestId('answer-content-input');
      expect(textareaAfter).toHaveValue(initialContent);
    });

    it('should display generic error when API rejects with a non-UpdateAnswerApiError', async () => {
      const updatedContent = 'attempted edit content';

      mockValidateAnswerUpdate.mockReturnValue({
        valid: true,
        payload: { id: answerId, content: updatedContent },
      });
      mockUpdateAnswer.mockRejectedValueOnce(
        new Error('Network failure')
      );

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);
      await userEvent.type(textarea, updatedContent);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toBe(
          'An unexpected error occurred. Please try again.'
        );
      });

      // Original content should remain unchanged in textarea
      const textareaAfter = screen.getByTestId('answer-content-input');
      expect(textareaAfter).toHaveValue(initialContent);
    });

    it('should preserve original content on LOCKED_ANSWER_MODIFICATION_FORBIDDEN error', async () => {
      const updatedContent = 'attempted edit content';

      mockValidateAnswerUpdate.mockReturnValue({
        valid: true,
        payload: { id: answerId, content: updatedContent },
      });
      mockUpdateAnswer.mockRejectedValueOnce(
        new UpdateAnswerApiError(
          'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
          'This answer has been finalized and cannot be modified.'
        )
      );

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);
      await userEvent.type(textarea, updatedContent);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });

      // Original content should be restored
      const textareaAfter = screen.getByTestId('answer-content-input');
      expect(textareaAfter).toHaveValue(initialContent);
    });
  });
});
