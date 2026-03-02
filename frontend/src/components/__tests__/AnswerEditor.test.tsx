/**
 * AnswerEditor.test.tsx - Step 1: Submit edit request
 *
 * TLA+ Properties:
 * - Reachability: Render AnswerEditor with valid answerId and initialContent, change textarea, click Save → assert updateAnswer called with { id, content }
 * - TypeInvariant: Assert request payload matches shape { id: string, content: string }; after successful save, assert onSaved callback receives { id, content }
 * - ErrorConsistency: Mock validateAnswerUpdate → invalid, click Save → assert error message displayed and updateAnswer NOT called
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
import { updateAnswer } from '@/api_contracts/updateAnswer';
import { validateAnswerUpdate } from '@/verifiers/answerUpdateVerifier';

const mockUpdateAnswer = vi.mocked(updateAnswer);
const mockValidateAnswerUpdate = vi.mocked(validateAnswerUpdate);

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const initialContent = 'My original answer about leadership.';

describe('AnswerEditor — Step 1: Submit edit request', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call updateAnswer with answerId and updated content on Save', async () => {
      const updatedContent = 'updated content';

      mockValidateAnswerUpdate.mockReturnValue({
        valid: true,
        payload: { id: answerId, content: updatedContent },
      });
      mockUpdateAnswer.mockResolvedValueOnce({
        id: answerId,
        content: updatedContent,
      });

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);
      await userEvent.type(textarea, updatedContent);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        expect(mockUpdateAnswer).toHaveBeenCalledTimes(1);
        expect(mockUpdateAnswer).toHaveBeenCalledWith({
          id: answerId,
          content: updatedContent,
        });
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload matching { id: string, content: string } shape', async () => {
      const updatedContent = 'updated content';

      mockValidateAnswerUpdate.mockReturnValue({
        valid: true,
        payload: { id: answerId, content: updatedContent },
      });
      mockUpdateAnswer.mockResolvedValueOnce({
        id: answerId,
        content: updatedContent,
      });

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);
      await userEvent.type(textarea, updatedContent);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        expect(mockUpdateAnswer).toHaveBeenCalledTimes(1);
      });

      const payload = mockUpdateAnswer.mock.calls[0][0];
      expect(typeof payload.id).toBe('string');
      expect(typeof payload.content).toBe('string');
      expect(payload.id.length).toBeGreaterThan(0);
      expect(payload.content.length).toBeGreaterThan(0);
    });

    it('should invoke onSaved callback with response after successful save', async () => {
      const updatedContent = 'updated content';
      const onSaved = vi.fn();

      mockValidateAnswerUpdate.mockReturnValue({
        valid: true,
        payload: { id: answerId, content: updatedContent },
      });
      mockUpdateAnswer.mockResolvedValueOnce({
        id: answerId,
        content: updatedContent,
      });

      render(
        <AnswerEditor
          answerId={answerId}
          initialContent={initialContent}
          onSaved={onSaved}
        />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);
      await userEvent.type(textarea, updatedContent);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        expect(onSaved).toHaveBeenCalledTimes(1);
        expect(onSaved).toHaveBeenCalledWith({
          id: answerId,
          content: updatedContent,
        });
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should display validation error and NOT call updateAnswer when validation fails', async () => {
      mockValidateAnswerUpdate.mockReturnValue({
        valid: false,
        errors: ['Content is required'],
      });

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      const textarea = screen.getByTestId('answer-content-input');
      await userEvent.clear(textarea);

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('Content is required');
      });

      expect(mockUpdateAnswer).not.toHaveBeenCalled();
    });

    it('should display joined error messages when multiple validation errors occur', async () => {
      mockValidateAnswerUpdate.mockReturnValue({
        valid: false,
        errors: ['Answer ID is required', 'Content is required'],
      });

      render(
        <AnswerEditor answerId={answerId} initialContent={initialContent} />
      );

      await userEvent.click(screen.getByRole('button', { name: /save/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('Answer ID is required');
        expect(errorElement.textContent).toContain('Content is required');
      });

      expect(mockUpdateAnswer).not.toHaveBeenCalled();
    });
  });
});
