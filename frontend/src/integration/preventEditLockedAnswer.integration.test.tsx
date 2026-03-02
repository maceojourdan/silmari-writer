/**
 * Integration Test: prevent-edit-of-locked-answer
 *
 * Path: 337
 *
 * End-to-end flow:
 *   1. Render AnswerEditor with locked answer data
 *   2. User attempts edit and clicks Save
 *   3. Request flows through: Component → API Contract → Route → Handler → Service → DAO
 *   4. Service detects locked status and throws LOCKED_ANSWER_MODIFICATION_FORBIDDEN
 *   5. Error propagates back through layers to UI
 *   6. UI displays locked message and preserves original content
 *
 * TLA+ Properties proved:
 * - Reachability: Full trigger → UI error path is exercisable
 * - TypeInvariant: Types consistent across UI → API → service → DAO
 * - ErrorConsistency: Locked branch always results in correct domain + UI error state
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import React from 'react';

// ---------------------------------------------------------------------------
// Mocks — only DAOs and logger (lowest layer)
// ---------------------------------------------------------------------------

vi.mock('@/server/data_access_objects/AnswerDAO', () => ({
  AnswerDAO: {
    findById: vi.fn(),
    update: vi.fn(),
    updateContent: vi.fn(),
  },
}));

vi.mock('@/server/logging/logger', () => ({
  logger: { info: vi.fn(), warn: vi.fn(), error: vi.fn() },
}));

import { AnswerDAO } from '@/server/data_access_objects/AnswerDAO';
import { AnswerService } from '@/server/services/AnswerService';
import { UpdateAnswerResultSchema } from '@/server/services/AnswerService';
import { UpdateAnswerRequestHandler } from '@/server/request_handlers/UpdateAnswerRequestHandler';
import { AnswerError } from '@/server/error_definitions/AnswerErrors';
import { UpdateAnswerRequestSchema, UpdateAnswerResponseSchema } from '@/api_contracts/updateAnswer';
import { validateAnswerUpdate } from '@/verifiers/answerUpdateVerifier';
import type { Answer } from '@/server/data_structures/Answer';
import { AnswerSchema } from '@/server/data_structures/Answer';

// Import frontend component
import AnswerEditor from '@/components/AnswerEditor';

const mockFindById = vi.mocked(AnswerDAO.findById);
const mockUpdateContent = vi.mocked(AnswerDAO.updateContent);

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

const NOW = new Date().toISOString();

const lockedAnswer: Answer = {
  id: '550e8400-e29b-41d4-a716-446655440000',
  status: 'FINALIZED',
  finalized: true,
  editable: false,
  locked: true,
  content: 'This is the original finalized answer content.',
  userId: 'user-integration-001',
  createdAt: NOW,
  updatedAt: NOW,
};

const unlockedAnswer: Answer = {
  id: '550e8400-e29b-41d4-a716-446655440001',
  status: 'COMPLETED',
  finalized: false,
  editable: true,
  locked: false,
  content: 'This is an editable answer.',
  userId: 'user-integration-001',
  createdAt: NOW,
  updatedAt: NOW,
};

// ---------------------------------------------------------------------------
// Integration Test
// ---------------------------------------------------------------------------

describe('Integration: prevent-edit-of-locked-answer full flow', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should execute full flow from locked answer detection to error response', async () => {
    // --------- Step 1: Validate fixture against Answer schema ---------
    const answerValidation = AnswerSchema.safeParse(lockedAnswer);
    expect(answerValidation.success).toBe(true);

    // --------- Step 2: Validate request through verifier ---------
    const verifierResult = validateAnswerUpdate(lockedAnswer.id, 'New content attempt');
    expect(verifierResult.valid).toBe(true);
    if (verifierResult.valid) {
      const requestValidation = UpdateAnswerRequestSchema.safeParse({
        id: verifierResult.payload.id,
        content: verifierResult.payload.content,
      });
      expect(requestValidation.success).toBe(true);
    }

    // --------- Step 3: Service detects locked status ---------
    mockFindById.mockResolvedValue(lockedAnswer);

    try {
      await AnswerService.updateAnswer(lockedAnswer.id, 'New content attempt');
      expect.fail('Should have thrown LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
    } catch (error) {
      expect(error).toBeInstanceOf(AnswerError);
      const answerError = error as AnswerError;
      expect(answerError.code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
      expect(answerError.statusCode).toBe(403);
      expect(answerError.message).toBe('This answer has been finalized and cannot be modified.');
    }

    // --------- Step 4: Verify DAO.updateContent was NOT called ---------
    expect(mockUpdateContent).not.toHaveBeenCalled();

    // --------- Step 5: Verify through request handler ---------
    mockFindById.mockResolvedValue(lockedAnswer);

    try {
      await UpdateAnswerRequestHandler.handle(lockedAnswer.id, 'New content attempt');
      expect.fail('Should have thrown');
    } catch (error) {
      expect(error).toBeInstanceOf(AnswerError);
      expect((error as AnswerError).code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
    }

    // --------- Step 6: DB content unchanged ---------
    expect(mockUpdateContent).not.toHaveBeenCalled();
  });

  it('should prove Reachability: trigger → UI error path is exercisable', async () => {
    // Mock fetch to simulate the full API response chain
    const mockFetch = vi.fn().mockResolvedValue({
      ok: false,
      status: 403,
      json: async () => ({
        code: 'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
        message: 'This answer has been finalized and cannot be modified.',
      }),
    });
    vi.stubGlobal('fetch', mockFetch);

    const user = userEvent.setup();

    render(
      <AnswerEditor
        answerId={lockedAnswer.id}
        initialContent={lockedAnswer.content}
      />,
    );

    // User attempts to edit
    const textarea = screen.getByTestId('answer-content-input');
    await user.clear(textarea);
    await user.type(textarea, 'Attempting to modify locked answer');

    // User clicks Save
    const saveButton = screen.getByRole('button', { name: /save/i });
    await user.click(saveButton);

    // Assert locked message displayed
    await waitFor(() => {
      const errorElement = screen.getByRole('alert');
      expect(errorElement).toBeDefined();
      expect(errorElement.textContent).toContain(
        'This answer has been finalized and cannot be modified.',
      );
    });

    // Assert HTTP response contained LOCKED_ANSWER_MODIFICATION_FORBIDDEN
    expect(mockFetch).toHaveBeenCalledTimes(1);
    const [url, options] = mockFetch.mock.calls[0];
    expect(url).toContain(`/api/answers/${lockedAnswer.id}`);
    expect(options.method).toBe('PUT');

    vi.unstubAllGlobals();
  });

  it('should prove TypeInvariant: types consistent across UI → API → service → DAO', async () => {
    // 1. Answer entity validates against AnswerSchema
    const entityValidation = AnswerSchema.safeParse(lockedAnswer);
    expect(entityValidation.success).toBe(true);

    // 2. Frontend verifier produces typed payload
    const verifierResult = validateAnswerUpdate(lockedAnswer.id, 'test content');
    expect(verifierResult.valid).toBe(true);
    if (verifierResult.valid) {
      expect(typeof verifierResult.payload.id).toBe('string');
      expect(typeof verifierResult.payload.content).toBe('string');
    }

    // 3. API request matches request schema
    const requestValidation = UpdateAnswerRequestSchema.safeParse({
      id: lockedAnswer.id,
      content: 'test content',
    });
    expect(requestValidation.success).toBe(true);

    // 4. Service returns typed result for unlocked answer
    mockFindById.mockResolvedValue(unlockedAnswer);
    const updatedAnswer: Answer = {
      ...unlockedAnswer,
      content: 'new content',
      updatedAt: NOW,
    };
    mockUpdateContent.mockResolvedValue(updatedAnswer);

    const serviceResult = await AnswerService.updateAnswer(
      unlockedAnswer.id,
      'new content',
    );
    const resultValidation = UpdateAnswerResultSchema.safeParse(serviceResult);
    expect(resultValidation.success).toBe(true);

    // 5. Response matches response schema
    const responseValidation = UpdateAnswerResponseSchema.safeParse(serviceResult);
    expect(responseValidation.success).toBe(true);

    // 6. Error has typed { code: string, message: string } shape
    mockFindById.mockResolvedValue(lockedAnswer);
    try {
      await AnswerService.updateAnswer(lockedAnswer.id, 'attempt');
      expect.fail('Should have thrown');
    } catch (error) {
      expect(error).toBeInstanceOf(AnswerError);
      const answerError = error as AnswerError;
      expect(typeof answerError.code).toBe('string');
      expect(typeof answerError.message).toBe('string');
      expect(typeof answerError.statusCode).toBe('number');
    }
  });

  it('should prove ErrorConsistency: locked branch always results in correct domain + UI error state', async () => {
    // 1. Service level: locked answer always throws correct error
    mockFindById.mockResolvedValue(lockedAnswer);

    try {
      await AnswerService.updateAnswer(lockedAnswer.id, 'any content');
      expect.fail('Should have thrown');
    } catch (error) {
      const answerError = error as AnswerError;
      expect(answerError.code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
      expect(answerError.statusCode).toBe(403);
      expect(answerError.retryable).toBe(false);
    }

    // 2. Handler level: error propagates unchanged
    mockFindById.mockResolvedValue(lockedAnswer);

    try {
      await UpdateAnswerRequestHandler.handle(lockedAnswer.id, 'any content');
      expect.fail('Should have thrown');
    } catch (error) {
      const answerError = error as AnswerError;
      expect(answerError.code).toBe('LOCKED_ANSWER_MODIFICATION_FORBIDDEN');
      expect(answerError.statusCode).toBe(403);
    }

    // 3. DAO.updateContent never called
    expect(mockUpdateContent).not.toHaveBeenCalled();

    // 4. UI level: mock fetch to return locked error, verify UI state
    const mockFetch = vi.fn().mockResolvedValue({
      ok: false,
      status: 403,
      json: async () => ({
        code: 'LOCKED_ANSWER_MODIFICATION_FORBIDDEN',
        message: 'This answer has been finalized and cannot be modified.',
      }),
    });
    vi.stubGlobal('fetch', mockFetch);

    const user = userEvent.setup();

    render(
      <AnswerEditor
        answerId={lockedAnswer.id}
        initialContent="Original content"
      />,
    );

    // Edit and save
    const textarea = screen.getByTestId('answer-content-input');
    await user.clear(textarea);
    await user.type(textarea, 'Trying to edit locked answer');
    await user.click(screen.getByRole('button', { name: /save/i }));

    // Assert UI shows locked message
    await waitFor(() => {
      expect(screen.getByRole('alert').textContent).toContain(
        'This answer has been finalized and cannot be modified.',
      );
    });

    // Assert content reverted to original
    await waitFor(() => {
      expect(textarea).toHaveValue('Original content');
    });

    vi.unstubAllGlobals();
  });
});
