/**
 * RecallSlotPrompt.reprompt.test.tsx - Step 5: Render Repeated Prompt in UI
 *
 * TLA+ Properties:
 * - Reachability: mock API response with same missing slots → assert same prompts displayed
 * - TypeInvariant: component state matches RecallPromptState type
 * - ErrorConsistency: simulate setState failure → logger called and previous prompt remains
 * - Feedback Loop: simulate 5 consecutive failed attempts → assert guidance hint rendered
 *
 * Resource: ui-w8p2 (component)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import React from 'react';
import type { SlotPrompt } from '@/api_contracts/submitSlots';

// Mock fetch globally
const mockFetch = vi.fn();
global.fetch = mockFetch;

// Mock frontend logger
vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { RecallSlotPrompt } from '../RecallSlotPrompt';
import { frontendLogger } from '@/logging/index';

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const missingSlotPrompts: SlotPrompt[] = [
  { name: 'objective', promptLabel: 'What was your objective or goal?' },
  { name: 'outcome', promptLabel: 'What was the outcome or result?' },
];

function createRepromptResponse(
  prompts: SlotPrompt[] = missingSlotPrompts,
  attemptCount: number = 2,
  guidanceHint: boolean = false,
) {
  return {
    ok: true,
    json: () =>
      Promise.resolve({
        prompts,
        attemptCount,
        guidanceHint,
      }),
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallSlotPrompt — Step 5: Render Repeated Prompt in UI', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockFetch.mockReset();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should display same prompts after API returns same missing slots', async () => {
      // First response returns same missing slots
      mockFetch.mockResolvedValueOnce(
        createRepromptResponse(missingSlotPrompts, 2),
      );

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={missingSlotPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();

      // Submit with empty inputs
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      // After re-prompt, same prompts should be displayed
      await waitFor(() => {
        expect(screen.getByText('What was your objective or goal?')).toBeInTheDocument();
        expect(screen.getByText('What was the outcome or result?')).toBeInTheDocument();
      });
    });

    it('should not trigger navigation after re-prompt', async () => {
      mockFetch.mockResolvedValueOnce(
        createRepromptResponse(missingSlotPrompts, 2),
      );

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={missingSlotPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      // Form should still be present (no navigation)
      await waitFor(() => {
        expect(screen.getByTestId('recall-slot-prompt-form')).toBeInTheDocument();
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should maintain component state with all required RecallPromptState fields', async () => {
      mockFetch.mockResolvedValueOnce(
        createRepromptResponse(missingSlotPrompts, 3, false),
      );

      const onUpdate = vi.fn();

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={missingSlotPrompts}
          attemptCount={2}
          guidanceHint={false}
          onUpdate={onUpdate}
        />,
      );

      const user = userEvent.setup();
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      await waitFor(() => {
        expect(onUpdate).toHaveBeenCalledWith(
          expect.objectContaining({
            prompts: expect.any(Array),
            attemptCount: expect.any(Number),
            guidanceHint: expect.any(Boolean),
          }),
        );
      });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should log error and preserve prompt state on network failure', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={missingSlotPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      // Prompts should still be displayed (previous state preserved)
      await waitFor(() => {
        expect(screen.getByText('What was your objective or goal?')).toBeInTheDocument();
        expect(screen.getByText('What was the outcome or result?')).toBeInTheDocument();
      });

      // Logger should have been called
      expect(frontendLogger.error).toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // Feedback Loop
  // -------------------------------------------------------------------------

  describe('Feedback Loop', () => {
    it('should render guidance hint when attemptCount >= 5', () => {
      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={missingSlotPrompts}
          attemptCount={5}
          guidanceHint={true}
        />,
      );

      expect(screen.getByTestId('guidance-hint')).toBeInTheDocument();
    });

    it('should not render guidance hint when attemptCount < 5', () => {
      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={missingSlotPrompts}
          attemptCount={3}
          guidanceHint={false}
        />,
      );

      expect(screen.queryByTestId('guidance-hint')).not.toBeInTheDocument();
    });

    it('should show guidance hint after API response indicates threshold reached', async () => {
      mockFetch.mockResolvedValueOnce(
        createRepromptResponse(missingSlotPrompts, 5, true),
      );

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={missingSlotPrompts}
          attemptCount={4}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      await waitFor(() => {
        expect(screen.getByTestId('guidance-hint')).toBeInTheDocument();
      });
    });
  });
});
