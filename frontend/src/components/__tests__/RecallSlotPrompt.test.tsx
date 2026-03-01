/**
 * RecallSlotPrompt.test.tsx - Step 1: Capture User Slot Input
 *
 * TLA+ Properties:
 * - Reachability: simulate user submit → assert SubmitSlots contract called with structured payload
 * - TypeInvariant: payload matches Zod schema in SubmitSlots.ts
 * - ErrorConsistency: submit malformed payload → mock 400 response with SLOT_SUBMISSION_INVALID
 *   → component re-renders same prompt
 *
 * Resource: ui-w8p2 (component)
 * Path: 320-re-prompt-unfilled-required-slots
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import React from 'react';
import { SubmitSlotsRequestSchema } from '@/api_contracts/submitSlots';
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

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const validSessionId = 'a1b2c3d4-e5f6-7890-abcd-ef1234567890';

const defaultPrompts: SlotPrompt[] = [
  { name: 'objective', promptLabel: 'What was your objective or goal?' },
  { name: 'outcome', promptLabel: 'What was the outcome or result?' },
];

function createSuccessResponse(prompts: SlotPrompt[] = defaultPrompts) {
  return {
    ok: true,
    json: () =>
      Promise.resolve({
        prompts,
        attemptCount: 2,
        guidanceHint: false,
      }),
  };
}

function create400Response() {
  return {
    ok: false,
    status: 400,
    json: () =>
      Promise.resolve({
        code: 'SLOT_SUBMISSION_INVALID',
        message: 'Slot submission payload is malformed or incomplete',
      }),
  };
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('RecallSlotPrompt — Step 1: Capture User Slot Input', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockFetch.mockReset();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should render prompt labels for each missing slot', () => {
      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={defaultPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      expect(screen.getByText('What was your objective or goal?')).toBeInTheDocument();
      expect(screen.getByText('What was the outcome or result?')).toBeInTheDocument();
    });

    it('should call submit endpoint with structured payload on form submit', async () => {
      mockFetch.mockResolvedValueOnce(createSuccessResponse());

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={defaultPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();

      // Fill in the input fields
      const inputs = screen.getAllByRole('textbox');
      await user.type(inputs[0], 'Increase revenue');
      await user.type(inputs[1], 'Revenue grew by 25%');

      // Submit the form
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      // Verify the fetch was called with correct endpoint and payload structure
      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe('/api/session/submit-slots');
      expect(options.method).toBe('POST');

      const body = JSON.parse(options.body);
      expect(body.sessionId).toBe(validSessionId);
      expect(body.questionType).toBe('behavioral_question');
      expect(body.slotValues).toBeDefined();
      expect(body.attemptCount).toBe(1);
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload matching SubmitSlotsRequest Zod schema', async () => {
      mockFetch.mockResolvedValueOnce(createSuccessResponse());

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={defaultPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();

      // Fill in inputs
      const inputs = screen.getAllByRole('textbox');
      await user.type(inputs[0], 'Test objective');
      await user.type(inputs[1], 'Test outcome');

      // Submit
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalled();
      });

      // Parse and validate against Zod schema
      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = SubmitSlotsRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should re-render same prompts on 400 SLOT_SUBMISSION_INVALID response', async () => {
      mockFetch.mockResolvedValueOnce(create400Response());

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={defaultPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();

      // Submit without filling inputs (malformed)
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      // Prompts should still be visible
      await waitFor(() => {
        expect(screen.getByText('What was your objective or goal?')).toBeInTheDocument();
        expect(screen.getByText('What was the outcome or result?')).toBeInTheDocument();
      });
    });

    it('should display error message on submission failure', async () => {
      mockFetch.mockResolvedValueOnce(create400Response());

      render(
        <RecallSlotPrompt
          sessionId={validSessionId}
          questionType="behavioral_question"
          prompts={defaultPrompts}
          attemptCount={1}
          guidanceHint={false}
        />,
      );

      const user = userEvent.setup();
      const submitButton = screen.getByRole('button', { name: /submit/i });
      await user.click(submitButton);

      await waitFor(() => {
        expect(screen.getByRole('alert')).toBeInTheDocument();
      });
    });
  });
});
