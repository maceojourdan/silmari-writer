/**
 * SessionControls.test.tsx - Step 1: Capture "Add Voice Input" action
 *
 * TLA+ Properties:
 * - Reachability: simulate click "Add Voice Input" with valid sessionId, assert modifySession() called.
 * - TypeInvariant: assert payload matches { sessionId: string; action: 'ADD_VOICE' | 'FINALIZE' }
 * - ErrorConsistency: pass invalid payload (missing sessionId), assert verifier prevents call and displays validation error.
 *
 * Resource: ui-w8p2 (component)
 * Path: 309-reject-modifications-to-finalized-session
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { ModifySessionPayloadSchema } from '@/verifiers/SessionModificationVerifier';

// Mock fetch at the network level
const mockFetch = vi.fn();

import SessionControls from '../SessionControls';

describe('SessionControls — Step 1: Capture modification action', () => {
  const sessionId = '550e8400-e29b-41d4-a716-446655440000';

  beforeEach(() => {
    vi.stubGlobal('fetch', mockFetch);
    mockFetch.mockReset();
  });

  afterEach(() => {
    vi.unstubAllGlobals();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call modifySession API with { sessionId, action: ADD_VOICE } on click', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ id: sessionId, status: 'DRAFT' }),
      });

      render(<SessionControls sessionId={sessionId} />);
      await userEvent.click(screen.getByRole('button', { name: /add voice input/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe(`/api/sessions/${sessionId}/modify`);
      expect(options.method).toBe('POST');

      const body = JSON.parse(options.body);
      expect(body.sessionId).toBe(sessionId);
      expect(body.action).toBe('ADD_VOICE');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload that satisfies ModifySessionPayloadSchema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ id: sessionId, status: 'DRAFT' }),
      });

      render(<SessionControls sessionId={sessionId} />);
      await userEvent.click(screen.getByRole('button', { name: /add voice input/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = ModifySessionPayloadSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should block API call and display validation error when sessionId is empty', async () => {
      render(<SessionControls sessionId="" />);
      await userEvent.click(screen.getByRole('button', { name: /add voice input/i }));

      // API should NOT have been called
      expect(mockFetch).not.toHaveBeenCalled();

      // Should display validation error
      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should display error message when API returns 409', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 409,
        json: async () => ({
          code: 'SESSION_ALREADY_FINALIZED',
          message: 'Session is already finalized and cannot be modified',
        }),
      });

      render(<SessionControls sessionId={sessionId} />);
      await userEvent.click(screen.getByRole('button', { name: /add voice input/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('finalized');
      });
    });
  });
});
