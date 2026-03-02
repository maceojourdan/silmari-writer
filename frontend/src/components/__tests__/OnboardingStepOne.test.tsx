/**
 * OnboardingStepOne.test.tsx - Step 1: User completes KPI-contributing action
 *
 * TLA+ Properties:
 * - Reachability: Render component with userId, simulate valid completion → assert completeOnboardingStep (via fetch) called with { userId, step: 1, metadata }
 * - TypeInvariant: Assert request payload matches CompleteOnboardingStepRequestSchema
 * - ErrorConsistency: Provide invalid input (empty userId) → assert verifier blocks submission, assert API contract not called
 *
 * Resource: ui-a4y1 (component)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 */

// @ts-nocheck
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { render, screen, waitFor } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import { CompleteOnboardingStepRequestSchema } from '@/api_contracts/CompleteOnboardingStep';

// Mock fetch at the network level
const mockFetch = vi.fn();

import OnboardingStepOne from '../OnboardingStepOne';

describe('OnboardingStepOne — Step 1: User completes KPI-contributing action', () => {
  const userId = 'user-abc-123';

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
    it('should call API with userId and step 1 when button is clicked', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          status: 'completed',
          onboardingId: 'onb-001',
          step: 1,
          analyticsRecorded: true,
        }),
      });

      render(<OnboardingStepOne userId={userId} />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const [url, options] = mockFetch.mock.calls[0];
      expect(url).toBe('/api/onboarding/complete');
      expect(options.method).toBe('POST');

      const body = JSON.parse(options.body);
      expect(body.userId).toBe(userId);
      expect(body.step).toBe(1);
    });

    it('should show success message after completion', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          status: 'completed',
          onboardingId: 'onb-001',
          step: 1,
          analyticsRecorded: true,
        }),
      });

      render(<OnboardingStepOne userId={userId} />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      await waitFor(() => {
        expect(screen.getByTestId('onboarding-success')).toBeInTheDocument();
      });

      expect(screen.getByText(/onboarding step 1 completed successfully/i)).toBeInTheDocument();
    });

    it('should invoke onCompleted callback with the response', async () => {
      const expectedResponse = {
        status: 'completed',
        onboardingId: 'onb-001',
        step: 1,
        analyticsRecorded: true,
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => expectedResponse,
      });

      const onCompleted = vi.fn();
      render(<OnboardingStepOne userId={userId} onCompleted={onCompleted} />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      await waitFor(() => {
        expect(onCompleted).toHaveBeenCalledTimes(1);
        expect(onCompleted).toHaveBeenCalledWith(expectedResponse);
      });
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should send payload that satisfies CompleteOnboardingStepRequestSchema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          status: 'completed',
          onboardingId: 'onb-001',
          step: 1,
          analyticsRecorded: true,
        }),
      });

      render(<OnboardingStepOne userId={userId} />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      const parsed = CompleteOnboardingStepRequestSchema.safeParse(body);
      expect(parsed.success).toBe(true);
    });

    it('should send userId as a string and step as a positive integer', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          status: 'completed',
          onboardingId: 'onb-001',
          step: 1,
          analyticsRecorded: true,
        }),
      });

      render(<OnboardingStepOne userId={userId} />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      await waitFor(() => {
        expect(mockFetch).toHaveBeenCalledTimes(1);
      });

      const body = JSON.parse(mockFetch.mock.calls[0][1].body);
      expect(typeof body.userId).toBe('string');
      expect(body.userId.length).toBeGreaterThan(0);
      expect(typeof body.step).toBe('number');
      expect(Number.isInteger(body.step)).toBe(true);
      expect(body.step).toBeGreaterThanOrEqual(1);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should block API call when userId is empty', async () => {
      render(<OnboardingStepOne userId="" />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      expect(mockFetch).not.toHaveBeenCalled();
    });

    it('should display validation error when userId is empty', async () => {
      render(<OnboardingStepOne userId="" />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
        expect(errorElement.textContent).toContain('User ID is required');
      });
    });

    it('should block API call when userId is whitespace only', async () => {
      render(<OnboardingStepOne userId="   " />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      expect(mockFetch).not.toHaveBeenCalled();

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });

    it('should display error when API call fails', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({
          code: 'INTERNAL_ERROR',
          message: 'Server error',
        }),
      });

      render(<OnboardingStepOne userId={userId} />);
      await userEvent.click(screen.getByRole('button', { name: /complete onboarding step/i }));

      await waitFor(() => {
        const errorElement = screen.getByRole('alert');
        expect(errorElement).toBeInTheDocument();
      });
    });
  });
});
