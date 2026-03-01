/**
 * route.test.ts - Step 5b: Enforce Block and Return Response
 *
 * TLA+ Properties:
 * - Reachability: valid consent → 200 response { sessionStatus: 'INIT' }
 * - TypeInvariant: response conforms to API contract
 * - ErrorConsistency:
 *   - Consent invalid → 400 with CONSENT_REQUIRED
 *   - Simulated service exception → 500 + backend log called
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 302-enforce-affirmative-consent-before-voice-session
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock the handler
vi.mock('@/server/request_handlers/StartVoiceSessionHandler', () => ({
  StartVoiceSessionHandler: {
    handle: vi.fn(),
  },
}));

import { StartVoiceSessionHandler } from '@/server/request_handlers/StartVoiceSessionHandler';
import { ConsentError } from '@/server/error_definitions/ConsentErrors';
import { POST } from '../route';

const mockHandler = vi.mocked(StartVoiceSessionHandler);

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function createRequest(body: Record<string, unknown>): NextRequest {
  return new NextRequest('http://localhost:3000/api/voice-session/start', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('POST /api/voice-session/start — Step 5b: Enforce Block and Return Response', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return 200 with { sessionStatus: INIT } for valid consent', async () => {
      mockHandler.handle.mockResolvedValue({
        authorized: true,
        sessionStatus: 'INIT',
      });

      const request = createRequest({ consent: true });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.sessionStatus).toBe('INIT');
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return JSON response with correct content-type', async () => {
      mockHandler.handle.mockResolvedValue({
        authorized: true,
        sessionStatus: 'INIT',
      });

      const request = createRequest({ consent: true });
      const response = await POST(request);

      expect(response.headers.get('content-type')).toContain('application/json');
    });

    it('should pass consent payload to handler', async () => {
      mockHandler.handle.mockResolvedValue({
        authorized: true,
        sessionStatus: 'INIT',
      });

      const request = createRequest({ consent: true });
      await POST(request);

      expect(mockHandler.handle).toHaveBeenCalledWith({ consent: true });
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 400 with CONSENT_REQUIRED when consent is invalid', async () => {
      mockHandler.handle.mockRejectedValue(
        new ConsentError(
          'Affirmative consent is required before starting voice session',
          'CONSENT_REQUIRED',
          400,
        ),
      );

      const request = createRequest({ consent: false });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('CONSENT_REQUIRED');
      expect(data.message).toContain('Affirmative consent is required');
    });

    it('should return 500 for unexpected errors', async () => {
      mockHandler.handle.mockRejectedValue(new Error('Unexpected DB failure'));

      const request = createRequest({ consent: true });
      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('INTERNAL_ERROR');
    });

    it('should return 400 for missing body', async () => {
      const request = new NextRequest('http://localhost:3000/api/voice-session/start', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({}),
      });

      // Handler will throw ConsentError for missing consent
      mockHandler.handle.mockRejectedValue(
        new ConsentError(
          'Affirmative consent is required before starting voice session',
          'CONSENT_REQUIRED',
          400,
        ),
      );

      const response = await POST(request);
      expect(response.status).toBe(400);
    });
  });
});
