/**
 * initiateVerification.integration.test.ts - Step 6: Full Path Integration Test
 *
 * TLA+ Properties:
 * - Reachability: Full path call with claimant lacking contact method → HTTP 200 with failure payload
 * - TypeInvariant: Response matches frontend API contract type
 * - ErrorConsistency: Serialization error → 500 + GENERIC_VERIFICATION_FAILURE
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 323-fail-verification-when-no-contact-method
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { InitiateVerificationResponseSchema } from '@/server/data_structures/VerificationAttempt';

// Mock VerificationDAO (lowest layer)
vi.mock('@/server/data_access_objects/VerificationDAO', () => ({
  VerificationDAO: {
    getClaimantById: vi.fn(),
    createVerificationAttempt: vi.fn(),
    getLatestVerificationAttempt: vi.fn(),
    updateDraftingStatus: vi.fn(),
  },
}));

// Mock the logger
vi.mock('@/server/logging/verificationLogger', () => ({
  verificationLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

// We don't mock ClaimDAO/SessionDAO/VerificationRequestDAO since Path 323 doesn't use them directly
// But they are imported by VerificationService, so mock them to prevent import errors
vi.mock('@/server/data_access_objects/ClaimDAO', () => ({
  ClaimDAO: {
    getUnverifiedClaimsBySession: vi.fn(),
    findById: vi.fn(),
    findByPhoneNumber: vi.fn(),
    updateTruthCheck: vi.fn(),
    updateStatusToVerified: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/VerificationRequestDAO', () => ({
  VerificationRequestDAO: {
    create: vi.fn(),
    findByToken: vi.fn(),
    findBySessionId: vi.fn(),
    updateStatus: vi.fn(),
    logDeliveryAttempt: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/SessionDAO', () => ({
  SessionDAO: {
    findById: vi.fn(),
    updateState: vi.fn(),
  },
}));

import { VerificationDAO } from '@/server/data_access_objects/VerificationDAO';
import type { Claimant } from '@/server/data_structures/Claimant';
import type { VerificationAttempt } from '@/server/data_structures/VerificationAttempt';

const mockDAO = vi.mocked(VerificationDAO);

// ---------------------------------------------------------------------------
// Test Fixtures
// ---------------------------------------------------------------------------

const now = new Date().toISOString();
const claimantId = '550e8400-e29b-41d4-a716-446655440000';

const claimantNoContact: Claimant = {
  id: claimantId,
  keyClaims: [
    { id: 'kc-1', category: 'metrics', content: 'Revenue +40%' },
  ],
  phone: null,
  smsOptIn: false,
};

const failedAttempt: VerificationAttempt = {
  id: 'va-001',
  claimantId,
  status: 'FAILED',
  reason: 'MISSING_CONTACT_METHOD',
  createdAt: now,
  updatedAt: now,
};

function createRequest(body: unknown): Request {
  return new Request('http://localhost/api/verification/initiate', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('Path 323 Integration: fail-verification-when-no-contact-method', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default mocks for the full path
    mockDAO.getClaimantById.mockResolvedValue(claimantNoContact);
    mockDAO.createVerificationAttempt.mockResolvedValue(failedAttempt);
    mockDAO.getLatestVerificationAttempt.mockResolvedValue(failedAttempt);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should return HTTP 200 with verificationStatus=FAILED and draftingAllowed=false', async () => {
      // Dynamic import to ensure mocks are set up first
      const { POST } = await import('@/app/api/verification/initiate/route');

      const request = createRequest({ claimantId });
      const response = await POST(request as any);
      const json = await response.json();

      expect(response.status).toBe(200);
      expect(json).toEqual({
        verificationStatus: 'FAILED',
        reason: 'MISSING_CONTACT_METHOD',
        draftingAllowed: false,
      });
    });

    it('should have called VerificationDAO.getClaimantById', async () => {
      const { POST } = await import('@/app/api/verification/initiate/route');

      const request = createRequest({ claimantId });
      await POST(request as any);

      expect(mockDAO.getClaimantById).toHaveBeenCalledWith(claimantId);
    });

    it('should have persisted a FAILED verification attempt', async () => {
      const { POST } = await import('@/app/api/verification/initiate/route');

      const request = createRequest({ claimantId });
      await POST(request as any);

      expect(mockDAO.createVerificationAttempt).toHaveBeenCalledWith(
        claimantId,
        'FAILED',
        'MISSING_CONTACT_METHOD',
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a response matching InitiateVerificationResponse schema', async () => {
      const { POST } = await import('@/app/api/verification/initiate/route');

      const request = createRequest({ claimantId });
      const response = await POST(request as any);
      const json = await response.json();

      const parsed = InitiateVerificationResponseSchema.safeParse(json);
      expect(parsed.success).toBe(true);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should return 400 with VERIFICATION_REQUEST_INVALID for empty body', async () => {
      const { POST } = await import('@/app/api/verification/initiate/route');

      const request = createRequest({});
      const response = await POST(request as any);
      const json = await response.json();

      expect(response.status).toBe(400);
      expect(json.code).toBe('VERIFICATION_REQUEST_INVALID');
    });

    it('should return 400 for non-UUID claimantId', async () => {
      const { POST } = await import('@/app/api/verification/initiate/route');

      const request = createRequest({ claimantId: 'not-a-uuid' });
      const response = await POST(request as any);

      expect(response.status).toBe(400);
    });

    it('should return 404 when claimant not found', async () => {
      mockDAO.getClaimantById.mockResolvedValue(null);

      const { POST } = await import('@/app/api/verification/initiate/route');

      const request = createRequest({ claimantId });
      const response = await POST(request as any);
      const json = await response.json();

      expect(response.status).toBe(404);
      expect(json.code).toBe('CLAIMANT_NOT_FOUND');
    });
  });
});
