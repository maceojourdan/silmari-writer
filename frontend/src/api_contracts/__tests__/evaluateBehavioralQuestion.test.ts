/**
 * evaluateBehavioralQuestion API Contract Tests
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * Properties tested:
 * - Reachability: mock fetch 200 → call contract → assert POST to /api/behavioral-question/evaluate
 * - TypeInvariant: request body matches BehavioralQuestionDraft
 * - ErrorConsistency: mock 500 → expect SharedErrors.NetworkError; retry logic ≤5 times
 */

import {
  evaluateBehavioralQuestion,
  EvaluateBehavioralQuestionResponseSchema,
} from '../evaluateBehavioralQuestion';
import type {
  EvaluateBehavioralQuestionRequest,
  EvaluateBehavioralQuestionResponse,
} from '../evaluateBehavioralQuestion';

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

const validRequest: EvaluateBehavioralQuestionRequest = {
  sessionId: 'session-001',
  objective: 'Led a cross-functional team to migrate legacy systems',
  actions: [
    'Identified key stakeholders and gathered requirements',
    'Created a phased migration plan with rollback procedures',
    'Coordinated daily standups across three teams',
  ],
  obstacles: ['Legacy system had undocumented dependencies'],
  outcome: 'Successfully migrated 100% of services with zero downtime',
  roleClarity: 'I was the technical lead responsible for architecture decisions',
};

const validResponse: EvaluateBehavioralQuestionResponse = {
  eligible: true,
  questionId: 'bq-001',
  status: 'VERIFY',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

describe('evaluateBehavioralQuestion API contract', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: Sends POST request to correct endpoint', () => {
    it('should POST to /api/behavioral-question/evaluate with the payload', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      await evaluateBehavioralQuestion(validRequest);

      expect(mockFetch).toHaveBeenCalledTimes(1);
      expect(mockFetch).toHaveBeenCalledWith('/api/behavioral-question/evaluate', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(validRequest),
      });
    });

    it('should return the parsed response on success', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      const result = await evaluateBehavioralQuestion(validRequest);
      expect(result.eligible).toBe(true);
      expect(result.questionId).toBe('bq-001');
      expect(result.status).toBe('VERIFY');
    });
  });

  describe('TypeInvariant: Response matches schema', () => {
    it('should return a valid EvaluateBehavioralQuestionResponse on success', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => validResponse,
      });

      const result = await evaluateBehavioralQuestion(validRequest);
      const parsed = EvaluateBehavioralQuestionResponseSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should throw on malformed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({ garbage: true }),
      });

      await expect(evaluateBehavioralQuestion(validRequest)).rejects.toThrow();
    });
  });

  describe('ErrorConsistency: Network errors with retry logic', () => {
    it('should retry up to 5 times on network failure then throw', async () => {
      mockFetch.mockRejectedValue(new Error('Network error'));

      await expect(evaluateBehavioralQuestion(validRequest)).rejects.toThrow();

      // Should have retried 5 times total
      expect(mockFetch).toHaveBeenCalledTimes(5);
    });

    it('should throw with SharedError-like message on 500 response', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 500,
        json: async () => ({ code: 'INTERNAL_ERROR', message: 'Server error' }),
      });

      await expect(evaluateBehavioralQuestion(validRequest)).rejects.toThrow();
    });

    it('should succeed on retry if a later attempt succeeds', async () => {
      mockFetch
        .mockRejectedValueOnce(new Error('Network error'))
        .mockRejectedValueOnce(new Error('Network error'))
        .mockResolvedValueOnce({
          ok: true,
          json: async () => validResponse,
        });

      const result = await evaluateBehavioralQuestion(validRequest);
      expect(result.eligible).toBe(true);
      expect(mockFetch).toHaveBeenCalledTimes(3);
    });

    it('should not retry on 4xx client errors', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 422,
        json: async () => ({ code: 'MINIMUM_SLOTS_NOT_MET', message: 'Missing slots' }),
      });

      await expect(evaluateBehavioralQuestion(validRequest)).rejects.toThrow('Missing slots');
      expect(mockFetch).toHaveBeenCalledTimes(1);
    });
  });
});
