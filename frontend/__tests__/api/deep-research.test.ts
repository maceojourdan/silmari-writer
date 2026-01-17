import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock response data for Deep Research API
const mockDeepResearchResponse = {
  id: 'resp_123456',
  object: 'response',
  status: 'completed',
  output: [{
    id: 'msg_001',
    type: 'message',
    role: 'assistant',
    content: [{
      type: 'output_text',
      text: 'This is a comprehensive research report on the topic.',
      annotations: [{
        type: 'url_citation',
        url: 'https://example.com/source',
        title: 'Source Article',
        start_index: 0,
        end_index: 50
      }]
    }]
  }],
  reasoning: [{
    id: 'reasoning_001',
    type: 'reasoning',
    summary: [{ type: 'summary_text', text: 'Analyzed multiple sources...' }]
  }],
  usage: {
    input_tokens: 100,
    output_tokens: 500,
    reasoning_tokens: 200
  }
};

const mockBackgroundJobResponse = {
  id: 'job_abc123',
  object: 'response',
  status: 'pending',
};

// Mock fetch for OpenAI API calls
const mockFetch = vi.fn();
global.fetch = mockFetch;

describe('/api/tools/deep-research', () => {
  const originalEnv = process.env;
  let POST: (request: NextRequest) => Promise<Response>;

  beforeEach(async () => {
    vi.clearAllMocks();
    vi.resetModules();
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-api-key-123' };

    // Reset fetch mock
    mockFetch.mockReset();

    // Dynamically import after mocks are set up
    const module = await import('@/app/api/tools/deep-research/route');
    POST = module.POST;
  });

  afterEach(() => {
    process.env = originalEnv;
  });

  // REQ_000.1: POST requests to Deep Research API
  describe('REQ_000.1: POST requests to Deep Research API', () => {
    it('should send POST request to https://api.openai.com/v1/responses with correct Authorization header', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI',
          depth: 'quick'
        })
      });

      await POST(request);

      expect(mockFetch).toHaveBeenCalledWith(
        'https://api.openai.com/v1/responses',
        expect.objectContaining({
          method: 'POST',
          headers: expect.objectContaining({
            'Authorization': 'Bearer test-api-key-123',
            'Content-Type': 'application/json'
          })
        })
      );
    });

    it('should include model field set to o3-deep-research model for thorough depth', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI',
          depth: 'thorough'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);
      expect(requestBody.model).toBe('o3-deep-research-2025-06-26');
    });

    it('should include model field set to o4-mini-deep-research model for quick depth', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI',
          depth: 'quick'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);
      expect(requestBody.model).toBe('o4-mini-deep-research-2025-06-26');
    });

    it('should return 500 when OPENAI_API_KEY is not configured', async () => {
      delete process.env.OPENAI_API_KEY;

      // Re-import to get fresh module with new env
      vi.resetModules();
      const module = await import('@/app/api/tools/deep-research/route');

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI'
        })
      });

      const response = await module.POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('CONFIG_ERROR');
    });

    it('should include Content-Type header set to application/json', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI'
        })
      });

      await POST(request);

      expect(mockFetch).toHaveBeenCalledWith(
        expect.any(String),
        expect.objectContaining({
          headers: expect.objectContaining({
            'Content-Type': 'application/json'
          })
        })
      );
    });

    it('should transform HTTP 4xx/5xx errors into typed DeepResearchApiError', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 400,
        json: async () => ({ error: { message: 'Bad request', code: 'invalid_request' } }),
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('API_ERROR');
      expect(data.error).toBeDefined();
    });

    it('should handle rate limit errors (429) with retryable flag', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 429,
        json: async () => ({ error: { message: 'Rate limit exceeded' } }),
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(429);
      expect(data.code).toBe('RATE_LIMIT');
      expect(data.retryable).toBe(true);
    });

    it('should validate response body against expected DeepResearchResponse schema', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research the history of AI'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.text).toBeDefined();
      expect(data.citations).toBeDefined();
      expect(Array.isArray(data.citations)).toBe(true);
    });
  });

  // REQ_000.2: Support developer and user role message inputs
  describe('REQ_000.2: Developer and user role message inputs', () => {
    it('should support developer role for system-level instructions', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research AI safety',
          developerInstructions: 'Focus on peer-reviewed sources only'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.input).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            role: 'developer',
            content: expect.arrayContaining([
              expect.objectContaining({
                type: 'input_text',
                text: 'Focus on peer-reviewed sources only'
              })
            ])
          })
        ])
      );
    });

    it('should support user role for research queries', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'What are the latest developments in quantum computing?'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.input).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            role: 'user',
            content: expect.arrayContaining([
              expect.objectContaining({
                type: 'input_text',
                text: 'What are the latest developments in quantum computing?'
              })
            ])
          })
        ])
      );
    });

    it('should format content as array with input_text objects', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      requestBody.input.forEach((msg: { content: Array<{ type: string }> }) => {
        expect(Array.isArray(msg.content)).toBe(true);
        msg.content.forEach((c: { type: string }) => {
          expect(c.type).toBe('input_text');
        });
      });
    });

    it('should return validation error for empty or whitespace-only query', async () => {
      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: '   '
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });

    it('should return validation error for missing query', async () => {
      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({})
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });

    it('should enforce maximum text length per message (32,000 characters)', async () => {
      const longQuery = 'a'.repeat(32001);

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: longQuery
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
      expect(data.error).toContain('32,000');
    });

    it('should place developer messages before user messages', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research AI',
          developerInstructions: 'Be thorough'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      const developerIndex = requestBody.input.findIndex((m: { role: string }) => m.role === 'developer');
      const userIndex = requestBody.input.findIndex((m: { role: string }) => m.role === 'user');

      expect(developerIndex).toBeLessThan(userIndex);
    });
  });

  // REQ_000.3: Configure reasoning summary options
  describe('REQ_000.3: Reasoning summary options', () => {
    it('should include reasoning object with summary field set to auto by default', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.reasoning).toBeDefined();
      expect(requestBody.reasoning.summary).toBe('auto');
    });

    it('should default to detailed reasoning for thorough depth', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          depth: 'thorough'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.reasoning.summary).toBe('detailed');
    });

    it('should default to auto reasoning for quick depth', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          depth: 'quick'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.reasoning.summary).toBe('auto');
    });

    it('should allow user to override default reasoning level', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          depth: 'quick',
          reasoningSummary: 'detailed'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.reasoning.summary).toBe('detailed');
    });

    it('should return validation error for invalid reasoning summary values', async () => {
      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          reasoningSummary: 'invalid_value'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(400);
      expect(data.code).toBe('VALIDATION_ERROR');
    });
  });

  // REQ_000.4: Enable background mode
  describe('REQ_000.4: Background mode', () => {
    it('should include background: true parameter by default', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockBackgroundJobResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic'
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.background).toBe(true);
    });

    it('should return job metadata including unique job ID for background mode', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockBackgroundJobResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(202);
      expect(data.jobId).toBeDefined();
      expect(typeof data.jobId).toBe('string');
    });

    it('should return status URL for background job', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockBackgroundJobResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(data.statusUrl).toBeDefined();
      expect(data.statusUrl).toContain('/api/tools/deep-research/');
      expect(data.statusUrl).toContain('/status');
    });

    it('should support background: false for synchronous execution', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      await POST(request);

      const fetchCall = mockFetch.mock.calls[0];
      const requestBody = JSON.parse(fetchCall[1].body);

      expect(requestBody.background).toBe(false);
    });

    it('should return full result directly for synchronous (non-background) requests', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.text).toBeDefined();
      expect(data.citations).toBeDefined();
    });

    it('should include job metadata with createdAt timestamp and model used', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockBackgroundJobResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(data.createdAt).toBeDefined();
      expect(data.model).toBeDefined();
    });
  });

  // REQ_000.5: Polling mechanism (tested in status route, but verify structure here)
  describe('REQ_000.5: Polling support', () => {
    it('should return status field in background job response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockBackgroundJobResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic'
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(data.status).toBeDefined();
      expect(['pending', 'processing', 'completed', 'failed']).toContain(data.status);
    });
  });

  // Response processing tests
  describe('Response processing', () => {
    it('should extract text from completed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(data.text).toBe('This is a comprehensive research report on the topic.');
    });

    it('should extract citations from completed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(data.citations).toHaveLength(1);
      expect(data.citations[0].url).toBe('https://example.com/source');
    });

    it('should extract reasoning steps from completed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(data.reasoningSteps).toBeDefined();
      expect(Array.isArray(data.reasoningSteps)).toBe(true);
    });

    it('should include usage information when available', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockDeepResearchResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(data.usage).toBeDefined();
      expect(data.usage.inputTokens).toBe(100);
      expect(data.usage.outputTokens).toBe(500);
    });
  });

  // Error handling tests
  describe('Error handling', () => {
    it('should handle network errors', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(502);
      expect(data.code).toBe('NETWORK');
      expect(data.retryable).toBe(true);
    });

    it('should handle API 500 errors as retryable', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        json: async () => ({ error: { message: 'Internal server error' } }),
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.retryable).toBe(true);
    });

    it('should handle API 401 errors as non-retryable', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 401,
        json: async () => ({ error: { message: 'Invalid API key' } }),
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research', {
        method: 'POST',
        body: JSON.stringify({
          query: 'Research topic',
          background: false
        })
      });

      const response = await POST(request);
      const data = await response.json();

      expect(response.status).toBe(401);
      expect(data.code).toBe('INVALID_API_KEY');
      expect(data.retryable).toBe(false);
    });
  });
});
