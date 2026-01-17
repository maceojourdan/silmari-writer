import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock response data
const mockCompletedResponse = {
  id: 'job_123',
  object: 'response',
  status: 'completed',
  output: [{
    id: 'msg_001',
    type: 'message',
    role: 'assistant',
    content: [{
      type: 'output_text',
      text: 'Research results here.',
      annotations: [{
        type: 'url_citation',
        url: 'https://example.com',
        title: 'Source',
        start_index: 0,
        end_index: 10
      }]
    }]
  }],
  reasoning: [{
    id: 'r_001',
    type: 'reasoning',
    summary: [{ type: 'summary_text', text: 'Analysis complete.' }]
  }],
  usage: {
    input_tokens: 50,
    output_tokens: 100,
    reasoning_tokens: 75
  }
};

const mockProcessingResponse = {
  id: 'job_123',
  object: 'response',
  status: 'processing',
};

const mockPendingResponse = {
  id: 'job_123',
  object: 'response',
  status: 'pending',
};

const mockFailedResponse = {
  id: 'job_123',
  object: 'response',
  status: 'failed',
  error: {
    code: 'research_failed',
    message: 'Unable to complete research due to rate limiting'
  }
};

// Mock fetch
const mockFetch = vi.fn();
global.fetch = mockFetch;

describe('/api/tools/deep-research/[responseId]/status', () => {
  const originalEnv = process.env;
  let GET: (request: NextRequest, context: { params: Promise<{ responseId: string }> }) => Promise<Response>;

  beforeEach(async () => {
    vi.clearAllMocks();
    vi.resetModules();
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-api-key-123' };
    mockFetch.mockReset();

    const module = await import('@/app/api/tools/deep-research/[responseId]/status/route');
    GET = module.GET;
  });

  afterEach(() => {
    process.env = originalEnv;
  });

  // REQ_000.5: Polling mechanism tests
  describe('REQ_000.5: Polling mechanism', () => {
    it('should return current job status for GET request', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockProcessingResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(response.status).toBe(200);
      expect(data.status).toBe('processing');
    });

    it('should include progress info for processing jobs', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockProcessingResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(data.progress).toBeDefined();
      expect(data.progress.step).toBeDefined();
    });

    it('should return full result for completed jobs', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockCompletedResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(data.status).toBe('completed');
      expect(data.result).toBeDefined();
      expect(data.result.text).toBe('Research results here.');
      expect(data.result.citations).toHaveLength(1);
      expect(data.result.reasoningSteps).toHaveLength(1);
      expect(data.result.usage).toBeDefined();
    });

    it('should return error details for failed jobs', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockFailedResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(data.status).toBe('failed');
      expect(data.error).toBeDefined();
      expect(data.error.code).toBe('research_failed');
      expect(data.error.message).toContain('rate limiting');
    });

    it('should return 404 for non-existent job IDs', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 404,
        json: async () => ({ error: { message: 'Not found' } }),
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/nonexistent_job/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'nonexistent_job' }) });
      const data = await response.json();

      expect(response.status).toBe(404);
      expect(data.code).toBe('JOB_NOT_FOUND');
    });

    it('should return 403 for job IDs belonging to other users', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 403,
        json: async () => ({ error: { message: 'Access denied' } }),
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/other_user_job/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'other_user_job' }) });
      const data = await response.json();

      expect(response.status).toBe(403);
      expect(data.code).toBe('JOB_FORBIDDEN');
    });

    it('should handle network errors during polling', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network failure'));

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(response.status).toBe(502);
      expect(data.code).toBe('NETWORK');
    });

    it('should call OpenAI API with correct job ID in URL', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockPendingResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_abc123/status');

      await GET(request, { params: Promise.resolve({ responseId: 'job_abc123' }) });

      expect(mockFetch).toHaveBeenCalledWith(
        'https://api.openai.com/v1/responses/job_abc123',
        expect.objectContaining({
          method: 'GET',
          headers: expect.objectContaining({
            'Authorization': 'Bearer test-api-key-123'
          })
        })
      );
    });

    it('should return pending status correctly', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockPendingResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(data.status).toBe('pending');
    });
  });

  // Configuration tests
  describe('Configuration', () => {
    it('should return 500 when OPENAI_API_KEY is not configured', async () => {
      delete process.env.OPENAI_API_KEY;
      vi.resetModules();
      const module = await import('@/app/api/tools/deep-research/[responseId]/status/route');

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await module.GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(response.status).toBe(500);
      expect(data.code).toBe('CONFIG_ERROR');
    });
  });

  // Response structure tests
  describe('Response structure', () => {
    it('should include usage information in completed result', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockCompletedResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(data.result.usage).toEqual({
        inputTokens: 50,
        outputTokens: 100,
        reasoningTokens: 75
      });
    });

    it('should extract citations correctly from completed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockCompletedResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(data.result.citations[0]).toEqual({
        type: 'url_citation',
        url: 'https://example.com',
        title: 'Source',
        start_index: 0,
        end_index: 10
      });
    });

    it('should extract reasoning steps correctly from completed response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => mockCompletedResponse,
      });

      const request = new NextRequest('http://localhost:3000/api/tools/deep-research/job_123/status');

      const response = await GET(request, { params: Promise.resolve({ responseId: 'job_123' }) });
      const data = await response.json();

      expect(data.result.reasoningSteps).toHaveLength(1);
      expect(data.result.reasoningSteps[0].id).toBe('r_001');
      expect(data.result.reasoningSteps[0].text).toBe('Analysis complete.');
    });
  });
});
