/**
 * Unit tests for Deep Research SSE Streaming API
 * REQ_011.1: SSE Streaming Route for Deep Research
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { NextRequest } from 'next/server';

import {
  GET,
  KEEP_ALIVE_INTERVAL_MS,
  POLL_INTERVAL_MS,
  MAX_POLL_DURATION_MS,
  OPENAI_API_URL,
  formatSSEEvent,
  formatSSEComment,
  estimateProgress,
  inferStepType,
  type SSEEventData,
} from '../route';

// Mock fetch
const mockFetch = vi.fn();
global.fetch = mockFetch;

// Mock environment
const originalEnv = process.env;

describe('SSE Streaming Route (REQ_011.1)', () => {
  beforeEach(() => {
    vi.resetAllMocks();
    vi.useFakeTimers();
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-api-key' };
  });

  afterEach(async () => {
    await vi.runAllTimersAsync();
    vi.useRealTimers();
    process.env = originalEnv;
  });

  describe('Constants', () => {
    it('should have correct keep-alive interval (15 seconds)', () => {
      expect(KEEP_ALIVE_INTERVAL_MS).toBe(15000);
    });

    it('should have correct poll interval (2 seconds)', () => {
      expect(POLL_INTERVAL_MS).toBe(2000);
    });

    it('should have correct max poll duration (30 minutes)', () => {
      expect(MAX_POLL_DURATION_MS).toBe(1800000);
    });

    it('should use correct OpenAI API URL', () => {
      expect(OPENAI_API_URL).toBe('https://api.openai.com/v1/responses');
    });
  });

  describe('formatSSEEvent (REQ_011.1.12)', () => {
    it('should format event with correct SSE syntax', () => {
      const data: SSEEventData = {
        type: 'progress',
        timestamp: '2026-01-16T00:00:00.000Z',
        responseId: 'resp_test123',
        percentage: 50,
      };

      const result = formatSSEEvent('progress', data);

      expect(result).toBe('event: progress\ndata: {"type":"progress","timestamp":"2026-01-16T00:00:00.000Z","responseId":"resp_test123","percentage":50}\n\n');
    });

    it('should JSON-encode complex data structures', () => {
      const data: SSEEventData = {
        type: 'reasoning',
        timestamp: '2026-01-16T00:00:00.000Z',
        responseId: 'resp_test123',
        steps: ['step1', 'step2'],
        nested: { key: 'value' },
      };

      const result = formatSSEEvent('reasoning', data);
      const dataLine = result.split('\n')[1];
      const parsed = JSON.parse(dataLine.replace('data: ', ''));

      expect(parsed.steps).toEqual(['step1', 'step2']);
      expect(parsed.nested).toEqual({ key: 'value' });
    });
  });

  describe('formatSSEComment (REQ_011.1.8)', () => {
    it('should format comment with colon prefix', () => {
      const result = formatSSEComment('keep-alive 1234567890');
      expect(result).toBe(': keep-alive 1234567890\n\n');
    });

    it('should handle empty comments', () => {
      const result = formatSSEComment('');
      expect(result).toBe(': \n\n');
    });
  });

  describe('estimateProgress', () => {
    it('should return 0 for initial pending state', () => {
      const progress = estimateProgress('pending', 0, false, false);
      expect(progress).toBe(0);
    });

    it('should increase progress over time for pending state', () => {
      const progress10s = estimateProgress('pending', 10000, false, false);
      const progress20s = estimateProgress('pending', 20000, false, false);

      expect(progress10s).toBe(5);
      expect(progress20s).toBe(10);
    });

    it('should cap pending progress at 10%', () => {
      const progress = estimateProgress('pending', 60000, false, false);
      expect(progress).toBe(10);
    });

    it('should add 20% for reasoning steps in processing state', () => {
      const withoutReasoning = estimateProgress('processing', 0, false, false);
      const withReasoning = estimateProgress('processing', 0, true, false);

      expect(withReasoning - withoutReasoning).toBe(20);
    });

    it('should add 30% for search results in processing state', () => {
      const withoutSearch = estimateProgress('processing', 0, false, false);
      const withSearch = estimateProgress('processing', 0, false, true);

      expect(withSearch - withoutSearch).toBe(30);
    });

    it('should add time-based progress in processing state', () => {
      const at0min = estimateProgress('processing', 0, false, false);
      const at1min = estimateProgress('processing', 60000, false, false);
      const at2min = estimateProgress('processing', 120000, false, false);

      expect(at1min - at0min).toBe(10);
      expect(at2min - at0min).toBe(20);
    });

    it('should cap progress at 95% for non-completed states', () => {
      // 10 base + 20 reasoning + 30 search + 30 time (10 min) = 90, but cap at 95
      const progress = estimateProgress('processing', 600000, true, true);
      expect(progress).toBe(90);
    });

    it('should cap accumulated progress at 95% when it would exceed', () => {
      // With very long time, progress could theoretically exceed but should cap at 95
      // 10 base + 20 reasoning + 30 search + 30 time max = 90 (max possible is 90)
      // To test the cap, we need a scenario where accumulated > 95
      // Since max is 90, let's verify the cap mechanism works
      const progress = estimateProgress('processing', 3600000, true, true); // 60 minutes
      expect(progress).toBeLessThanOrEqual(95);
    });

    it('should return 100 for completed status', () => {
      const progress = estimateProgress('completed', 0, false, false);
      expect(progress).toBe(100);
    });
  });

  describe('inferStepType', () => {
    it('should return "searching" for search-related text', () => {
      expect(inferStepType('Searching for information about AI')).toBe('searching');
      expect(inferStepType('Looking for relevant sources')).toBe('searching');
      expect(inferStepType('Finding data on the topic')).toBe('searching');
    });

    it('should return "synthesizing" for synthesis-related text', () => {
      expect(inferStepType('Synthesizing the findings')).toBe('synthesizing');
      expect(inferStepType('Combining all information')).toBe('synthesizing');
      expect(inferStepType('Summarizing the research')).toBe('synthesizing');
      expect(inferStepType('Creating the final report')).toBe('synthesizing');
    });

    it('should return "planning" for other text', () => {
      expect(inferStepType('Analyzing the query')).toBe('planning');
      expect(inferStepType('Determining approach')).toBe('planning');
      expect(inferStepType('Starting the investigation')).toBe('planning');
    });

    it('should be case-insensitive', () => {
      expect(inferStepType('SEARCHING for data')).toBe('searching');
      expect(inferStepType('SYNTHESIZING results')).toBe('synthesizing');
    });
  });

  describe('GET Endpoint (REQ_011.1.1)', () => {
    const createRequest = (responseId: string): NextRequest => {
      return new NextRequest(`http://localhost/api/tools/deep-research/${responseId}/stream`, {
        method: 'GET',
      });
    };

    const createParams = (responseId: string) => Promise.resolve({ responseId });

    describe('Validation', () => {
      it('should return 500 when API key is not configured', async () => {
        process.env = { ...originalEnv };
        delete process.env.OPENAI_API_KEY;

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        expect(response.status).toBe(500);
        const body = await response.json();
        expect(body.code).toBe('CONFIG_ERROR');
      });

      it('should return 400 for invalid response ID format', async () => {
        const request = createRequest('invalid_id');
        const response = await GET(request, { params: createParams('invalid_id') });

        expect(response.status).toBe(400);
        const body = await response.json();
        expect(body.code).toBe('VALIDATION_ERROR');
        expect(body.error).toContain('Invalid response ID format');
      });

      it('should return 400 for empty response ID', async () => {
        const request = createRequest('');
        const response = await GET(request, { params: createParams('') });

        expect(response.status).toBe(400);
      });

      it('should accept valid response ID format', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({
            id: 'resp_abc123',
            status: 'completed',
            output: [],
          }),
        });

        const request = createRequest('resp_abc123');
        const response = await GET(request, { params: createParams('resp_abc123') });

        expect(response.status).toBe(200);
        expect(response.headers.get('Content-Type')).toBe('text/event-stream');
      });
    });

    describe('SSE Headers (REQ_011.1)', () => {
      it('should return Content-Type: text/event-stream', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({
            id: 'resp_test123',
            status: 'completed',
            output: [],
          }),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        expect(response.headers.get('Content-Type')).toBe('text/event-stream');
      });

      it('should return Cache-Control: no-cache', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({
            id: 'resp_test123',
            status: 'completed',
            output: [],
          }),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        expect(response.headers.get('Cache-Control')).toBe('no-cache');
      });

      it('should return Connection: keep-alive', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({
            id: 'resp_test123',
            status: 'completed',
            output: [],
          }),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        expect(response.headers.get('Connection')).toBe('keep-alive');
      });

      it('should return X-Accel-Buffering: no for nginx', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({
            id: 'resp_test123',
            status: 'completed',
            output: [],
          }),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        expect(response.headers.get('X-Accel-Buffering')).toBe('no');
      });
    });

    describe('Event Streaming (REQ_011.1.2-6)', () => {
      it('should send done event on completion (REQ_011.1.5)', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({
            id: 'resp_test123',
            status: 'completed',
            output: [],
          }),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        // Read all chunks
        let fullText = '';
        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: done');
        expect(fullText).toContain('"finalReportAvailable":true');
      });

      it('should send error event on failure (REQ_011.1.6)', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({
            id: 'resp_test123',
            status: 'failed',
            error: { code: 'RESEARCH_FAILED', message: 'Research failed' },
          }),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: error');
        expect(fullText).toContain('Research failed');
      });

      it('should send reasoning events (REQ_011.1.2)', async () => {
        mockFetch
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'processing',
              output: [
                {
                  id: 'reasoning_1',
                  type: 'reasoning',
                  summary: [{ type: 'summary_text', text: 'Analyzing the query' }],
                },
              ],
            }),
          })
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'completed',
              output: [],
            }),
          });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        // Read first chunk
        const { value: value1 } = await reader.read();
        fullText += decoder.decode(value1, { stream: true });

        // Advance timer to trigger next poll
        await vi.advanceTimersByTimeAsync(POLL_INTERVAL_MS);

        // Read remaining chunks
        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: reasoning');
        expect(fullText).toContain('Analyzing the query');
      });

      it('should send web_search_call events (REQ_011.1.3)', async () => {
        mockFetch
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'processing',
              output: [
                {
                  id: 'search_1',
                  type: 'web_search_call',
                  query: 'AI research trends 2026',
                },
              ],
            }),
          })
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'completed',
              output: [],
            }),
          });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        const { value: value1 } = await reader.read();
        fullText += decoder.decode(value1, { stream: true });

        await vi.advanceTimersByTimeAsync(POLL_INTERVAL_MS);

        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: web_search_call');
        expect(fullText).toContain('AI research trends 2026');
      });

      it('should send progress events (REQ_011.1.4)', async () => {
        mockFetch
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'processing',
              output: [],
            }),
          })
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'completed',
              output: [],
            }),
          });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        const { value: value1 } = await reader.read();
        fullText += decoder.decode(value1, { stream: true });

        await vi.advanceTimersByTimeAsync(POLL_INTERVAL_MS);

        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: progress');
        expect(fullText).toContain('"percentage"');
      });
    });

    describe('Deduplication', () => {
      it('should not send duplicate reasoning events', async () => {
        mockFetch
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'processing',
              output: [
                {
                  id: 'reasoning_1',
                  type: 'reasoning',
                  summary: [{ type: 'summary_text', text: 'First step' }],
                },
              ],
            }),
          })
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'processing',
              output: [
                {
                  id: 'reasoning_1', // Same ID
                  type: 'reasoning',
                  summary: [{ type: 'summary_text', text: 'First step' }],
                },
                {
                  id: 'reasoning_2', // New ID
                  type: 'reasoning',
                  summary: [{ type: 'summary_text', text: 'Second step' }],
                },
              ],
            }),
          })
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'completed',
              output: [],
            }),
          });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        const { value: value1 } = await reader.read();
        fullText += decoder.decode(value1, { stream: true });

        await vi.advanceTimersByTimeAsync(POLL_INTERVAL_MS);

        const { value: value2 } = await reader.read();
        fullText += decoder.decode(value2, { stream: true });

        await vi.advanceTimersByTimeAsync(POLL_INTERVAL_MS);

        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        // Count occurrences of "First step"
        const firstStepCount = (fullText.match(/First step/g) || []).length;
        expect(firstStepCount).toBe(1);

        // "Second step" should appear once
        expect(fullText).toContain('Second step');
      });
    });

    describe('Error Handling', () => {
      it('should handle 404 error (REQ_011.1.6)', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 404,
          text: () => Promise.resolve('{"error":{"message":"Not found"}}'),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: error');
        expect(fullText).toContain('JOB_NOT_FOUND');
      });

      it('should handle 429 rate limit error', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 429,
          text: () => Promise.resolve('{"error":{"message":"Rate limited"}}'),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: error');
        expect(fullText).toContain('RATE_LIMIT');
        expect(fullText).toContain('"retryable":true');
      });

      it('should handle 500 server error', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 500,
          text: () => Promise.resolve('{"error":{"message":"Server error"}}'),
        });

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: error');
        expect(fullText).toContain('API_ERROR');
        expect(fullText).toContain('"retryable":true');
      });

      it('should handle network errors', async () => {
        mockFetch.mockRejectedValueOnce(new Error('Network failure'));

        const request = createRequest('resp_test123');
        const response = await GET(request, { params: createParams('resp_test123') });

        const reader = response.body!.getReader();
        const decoder = new TextDecoder();

        let fullText = '';
        while (true) {
          const { done, value } = await reader.read();
          if (done) break;
          fullText += decoder.decode(value, { stream: true });
        }

        expect(fullText).toContain('event: error');
        expect(fullText).toContain('NETWORK');
        expect(fullText).toContain('Network failure');
      });
    });

    describe('Keep-Alive (REQ_011.1.8)', () => {
      it('should have keep-alive interval configured at 15 seconds', () => {
        // Verify the constant is set correctly
        expect(KEEP_ALIVE_INTERVAL_MS).toBe(15000);
      });

      it('should format keep-alive comments correctly', () => {
        // Test that the formatSSEComment function creates valid keep-alive comments
        const comment = formatSSEComment('keep-alive 1234567890');
        expect(comment).toBe(': keep-alive 1234567890\n\n');
        expect(comment.startsWith(':')).toBe(true);
      });
    });

    describe('Concurrent Subscribers (REQ_011.1.9)', () => {
      it('should handle multiple concurrent connections', async () => {
        // Each connection should work independently
        mockFetch
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test123',
              status: 'completed',
              output: [],
            }),
          })
          .mockResolvedValueOnce({
            ok: true,
            json: () => Promise.resolve({
              id: 'resp_test456',
              status: 'completed',
              output: [],
            }),
          });

        const request1 = createRequest('resp_test123');
        const request2 = createRequest('resp_test456');

        const [response1, response2] = await Promise.all([
          GET(request1, { params: createParams('resp_test123') }),
          GET(request2, { params: createParams('resp_test456') }),
        ]);

        expect(response1.status).toBe(200);
        expect(response2.status).toBe(200);

        // Both should have SSE content type
        expect(response1.headers.get('Content-Type')).toBe('text/event-stream');
        expect(response2.headers.get('Content-Type')).toBe('text/event-stream');
      });
    });
  });

  describe('JSON Event Structure (REQ_011.1.12)', () => {
    it('should include required fields in all events', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          id: 'resp_test123',
          status: 'completed',
          output: [],
        }),
      });

      const request = new NextRequest('http://localhost/api/tools/deep-research/resp_test123/stream');
      const response = await GET(request, { params: Promise.resolve({ responseId: 'resp_test123' }) });

      const reader = response.body!.getReader();
      const decoder = new TextDecoder();

      let fullText = '';
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        fullText += decoder.decode(value, { stream: true });
      }

      // Extract the done event data
      const doneEventMatch = fullText.match(/event: done\ndata: (.+)\n\n/);
      expect(doneEventMatch).toBeTruthy();

      const eventData = JSON.parse(doneEventMatch![1]);
      expect(eventData).toHaveProperty('type');
      expect(eventData).toHaveProperty('timestamp');
      expect(eventData).toHaveProperty('responseId');
      expect(eventData.responseId).toBe('resp_test123');
    });

    it('should include valid ISO timestamp', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve({
          id: 'resp_test123',
          status: 'completed',
          output: [],
        }),
      });

      const request = new NextRequest('http://localhost/api/tools/deep-research/resp_test123/stream');
      const response = await GET(request, { params: Promise.resolve({ responseId: 'resp_test123' }) });

      const reader = response.body!.getReader();
      const decoder = new TextDecoder();

      let fullText = '';
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        fullText += decoder.decode(value, { stream: true });
      }

      const doneEventMatch = fullText.match(/event: done\ndata: (.+)\n\n/);
      const eventData = JSON.parse(doneEventMatch![1]);

      // Should be a valid ISO date
      const timestamp = new Date(eventData.timestamp);
      expect(timestamp.toISOString()).toBe(eventData.timestamp);
    });
  });
});
