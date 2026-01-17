import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { POST } from '@/app/api/transcribe/route'
import { NextRequest } from 'next/server'

// Create mock functions using vi.hoisted to avoid hoisting issues
const { mockCreate, mockToFile, mockDel, mockFetch } = vi.hoisted(() => {
  return {
    mockCreate: vi.fn(),
    mockToFile: vi.fn((data: Uint8Array, filename: string, options: any) => {
      // Return a mock file object that includes the data for verification
      return Promise.resolve({
        name: filename,
        type: options.type,
        size: data.length,
        arrayBuffer: async () => data.buffer,
      })
    }),
    mockDel: vi.fn(),
    mockFetch: vi.fn(),
  }
})

// Mock the OpenAI module
vi.mock('openai', () => {
  return {
    default: class MockOpenAI {
      audio = {
        transcriptions: {
          create: mockCreate,
        },
      }
    },
  }
})

// Mock openai/uploads module
vi.mock('openai/uploads', () => {
  return {
    toFile: mockToFile,
  }
})

// Mock @vercel/blob
vi.mock('@vercel/blob', () => {
  return {
    del: mockDel,
  }
})

// Helper to create a request with JSON body
function createRequest(body: Record<string, unknown>): NextRequest {
  return new NextRequest('http://localhost:3000/api/transcribe', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify(body),
  })
}

// Helper to setup mock fetch for blob retrieval
function setupBlobFetch(
  contentType: string,
  size: number = 1000,
  ok: boolean = true
) {
  const buffer = new ArrayBuffer(size)
  mockFetch.mockResolvedValueOnce({
    ok,
    status: ok ? 200 : 500,
    headers: new Map([['content-type', contentType]]),
    arrayBuffer: () => Promise.resolve(buffer),
  })
}

describe('POST /api/transcribe', () => {
  const originalFetch = global.fetch

  beforeEach(() => {
    vi.clearAllMocks()
    // Clear environment
    delete process.env.OPENAI_API_KEY
    delete process.env.BLOB_READ_WRITE_TOKEN
    // Replace global fetch with mock
    global.fetch = mockFetch
  })

  afterEach(() => {
    global.fetch = originalFetch
  })

  describe('validation', () => {
    it('should return 400 if no blob URL is provided', async () => {
      const request = createRequest({})

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data).toMatchObject({
        error: 'No blob URL provided',
        code: 'NO_BLOB_URL',
      })
    })

    it('should return 500 if OPENAI_API_KEY is not configured', async () => {
      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/test.webm',
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('CONFIG_ERROR')
      expect(data.retryable).toBe(false)
    })

    it('should return 400 if file type is unsupported', async () => {
      process.env.OPENAI_API_KEY = 'sk-test-key-123'

      setupBlobFetch('text/plain')

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/test.txt',
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data.code).toBe('UNSUPPORTED_FILE_TYPE')
      expect(data.retryable).toBe(false)
    })

    it('should return 400 if file exceeds 25MB', async () => {
      process.env.OPENAI_API_KEY = 'sk-test-key-123'

      // Setup blob fetch with 26MB file
      setupBlobFetch('audio/webm', 26 * 1024 * 1024)

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/large.webm',
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data.code).toBe('FILE_TOO_LARGE')
      expect(data.retryable).toBe(false)
    })
  })

  describe('successful transcription', () => {
    beforeEach(() => {
      process.env.OPENAI_API_KEY = 'sk-test-key-123'
      process.env.BLOB_READ_WRITE_TOKEN = 'test-blob-token'
    })

    it('should call OpenAI API with correct parameters', async () => {
      setupBlobFetch('audio/webm')

      mockCreate.mockResolvedValueOnce({
        text: 'This is the transcribed text',
      })

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data).toEqual({ text: 'This is the transcribed text' })
      expect(mockCreate).toHaveBeenCalledWith(
        expect.objectContaining({
          model: 'whisper-1',
          file: expect.objectContaining({
            type: 'audio/webm',
          }),
        })
      )
    })

    it('should pass language parameter to OpenAI', async () => {
      setupBlobFetch('audio/webm')

      mockCreate.mockResolvedValueOnce({
        text: 'Texto transcrito',
      })

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
        language: 'es',
      })

      await POST(request)

      expect(mockCreate).toHaveBeenCalledWith(
        expect.objectContaining({
          model: 'whisper-1',
          language: 'es',
        })
      )
    })

    it('should handle mp3 files correctly', async () => {
      setupBlobFetch('audio/mpeg')

      mockCreate.mockResolvedValueOnce({
        text: 'Transcribed from mp3',
      })

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.mp3',
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data).toEqual({ text: 'Transcribed from mp3' })
      expect(mockCreate).toHaveBeenCalledWith(
        expect.objectContaining({
          file: expect.objectContaining({
            type: 'audio/mpeg',
          }),
        })
      )
    })

    it('should handle m4a files correctly', async () => {
      setupBlobFetch('audio/mp4')

      mockCreate.mockResolvedValueOnce({
        text: 'Transcribed from m4a',
      })

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.m4a',
      })

      const response = await POST(request)

      expect(response.status).toBe(200)
      expect(mockCreate).toHaveBeenCalledWith(
        expect.objectContaining({
          file: expect.objectContaining({
            type: 'audio/mp4',
          }),
        })
      )
    })

    it('should delete blob after successful transcription', async () => {
      setupBlobFetch('audio/webm')

      mockCreate.mockResolvedValueOnce({
        text: 'Transcribed text',
      })

      const blobUrl = 'https://blob.vercel-storage.com/recording.webm'
      const request = createRequest({ blobUrl })

      await POST(request)

      expect(mockDel).toHaveBeenCalledWith(blobUrl, {
        token: 'test-blob-token',
      })
    })
  })

  describe('OpenAI API error handling', () => {
    beforeEach(() => {
      process.env.OPENAI_API_KEY = 'sk-test-key-123'
      process.env.BLOB_READ_WRITE_TOKEN = 'test-blob-token'
      vi.useFakeTimers()
    })

    afterEach(() => {
      vi.useRealTimers()
    })

    it('should return 401 on invalid API key (non-retryable)', async () => {
      setupBlobFetch('audio/webm')

      const apiError = {
        status: 401,
        message: 'Invalid authentication',
      }
      mockCreate.mockRejectedValueOnce(apiError)

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(401)
      expect(data.code).toBe('INVALID_API_KEY')
      expect(data.retryable).toBe(false)
      // Should not retry on non-retryable errors
      expect(mockCreate).toHaveBeenCalledTimes(1)
    })

    it('should return 429 on rate limit error after max retries', async () => {
      setupBlobFetch('audio/webm')

      const apiError = {
        status: 429,
        message: 'Rate limit exceeded',
      }
      // All calls fail with rate limit
      mockCreate.mockRejectedValue(apiError)

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const responsePromise = POST(request)

      // Fast-forward through all retries: 10s + 20s + 40s
      await vi.advanceTimersByTimeAsync(10000)
      await vi.advanceTimersByTimeAsync(20000)
      await vi.advanceTimersByTimeAsync(40000)

      const response = await responsePromise
      const data = await response.json()

      expect(response.status).toBe(429)
      expect(data.code).toBe('RATE_LIMIT')
      expect(data.retryable).toBe(true)
      // Initial call + 3 retries
      expect(mockCreate).toHaveBeenCalledTimes(4)
    })

    it('should return 500 on OpenAI server error after max retries', async () => {
      setupBlobFetch('audio/webm')

      const apiError = {
        status: 503,
        message: 'Service unavailable',
      }
      // All calls fail with server error
      mockCreate.mockRejectedValue(apiError)

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const responsePromise = POST(request)

      // Fast-forward through all retries: 2s + 4s + 8s
      await vi.advanceTimersByTimeAsync(2000)
      await vi.advanceTimersByTimeAsync(4000)
      await vi.advanceTimersByTimeAsync(8000)

      const response = await responsePromise
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('API_ERROR')
      expect(data.retryable).toBe(true)
      // Initial call + 3 retries
      expect(mockCreate).toHaveBeenCalledTimes(4)
    })

    it('should handle network errors after max retries', async () => {
      setupBlobFetch('audio/webm')

      mockCreate.mockRejectedValue(new Error('Connection refused'))

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const responsePromise = POST(request)

      // Fast-forward through all retries: 2s + 4s + 8s
      await vi.advanceTimersByTimeAsync(2000)
      await vi.advanceTimersByTimeAsync(4000)
      await vi.advanceTimersByTimeAsync(8000)

      const response = await responsePromise
      const data = await response.json()

      expect(response.status).toBe(502)
      expect(data.code).toBe('NETWORK')
      expect(data.retryable).toBe(true)
      // Initial call + 3 retries
      expect(mockCreate).toHaveBeenCalledTimes(4)
    })

    it('should clean up blob even on error', async () => {
      setupBlobFetch('audio/webm')

      mockCreate.mockRejectedValueOnce({ status: 401, message: 'Invalid key' })

      const blobUrl = 'https://blob.vercel-storage.com/recording.webm'
      const request = createRequest({ blobUrl })

      await POST(request)

      expect(mockDel).toHaveBeenCalledWith(blobUrl, {
        token: 'test-blob-token',
      })
    })
  })

  describe('retry logic integration', () => {
    beforeEach(() => {
      process.env.OPENAI_API_KEY = 'sk-test-key-123'
      process.env.BLOB_READ_WRITE_TOKEN = 'test-blob-token'
      vi.useFakeTimers()
    })

    afterEach(() => {
      vi.useRealTimers()
    })

    it('should retry on rate limit and succeed', async () => {
      setupBlobFetch('audio/webm')

      // First call fails with rate limit, second succeeds
      mockCreate
        .mockRejectedValueOnce({ status: 429, message: 'Rate limit' })
        .mockResolvedValueOnce({ text: 'Success after retry' })

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const responsePromise = POST(request)

      // Fast-forward through the retry delay (10 seconds for rate limit)
      await vi.advanceTimersByTimeAsync(10000)

      const response = await responsePromise
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data.text).toBe('Success after retry')
      expect(mockCreate).toHaveBeenCalledTimes(2)
    })

    it('should retry on server errors and succeed', async () => {
      setupBlobFetch('audio/webm')

      // First call fails with server error, second succeeds
      mockCreate
        .mockRejectedValueOnce({ status: 500, message: 'Internal server error' })
        .mockResolvedValueOnce({ text: 'Success after retry' })

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const responsePromise = POST(request)

      // Fast-forward through the retry delay (2 seconds for network errors)
      await vi.advanceTimersByTimeAsync(2000)

      const response = await responsePromise
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data.text).toBe('Success after retry')
      expect(mockCreate).toHaveBeenCalledTimes(2)
    })

    it('should fail after max retries', async () => {
      setupBlobFetch('audio/webm')

      // All calls fail
      mockCreate.mockRejectedValue({ status: 429, message: 'Rate limit' })

      const request = createRequest({
        blobUrl: 'https://blob.vercel-storage.com/recording.webm',
      })

      const responsePromise = POST(request)

      // Fast-forward through all retries: 10s + 20s + 40s
      await vi.advanceTimersByTimeAsync(10000) // First retry
      await vi.advanceTimersByTimeAsync(20000) // Second retry
      await vi.advanceTimersByTimeAsync(40000) // Third retry

      const response = await responsePromise
      const data = await response.json()

      expect(response.status).toBe(429)
      expect(data.code).toBe('RATE_LIMIT')
      // Initial call + 3 retries = 4 total calls
      expect(mockCreate).toHaveBeenCalledTimes(4)
    })
  })
})
