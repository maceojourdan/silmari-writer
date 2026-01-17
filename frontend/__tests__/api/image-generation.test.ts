import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { NextRequest } from 'next/server'

// Create mock functions using vi.hoisted to ensure they are hoisted above mocks
const { mockPut } = vi.hoisted(() => {
  return {
    mockPut: vi.fn(),
  }
})

// Mock @vercel/blob - must be at top level before any imports
vi.mock('@vercel/blob', () => ({
  put: mockPut,
}))

// Mock global fetch
const mockFetch = vi.fn()
global.fetch = mockFetch

describe('POST /api/tools/image-generation', () => {
  let POST: (request: NextRequest) => Promise<Response>
  const originalEnv = process.env

  beforeEach(async () => {
    vi.clearAllMocks()
    vi.resetModules()
    process.env = {
      ...originalEnv,
      OPENAI_API_KEY: 'test-api-key-123',
      BLOB_READ_WRITE_TOKEN: 'test-blob-token',
    }

    // Reset mocks
    mockFetch.mockReset()
    mockPut.mockReset()

    // Dynamically import after mocks are set up
    const module = await import('@/app/api/tools/image-generation/route')
    POST = module.POST
  })

  afterEach(() => {
    process.env = originalEnv
  })

  // Helper to create test request
  const createRequest = (body: Record<string, unknown>) => {
    return new NextRequest('http://localhost:3000/api/tools/image-generation', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(body),
    })
  }

  // Helper to create valid base64 PNG (smallest valid PNG)
  const createValidBase64PNG = () => {
    // PNG magic bytes: 89 50 4E 47 0D 0A 1A 0A followed by minimal chunks
    const pngHeader = new Uint8Array([
      0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a,
      // IHDR chunk (minimal)
      0x00, 0x00, 0x00, 0x0d, 0x49, 0x48, 0x44, 0x52,
      0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
      0x08, 0x02, 0x00, 0x00, 0x00, 0x90, 0x77, 0x53,
      0xde,
      // IDAT chunk (minimal)
      0x00, 0x00, 0x00, 0x0c, 0x49, 0x44, 0x41, 0x54,
      0x08, 0xd7, 0x63, 0xf8, 0x0f, 0x00, 0x00, 0x01,
      0x01, 0x00, 0x05, 0xfe, 0xce, 0x8a,
      // IEND chunk
      0x00, 0x00, 0x00, 0x00, 0x49, 0x45, 0x4e, 0x44,
      0xae, 0x42, 0x60, 0x82,
    ])
    return Buffer.from(pngHeader).toString('base64')
  }

  // Helper for mock OpenAI response
  const createMockOpenAIResponse = (overrides?: Partial<{ data: Array<{ b64_json: string; revised_prompt?: string }> }>) => ({
    created: Date.now(),
    data: [
      {
        b64_json: createValidBase64PNG(),
        revised_prompt: 'A test image prompt',
      },
    ],
    ...overrides,
  })

  describe('REQ_002.1: POST requests to /images/generations', () => {
    describe('request validation', () => {
      it('should return 400 if prompt is missing', async () => {
        const request = createRequest({})
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
        expect(data.error).toContain('prompt')
      })

      it('should return 400 if prompt exceeds 32K characters', async () => {
        const longPrompt = 'a'.repeat(32001)
        const request = createRequest({ prompt: longPrompt })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
        expect(data.error).toContain('32')
      })

      it('should return 500 if OPENAI_API_KEY is not configured', async () => {
        delete process.env.OPENAI_API_KEY

        // Re-import to pick up environment change
        vi.resetModules()
        const module = await import('@/app/api/tools/image-generation/route')
        POST = module.POST

        const request = createRequest({ prompt: 'test' })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(500)
        expect(data.code).toBe('CONFIG_ERROR')
      })

      it('should return 500 if BLOB_READ_WRITE_TOKEN is not configured', async () => {
        delete process.env.BLOB_READ_WRITE_TOKEN

        // Re-import to pick up environment change
        vi.resetModules()
        const module = await import('@/app/api/tools/image-generation/route')
        POST = module.POST

        const request = createRequest({ prompt: 'test' })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(500)
        expect(data.code).toBe('CONFIG_ERROR')
      })
    })

    describe('API request format', () => {
      beforeEach(() => {
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: async () => createMockOpenAIResponse(),
        })
        mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })
      })

      it('should send POST to correct endpoint with auth header', async () => {
        const request = createRequest({ prompt: 'A beautiful sunset' })
        await POST(request)

        expect(mockFetch).toHaveBeenCalledWith(
          'https://api.openai.com/v1/images/generations',
          expect.objectContaining({
            method: 'POST',
            headers: expect.objectContaining({
              'Content-Type': 'application/json',
              'Authorization': 'Bearer test-api-key-123',
            }),
          })
        )
      })

      it('should include required fields in request body', async () => {
        const request = createRequest({ prompt: 'A beautiful sunset' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body).toMatchObject({
          model: 'gpt-image-1.5', // default
          prompt: 'A beautiful sunset',
        })
      })

      it('should use 120 second timeout for image generation', async () => {
        const request = createRequest({ prompt: 'A test image' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const signal = fetchCall[1].signal

        // AbortSignal should be present for timeout
        expect(signal).toBeDefined()
      })
    })

    describe('API error handling', () => {
      beforeEach(() => {
        vi.useFakeTimers()
      })

      afterEach(() => {
        vi.useRealTimers()
      })

      it('should return 401 on invalid API key (non-retryable)', async () => {
        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 401,
          json: async () => ({ error: { message: 'Invalid authentication' } }),
        })

        const request = createRequest({ prompt: 'test' })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(401)
        expect(data.code).toBe('INVALID_API_KEY')
        expect(data.retryable).toBe(false)
        expect(mockFetch).toHaveBeenCalledTimes(1)
      })

      it('should retry on rate limit (429) with exponential backoff', async () => {
        mockFetch
          .mockResolvedValueOnce({
            ok: false,
            status: 429,
            json: async () => ({ error: { message: 'Rate limit exceeded' } }),
          })
          .mockResolvedValueOnce({
            ok: true,
            json: async () => createMockOpenAIResponse(),
          })

        mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

        const request = createRequest({ prompt: 'test' })
        const responsePromise = POST(request)

        // Fast-forward through retry delay (10 seconds base for rate limit)
        await vi.advanceTimersByTimeAsync(10000)

        const response = await responsePromise
        expect(response.status).toBe(200)
        expect(mockFetch).toHaveBeenCalledTimes(2)
      })

      it('should fail after max 3 retries on rate limit', async () => {
        mockFetch.mockResolvedValue({
          ok: false,
          status: 429,
          json: async () => ({ error: { message: 'Rate limit exceeded' } }),
        })

        const request = createRequest({ prompt: 'test' })
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
        expect(mockFetch).toHaveBeenCalledTimes(4) // Initial + 3 retries
      })

      it('should handle network errors with retry', async () => {
        mockFetch
          .mockRejectedValueOnce(new Error('Connection refused'))
          .mockResolvedValueOnce({
            ok: true,
            json: async () => createMockOpenAIResponse(),
          })

        mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

        const request = createRequest({ prompt: 'test' })
        const responsePromise = POST(request)

        // Fast-forward through retry delay (10 seconds base for network)
        await vi.advanceTimersByTimeAsync(10000)

        const response = await responsePromise
        expect(response.status).toBe(200)
        expect(mockFetch).toHaveBeenCalledTimes(2)
      })

      it('should wrap network errors in ToolError format', async () => {
        mockFetch.mockRejectedValue(new Error('Connection refused'))

        const request = createRequest({ prompt: 'test' })
        const responsePromise = POST(request)

        // Fast-forward through all retries
        await vi.advanceTimersByTimeAsync(10000)
        await vi.advanceTimersByTimeAsync(20000)
        await vi.advanceTimersByTimeAsync(40000)

        const response = await responsePromise
        const data = await response.json()

        expect(response.status).toBe(502)
        expect(data.code).toBe('NETWORK')
        expect(data.retryable).toBe(true)
        expect(data.error).toBeDefined()
      })

      it('should log request with truncated prompt for debugging', async () => {
        const consoleSpy = vi.spyOn(console, 'log').mockImplementation(() => {})

        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: async () => createMockOpenAIResponse(),
        })
        mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

        const longPrompt = 'A'.repeat(200)
        const request = createRequest({ prompt: longPrompt })
        await POST(request)

        // Verify logging occurred (implementation will truncate to 100 chars)
        expect(consoleSpy).toHaveBeenCalled()
        consoleSpy.mockRestore()
      })
    })
  })

  describe('REQ_002.2: Model support and deprecation', () => {
    beforeEach(() => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockResolvedValue({ url: 'https://blob.vercel.com/test.png' })
    })

    it('should default to gpt-image-1.5 when no model specified', async () => {
      const request = createRequest({ prompt: 'test' })
      await POST(request)

      const fetchCall = mockFetch.mock.calls[0]
      const body = JSON.parse(fetchCall[1].body)

      expect(body.model).toBe('gpt-image-1.5')
    })

    it('should accept gpt-image-1 model', async () => {
      const request = createRequest({ prompt: 'test', model: 'gpt-image-1' })
      await POST(request)

      const fetchCall = mockFetch.mock.calls[0]
      const body = JSON.parse(fetchCall[1].body)

      expect(body.model).toBe('gpt-image-1')
    })

    it('should accept gpt-image-1-mini model for cost optimization', async () => {
      const request = createRequest({ prompt: 'test', model: 'gpt-image-1-mini' })
      await POST(request)

      const fetchCall = mockFetch.mock.calls[0]
      const body = JSON.parse(fetchCall[1].body)

      expect(body.model).toBe('gpt-image-1-mini')
    })

    it('should reject invalid model values with 400', async () => {
      const request = createRequest({ prompt: 'test', model: 'invalid-model' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data.code).toBe('VALIDATION_ERROR')
      expect(data.error).toContain('model')
    })

    it('should return deprecation warning for dall-e-3', async () => {
      const request = createRequest({ prompt: 'test', model: 'dall-e-3' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data.error).toContain('dall-e-3')
      expect(data.error).toContain('deprecated')
      expect(data.error).toContain('gpt-image-1.5')
    })

    it('should return deprecation warning for dall-e-2', async () => {
      const request = createRequest({ prompt: 'test', model: 'dall-e-2' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data.error).toContain('dall-e-2')
      expect(data.error).toContain('deprecated')
      expect(data.error).toContain('gpt-image-1')
    })
  })

  describe('REQ_002.3: Base64 response handling', () => {
    it('should extract b64_json from response.data[0]', async () => {
      const base64 = createValidBase64PNG()
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: base64 }],
        }),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)

      expect(response.status).toBe(200)
      expect(mockPut).toHaveBeenCalled()
    })

    it('should validate base64 string format', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: '!!!invalid-base64!!!' }],
        }),
      })

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('INVALID_RESPONSE')
    })

    it('should handle multiple images when n > 1', async () => {
      const base64 = createValidBase64PNG()
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [
            { b64_json: base64, revised_prompt: 'Prompt 1' },
            { b64_json: base64, revised_prompt: 'Prompt 2' },
            { b64_json: base64, revised_prompt: 'Prompt 3' },
          ],
        }),
      })
      mockPut
        .mockResolvedValueOnce({ url: 'https://blob.vercel.com/test-0.png' })
        .mockResolvedValueOnce({ url: 'https://blob.vercel.com/test-1.png' })
        .mockResolvedValueOnce({ url: 'https://blob.vercel.com/test-2.png' })

      const request = createRequest({ prompt: 'test', n: 3 })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data.images).toHaveLength(3)
      expect(mockPut).toHaveBeenCalledTimes(3)
    })

    it('should extract revised_prompt if present', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: createValidBase64PNG(), revised_prompt: 'Enhanced prompt by AI' }],
        }),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data.images[0].revisedPrompt).toBe('Enhanced prompt by AI')
    })

    it('should return error when b64_json is empty', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: '' }],
        }),
      })

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('INVALID_RESPONSE')
      expect(data.error).toContain('No image data')
    })

    it('should return error when b64_json is null', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: null }],
        }),
      })

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('INVALID_RESPONSE')
    })

    it('should handle malformed JSON response gracefully', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => { throw new Error('Invalid JSON') },
      })

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('INVALID_RESPONSE')
    })
  })

  describe('REQ_002.4: Base64 to buffer and Vercel Blob storage', () => {
    it('should decode base64 to Buffer correctly', async () => {
      const base64 = createValidBase64PNG()
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: base64 }],
        }),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test' })
      await POST(request)

      // Verify put was called with a Buffer
      expect(mockPut).toHaveBeenCalledWith(
        expect.stringMatching(/generated-image-\d+-0\.png/),
        expect.any(Buffer),
        expect.anything()
      )
    })

    it('should validate PNG magic bytes', async () => {
      const base64 = createValidBase64PNG()
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: base64 }],
        }),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test', output_format: 'png' })
      const response = await POST(request)

      expect(response.status).toBe(200)
    })

    it('should use correct filename pattern', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test' })
      await POST(request)

      // Filename should be: generated-image-{timestamp}-{index}.{format}
      expect(mockPut).toHaveBeenCalledWith(
        expect.stringMatching(/^generated-image-\d+-0\.png$/),
        expect.anything(),
        expect.anything()
      )
    })

    it('should set correct Content-Type for PNG', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test', output_format: 'png' })
      await POST(request)

      expect(mockPut).toHaveBeenCalledWith(
        expect.anything(),
        expect.anything(),
        expect.objectContaining({
          contentType: 'image/png',
        })
      )
    })

    it('should set correct Content-Type for JPEG', async () => {
      // Create a valid JPEG base64
      const jpegHeader = new Uint8Array([0xff, 0xd8, 0xff, 0xe0, 0x00, 0x10, 0x4a, 0x46, 0x49, 0x46, 0x00])
      const jpegBase64 = Buffer.from(jpegHeader).toString('base64')

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [{ b64_json: jpegBase64 }],
        }),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.jpeg' })

      const request = createRequest({ prompt: 'test', output_format: 'jpeg' })
      await POST(request)

      expect(mockPut).toHaveBeenCalledWith(
        expect.anything(),
        expect.anything(),
        expect.objectContaining({
          contentType: 'image/jpeg',
        })
      )
    })

    it('should return UPLOAD_FAILED error when Vercel Blob upload fails', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockRejectedValueOnce(new Error('Upload failed'))

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('UPLOAD_FAILED')
      expect(data.retryable).toBe(true)
    })

    it('should upload multiple images in parallel', async () => {
      const base64 = createValidBase64PNG()
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          created: Date.now(),
          data: [
            { b64_json: base64 },
            { b64_json: base64 },
          ],
        }),
      })
      mockPut
        .mockResolvedValueOnce({ url: 'https://blob.vercel.com/test-0.png' })
        .mockResolvedValueOnce({ url: 'https://blob.vercel.com/test-1.png' })

      const request = createRequest({ prompt: 'test', n: 2 })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data.images).toHaveLength(2)
      expect(data.images[0].url).toBe('https://blob.vercel.com/test-0.png')
      expect(data.images[1].url).toBe('https://blob.vercel.com/test-1.png')
    })

    it('should return permanent blob URL for image display', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/permanent-url.png' })

      const request = createRequest({ prompt: 'test' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data.images[0].url).toBe('https://blob.vercel.com/permanent-url.png')
    })
  })

  describe('REQ_002.5: Parameter support', () => {
    beforeEach(() => {
      mockFetch.mockResolvedValue({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockResolvedValue({ url: 'https://blob.vercel.com/test.png' })
    })

    describe('size parameter', () => {
      it('should accept 1024x1024 (square) and use as default', async () => {
        const request = createRequest({ prompt: 'test' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.size).toBe('1024x1024')
      })

      it('should accept 1536x1024 (landscape)', async () => {
        const request = createRequest({ prompt: 'test', size: '1536x1024' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.size).toBe('1536x1024')
      })

      it('should accept 1024x1536 (portrait)', async () => {
        const request = createRequest({ prompt: 'test', size: '1024x1536' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.size).toBe('1024x1536')
      })

      it('should accept auto size', async () => {
        const request = createRequest({ prompt: 'test', size: 'auto' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.size).toBe('auto')
      })

      it('should reject invalid size values', async () => {
        const request = createRequest({ prompt: 'test', size: '512x512' })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
      })
    })

    describe('quality parameter', () => {
      it('should accept low quality', async () => {
        const request = createRequest({ prompt: 'test', quality: 'low' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.quality).toBe('low')
      })

      it('should accept medium quality', async () => {
        const request = createRequest({ prompt: 'test', quality: 'medium' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.quality).toBe('medium')
      })

      it('should default to high quality', async () => {
        const request = createRequest({ prompt: 'test' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.quality).toBe('high')
      })

      it('should reject invalid quality values', async () => {
        const request = createRequest({ prompt: 'test', quality: 'ultra' })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
      })
    })

    describe('output_format parameter', () => {
      it('should accept png format and use as default', async () => {
        const request = createRequest({ prompt: 'test' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.output_format).toBe('png')
      })

      it('should accept jpeg format', async () => {
        const request = createRequest({ prompt: 'test', output_format: 'jpeg' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.output_format).toBe('jpeg')
      })

      it('should accept webp format', async () => {
        const request = createRequest({ prompt: 'test', output_format: 'webp' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.output_format).toBe('webp')
      })

      it('should reject invalid format values', async () => {
        const request = createRequest({ prompt: 'test', output_format: 'gif' })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
      })
    })

    describe('background parameter', () => {
      it('should accept auto background (default)', async () => {
        const request = createRequest({ prompt: 'test' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.background).toBe('auto')
      })

      it('should accept transparent background', async () => {
        const request = createRequest({ prompt: 'test', background: 'transparent' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.background).toBe('transparent')
      })

      it('should accept opaque background', async () => {
        const request = createRequest({ prompt: 'test', background: 'opaque' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.background).toBe('opaque')
      })

      it('should warn and switch to png when transparent + jpeg requested', async () => {
        const consoleSpy = vi.spyOn(console, 'warn').mockImplementation(() => {})

        const request = createRequest({ prompt: 'test', background: 'transparent', output_format: 'jpeg' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        // Should switch to PNG because JPEG doesn't support transparency
        expect(body.output_format).toBe('png')
        expect(consoleSpy).toHaveBeenCalled()
        consoleSpy.mockRestore()
      })
    })

    describe('n parameter', () => {
      it('should default to 1 image', async () => {
        const request = createRequest({ prompt: 'test' })
        await POST(request)

        const fetchCall = mockFetch.mock.calls[0]
        const body = JSON.parse(fetchCall[1].body)

        expect(body.n).toBe(1)
      })

      it('should accept n up to 10', async () => {
        const base64 = createValidBase64PNG()
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: async () => ({
            created: Date.now(),
            data: Array(10).fill({ b64_json: base64 }),
          }),
        })
        mockPut.mockResolvedValue({ url: 'https://blob.vercel.com/test.png' })

        const request = createRequest({ prompt: 'test', n: 10 })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(200)
        expect(data.images).toHaveLength(10)
      })

      it('should reject n < 1', async () => {
        const request = createRequest({ prompt: 'test', n: 0 })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
      })

      it('should reject n > 10', async () => {
        const request = createRequest({ prompt: 'test', n: 11 })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
      })
    })

    describe('parameter validation with Zod', () => {
      it('should validate all parameters and return descriptive errors', async () => {
        const request = createRequest({
          prompt: 'test',
          model: 'invalid',
          size: 'invalid',
          quality: 'invalid',
          output_format: 'invalid',
          n: 100,
        })
        const response = await POST(request)
        const data = await response.json()

        expect(response.status).toBe(400)
        expect(data.code).toBe('VALIDATION_ERROR')
        // Error message should mention the specific field
        expect(data.error).toBeDefined()
      })
    })
  })

  describe('response format', () => {
    it('should return correct response structure', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test', quality: 'high' })
      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data).toMatchObject({
        images: expect.arrayContaining([
          expect.objectContaining({
            url: expect.any(String),
            format: 'png',
            size: '1024x1024',
            model: 'gpt-image-1.5',
            generatedAt: expect.any(String),
          }),
        ]),
        model: 'gpt-image-1.5',
        quality: 'high',
      })
    })

    it('should include model info in response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => createMockOpenAIResponse(),
      })
      mockPut.mockResolvedValueOnce({ url: 'https://blob.vercel.com/test.png' })

      const request = createRequest({ prompt: 'test', model: 'gpt-image-1-mini' })
      const response = await POST(request)
      const data = await response.json()

      expect(data.model).toBe('gpt-image-1-mini')
      expect(data.images[0].model).toBe('gpt-image-1-mini')
    })
  })
})
