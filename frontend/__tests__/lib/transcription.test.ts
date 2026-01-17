import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { transcribeAudio, MAX_FILE_SIZE_BYTES, MAX_FILE_SIZE_MB } from '@/lib/transcription'
import { TranscriptionError } from '@/lib/types'

// Mock fetch globally
const mockFetch = vi.fn()
global.fetch = mockFetch

// Helper to setup two-step mock responses (upload + transcribe)
function setupSuccessfulTranscription(text: string, blobUrl = 'https://blob.vercel-storage.com/test-file.webm') {
  // Step 1: Upload response
  mockFetch.mockResolvedValueOnce({
    ok: true,
    json: () => Promise.resolve({ url: blobUrl }),
  })
  // Step 2: Transcribe response
  mockFetch.mockResolvedValueOnce({
    ok: true,
    json: () => Promise.resolve({ text }),
  })
}

describe('transcribeAudio', () => {
  beforeEach(() => {
    vi.clearAllMocks()
  })

  describe('file size validation', () => {
    it('should reject files larger than 25MB', async () => {
      const largeBlob = new Blob([new ArrayBuffer(MAX_FILE_SIZE_BYTES + 1)], { type: 'audio/webm' })

      await expect(transcribeAudio(largeBlob)).rejects.toThrow(TranscriptionError)
      await expect(transcribeAudio(largeBlob)).rejects.toMatchObject({
        code: 'FILE_TOO_LARGE',
        retryable: false,
      })
    })

    it('should accept files at exactly 25MB', async () => {
      const exactBlob = new Blob([new ArrayBuffer(MAX_FILE_SIZE_BYTES)], { type: 'audio/webm' })
      setupSuccessfulTranscription('test transcription')

      await expect(transcribeAudio(exactBlob)).resolves.toBe('test transcription')
    })

    it('should accept files smaller than 25MB', async () => {
      const smallBlob = new Blob(['test audio content'], { type: 'audio/webm' })
      setupSuccessfulTranscription('hello world')

      const result = await transcribeAudio(smallBlob)
      expect(result).toBe('hello world')
    })
  })

  describe('successful transcription', () => {
    it('should POST to /api/upload then /api/transcribe in two-step process', async () => {
      const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })
      setupSuccessfulTranscription('transcribed text')

      await transcribeAudio(audioBlob)

      expect(mockFetch).toHaveBeenCalledTimes(2)
      // Step 1: Upload
      expect(mockFetch).toHaveBeenNthCalledWith(
        1,
        '/api/upload',
        expect.objectContaining({
          method: 'POST',
        })
      )
      // Step 2: Transcribe with blobUrl
      expect(mockFetch).toHaveBeenNthCalledWith(
        2,
        '/api/transcribe',
        expect.objectContaining({
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
        })
      )

      // Verify upload FormData contains file
      const [, uploadOptions] = mockFetch.mock.calls[0]
      expect(uploadOptions.body).toBeInstanceOf(FormData)
      const formData = uploadOptions.body as FormData
      expect(formData.get('file')).toBeInstanceOf(Blob)

      // Verify transcribe body contains blobUrl
      const [, transcribeOptions] = mockFetch.mock.calls[1]
      const transcribeBody = JSON.parse(transcribeOptions.body)
      expect(transcribeBody.blobUrl).toBe('https://blob.vercel-storage.com/test-file.webm')
    })

    it('should return transcription text from response', async () => {
      const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })
      setupSuccessfulTranscription('The quick brown fox jumps over the lazy dog')

      const result = await transcribeAudio(audioBlob)
      expect(result).toBe('The quick brown fox jumps over the lazy dog')
    })

    it('should pass language option to API', async () => {
      const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })
      setupSuccessfulTranscription('transcribed text')

      await transcribeAudio(audioBlob, { language: 'es' })

      // Verify language is included in transcribe request body
      const [, transcribeOptions] = mockFetch.mock.calls[1]
      const transcribeBody = JSON.parse(transcribeOptions.body)
      expect(transcribeBody.language).toBe('es')
    })

    it('should use .webm extension for audio/webm files', async () => {
      const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })
      setupSuccessfulTranscription('transcribed text')

      await transcribeAudio(audioBlob)

      const [, uploadOptions] = mockFetch.mock.calls[0]
      const formData = uploadOptions.body as FormData
      const file = formData.get('file') as File
      expect(file.name).toMatch(/^recording-\d+\.webm$/)
    })

    it('should use .mp4 extension for audio/mp4 files', async () => {
      const audioBlob = new Blob(['test audio'], { type: 'audio/mp4' })
      setupSuccessfulTranscription('transcribed text')

      await transcribeAudio(audioBlob)

      const [, uploadOptions] = mockFetch.mock.calls[0]
      const formData = uploadOptions.body as FormData
      const file = formData.get('file') as File
      expect(file.name).toMatch(/^recording-\d+\.mp4$/)
    })
  })

  describe('error handling', () => {
    describe('upload errors', () => {
      it('should throw UPLOAD_ERROR when upload fails with error response', async () => {
        const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })

        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 500,
          json: () => Promise.resolve({
            error: 'Upload failed',
            code: 'UPLOAD_ERROR',
          }),
        })

        await expect(transcribeAudio(audioBlob)).rejects.toMatchObject({
          code: 'UPLOAD_ERROR',
          retryable: false,
        })
      })

      it('should throw UPLOAD_ERROR with retryable=true on network failure during upload', async () => {
        const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })

        mockFetch.mockRejectedValueOnce(new Error('Network error'))

        await expect(transcribeAudio(audioBlob)).rejects.toMatchObject({
          code: 'UPLOAD_ERROR',
          retryable: true,
        })
      })
    })

    describe('transcription errors', () => {
      it('should throw INVALID_API_KEY error on 401 response from transcribe', async () => {
        const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })

        // Upload succeeds
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({ url: 'https://blob.vercel-storage.com/test.webm' }),
        })
        // Transcribe fails with 401
        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 401,
          json: () => Promise.resolve({
            error: 'Invalid API key',
            code: 'INVALID_API_KEY',
            retryable: false
          }),
        })

        await expect(transcribeAudio(audioBlob)).rejects.toMatchObject({
          code: 'INVALID_API_KEY',
          retryable: false,
        })
      })

      it('should throw NETWORK error on network failure during transcribe', async () => {
        const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })

        // Upload succeeds
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({ url: 'https://blob.vercel-storage.com/test.webm' }),
        })
        // Transcribe fails with network error
        mockFetch.mockRejectedValueOnce(new Error('Network error'))

        await expect(transcribeAudio(audioBlob)).rejects.toMatchObject({
          code: 'NETWORK',
          retryable: true,
        })
      })

      it('should throw API_ERROR on other API errors from transcribe', async () => {
        const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })

        // Upload succeeds
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({ url: 'https://blob.vercel-storage.com/test.webm' }),
        })
        // Transcribe fails with 400
        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 400,
          json: () => Promise.resolve({
            error: 'Bad request',
            code: 'API_ERROR',
            retryable: false
          }),
        })

        await expect(transcribeAudio(audioBlob)).rejects.toMatchObject({
          code: 'API_ERROR',
          retryable: false,
        })
      })

      it('should handle error responses with retryable flag from transcribe', async () => {
        const audioBlob = new Blob(['test audio'], { type: 'audio/webm' })

        // Upload succeeds
        mockFetch.mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve({ url: 'https://blob.vercel-storage.com/test.webm' }),
        })
        // Transcribe fails with 429
        mockFetch.mockResolvedValueOnce({
          ok: false,
          status: 429,
          json: () => Promise.resolve({
            error: 'Rate limit exceeded',
            code: 'RATE_LIMIT',
            retryable: true
          }),
        })

        await expect(transcribeAudio(audioBlob)).rejects.toMatchObject({
          code: 'RATE_LIMIT',
          retryable: true,
        })
      })
    })
  })
})

describe('constants', () => {
  it('should export MAX_FILE_SIZE_MB as 25', () => {
    expect(MAX_FILE_SIZE_MB).toBe(25)
  })

  it('should export MAX_FILE_SIZE_BYTES as 25 * 1024 * 1024', () => {
    expect(MAX_FILE_SIZE_BYTES).toBe(25 * 1024 * 1024)
  })
})
