import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { POST } from '@/app/api/upload/route'
import { NextRequest } from 'next/server'

// Create mock functions using vi.hoisted
const { mockPut } = vi.hoisted(() => {
  return {
    mockPut: vi.fn(),
  }
})

// Mock @vercel/blob
vi.mock('@vercel/blob', () => {
  return {
    put: mockPut,
  }
})

describe('POST /api/upload', () => {
  beforeEach(() => {
    vi.clearAllMocks()
    delete process.env.BLOB_READ_WRITE_TOKEN
  })

  describe('validation', () => {
    it('should return 400 if no file is provided', async () => {
      const formData = new FormData()
      const request = new NextRequest('http://localhost:3000/api/upload', {
        method: 'POST',
        body: formData,
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data).toMatchObject({
        error: 'No file provided',
        code: 'NO_FILE',
      })
    })

    it('should return 400 if file exceeds 25MB', async () => {
      const formData = new FormData()
      const largeFile = new File(
        [new ArrayBuffer(26 * 1024 * 1024)], // 26MB
        'large.webm',
        { type: 'audio/webm' }
      )
      formData.append('file', largeFile)

      const request = new NextRequest('http://localhost:3000/api/upload', {
        method: 'POST',
        body: formData,
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(400)
      expect(data.code).toBe('FILE_TOO_LARGE')
    })

    it('should return 500 if BLOB_READ_WRITE_TOKEN is not configured', async () => {
      const formData = new FormData()
      const file = new File(['test audio'], 'audio.webm', { type: 'audio/webm' })
      formData.append('file', file)

      const request = new NextRequest('http://localhost:3000/api/upload', {
        method: 'POST',
        body: formData,
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('CONFIG_ERROR')
    })
  })

  describe('successful upload', () => {
    beforeEach(() => {
      process.env.BLOB_READ_WRITE_TOKEN = 'test-blob-token'
    })

    it('should upload file to Vercel Blob and return URL', async () => {
      const formData = new FormData()
      const file = new File(['test audio content'], 'recording.webm', {
        type: 'audio/webm',
      })
      formData.append('file', file)

      mockPut.mockResolvedValueOnce({
        url: 'https://blob.vercel-storage.com/recording.webm',
      })

      const request = new NextRequest('http://localhost:3000/api/upload', {
        method: 'POST',
        body: formData,
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(200)
      expect(data).toEqual({
        url: 'https://blob.vercel-storage.com/recording.webm',
      })
    })

    it('should call Vercel Blob put with correct parameters', async () => {
      const formData = new FormData()
      const file = new File(['test audio'], 'recording.webm', {
        type: 'audio/webm',
      })
      formData.append('file', file)

      mockPut.mockResolvedValueOnce({
        url: 'https://blob.vercel-storage.com/recording.webm',
      })

      const request = new NextRequest('http://localhost:3000/api/upload', {
        method: 'POST',
        body: formData,
      })

      await POST(request)

      // Verify put was called with correct options
      expect(mockPut).toHaveBeenCalledTimes(1)
      const [fileName, fileArg, options] = mockPut.mock.calls[0]
      expect(typeof fileName).toBe('string')
      // File type check using duck typing since instanceof doesn't work across environments
      expect(fileArg).toHaveProperty('size')
      expect(fileArg).toHaveProperty('type', 'audio/webm')
      expect(options).toEqual({
        access: 'public',
        token: 'test-blob-token',
      })
    })

    it('should accept files at exactly 25MB', async () => {
      const formData = new FormData()
      const file = new File(
        [new ArrayBuffer(25 * 1024 * 1024)], // exactly 25MB
        'large-but-valid.webm',
        { type: 'audio/webm' }
      )
      formData.append('file', file)

      mockPut.mockResolvedValueOnce({
        url: 'https://blob.vercel-storage.com/large-but-valid.webm',
      })

      const request = new NextRequest('http://localhost:3000/api/upload', {
        method: 'POST',
        body: formData,
      })

      const response = await POST(request)
      expect(response.status).toBe(200)
    })
  })

  describe('error handling', () => {
    beforeEach(() => {
      process.env.BLOB_READ_WRITE_TOKEN = 'test-blob-token'
    })

    it('should return 500 on Vercel Blob upload failure', async () => {
      const formData = new FormData()
      const file = new File(['test audio'], 'recording.webm', {
        type: 'audio/webm',
      })
      formData.append('file', file)

      mockPut.mockRejectedValueOnce(new Error('Blob upload failed'))

      const request = new NextRequest('http://localhost:3000/api/upload', {
        method: 'POST',
        body: formData,
      })

      const response = await POST(request)
      const data = await response.json()

      expect(response.status).toBe(500)
      expect(data.code).toBe('UPLOAD_ERROR')
    })
  })
})
