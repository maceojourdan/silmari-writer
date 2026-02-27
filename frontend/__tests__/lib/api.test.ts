import { describe, it, expect, vi, beforeEach } from 'vitest'
import { generateResponse } from '@/lib/api'
import type { FileContentPayload } from '@/lib/file-content'

const mockFetch = vi.fn()
vi.stubGlobal('fetch', mockFetch)

beforeEach(() => {
  vi.clearAllMocks()
})

describe('generateResponse', () => {
  it('sends message and history without attachments (backward compat)', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ content: 'AI response' }),
    })

    const result = await generateResponse('Hello', [])

    expect(result).toBe('AI response')
    const body = JSON.parse(mockFetch.mock.calls[0][1].body)
    expect(body.message).toBe('Hello')
    expect(body.history).toEqual([])
    expect(body.attachments).toBeUndefined()
  })

  it('includes attachments in request body when provided', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ content: 'AI response' }),
    })

    const attachments: FileContentPayload[] = [
      { filename: 'test.txt', contentType: 'text/plain', textContent: 'file content' },
    ]

    const result = await generateResponse('Check this', [], attachments)

    expect(result).toBe('AI response')
    const body = JSON.parse(mockFetch.mock.calls[0][1].body)
    expect(body.message).toBe('Check this')
    expect(body.attachments).toHaveLength(1)
    expect(body.attachments[0].filename).toBe('test.txt')
  })

  it('includes image attachments with base64 data', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ content: 'I see the image' }),
    })

    const attachments: FileContentPayload[] = [
      { filename: 'photo.png', contentType: 'image/png', base64Data: 'data:image/png;base64,abc123' },
    ]

    await generateResponse('What is this?', [], attachments)

    const body = JSON.parse(mockFetch.mock.calls[0][1].body)
    expect(body.attachments[0].base64Data).toBe('data:image/png;base64,abc123')
  })

  it('bounds history to last 10 messages (INV-10 preserved)', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ content: 'response' }),
    })

    const history = Array.from({ length: 15 }, (_, i) => ({
      id: `msg-${i}`,
      role: 'user' as const,
      content: `Message ${i}`,
      timestamp: new Date(),
    }))

    await generateResponse('Hello', history)

    const body = JSON.parse(mockFetch.mock.calls[0][1].body)
    expect(body.history).toHaveLength(10)
  })

  it('throws on non-ok response', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: false,
      status: 500,
    })

    await expect(generateResponse('Hello', [])).rejects.toThrow('Failed to generate response')
  })
})
