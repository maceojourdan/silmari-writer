import { beforeEach, describe, expect, it, vi } from 'vitest'
import { generateResponse } from '@/lib/api'

const mockFetch = vi.fn()
vi.stubGlobal('fetch', mockFetch)

describe('generateResponse', () => {
  beforeEach(() => {
    vi.clearAllMocks()
  })

  it('sends message and history without attachments by default', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ content: 'ok' }),
    })

    await generateResponse('hello', [])

    const [, options] = mockFetch.mock.calls[0]
    const body = JSON.parse(options.body as string)
    expect(body.message).toBe('hello')
    expect(body.history).toEqual([])
    expect(body.attachments).toBeUndefined()
  })

  it('includes attachments when provided', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ content: 'ok' }),
    })

    await generateResponse('hello', [], [
      { filename: 'a.txt', contentType: 'text/plain', textContent: 'A' },
    ])

    const [, options] = mockFetch.mock.calls[0]
    const body = JSON.parse(options.body as string)
    expect(body.attachments).toEqual([
      { filename: 'a.txt', contentType: 'text/plain', textContent: 'A' },
    ])
  })
})
