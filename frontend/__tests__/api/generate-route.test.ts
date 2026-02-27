import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'

// Mock OpenAI before importing the route
const mockCreate = vi.fn()

class MockOpenAI {
  chat = {
    completions: {
      create: mockCreate,
    },
  }
}

vi.mock('openai', () => ({
  default: MockOpenAI,
}))

beforeEach(() => {
  vi.stubEnv('OPENAI_API_KEY', 'sk-test-key')
  vi.clearAllMocks()
  mockCreate.mockResolvedValue({
    choices: [{ message: { content: 'AI response' } }],
  })
})

afterEach(() => {
  vi.unstubAllEnvs()
})

// Helper to create a Request object matching what Next.js route handler receives
function createRequest(body: Record<string, unknown>): Request {
  return new Request('http://localhost/api/generate', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  })
}

describe('POST /api/generate', () => {
  it('builds string content when no attachments', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({ message: 'Hello' })

    await POST(request as any)

    const messages = mockCreate.mock.calls[0][0].messages
    const userMsg = messages.find((m: any) => m.role === 'user')
    expect(typeof userMsg.content).toBe('string')
    expect(userMsg.content).toBe('Hello')
  })

  it('builds multipart content for image attachments', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'What is this?',
      attachments: [
        { filename: 'photo.png', contentType: 'image/png', base64Data: 'data:image/png;base64,abc' },
      ],
    })

    await POST(request as any)

    const messages = mockCreate.mock.calls[0][0].messages
    const userMsg = messages.find((m: any) => m.role === 'user')
    expect(Array.isArray(userMsg.content)).toBe(true)
    expect(userMsg.content).toContainEqual({ type: 'text', text: 'What is this?' })
    expect(userMsg.content).toContainEqual({
      type: 'image_url',
      image_url: { url: 'data:image/png;base64,abc' },
    })
  })

  it('prepends text attachment content to user message', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'Summarize this',
      attachments: [
        { filename: 'notes.txt', contentType: 'text/plain', textContent: 'File content here' },
      ],
    })

    await POST(request as any)

    const messages = mockCreate.mock.calls[0][0].messages
    const userMsg = messages.find((m: any) => m.role === 'user')
    // Text attachments are prepended to the message as context
    expect(typeof userMsg.content).toBe('string')
    expect(userMsg.content).toContain('File content here')
    expect(userMsg.content).toContain('Summarize this')
    expect(userMsg.content).toContain('notes.txt')
  })

  it('handles mixed image and text attachments', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'Review both',
      attachments: [
        { filename: 'notes.txt', contentType: 'text/plain', textContent: 'Some notes' },
        { filename: 'diagram.png', contentType: 'image/png', base64Data: 'data:image/png;base64,xyz' },
      ],
    })

    await POST(request as any)

    const messages = mockCreate.mock.calls[0][0].messages
    const userMsg = messages.find((m: any) => m.role === 'user')
    // Should be multipart because there's an image
    expect(Array.isArray(userMsg.content)).toBe(true)
    // Text part should include both the original message and the text file content
    const textPart = userMsg.content.find((p: any) => p.type === 'text')
    expect(textPart.text).toContain('Review both')
    expect(textPart.text).toContain('Some notes')
    // Image part
    const imagePart = userMsg.content.find((p: any) => p.type === 'image_url')
    expect(imagePart.image_url.url).toBe('data:image/png;base64,xyz')
  })

  it('preserves backward-compatible history handling', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'Hello',
      history: [
        { role: 'user', content: 'First message' },
        { role: 'assistant', content: 'First reply' },
      ],
    })

    await POST(request as any)

    const messages = mockCreate.mock.calls[0][0].messages
    // system + 2 history + 1 user = 4 messages
    expect(messages).toHaveLength(4)
    expect(messages[0].role).toBe('system')
    expect(messages[1].content).toBe('First message')
    expect(messages[2].content).toBe('First reply')
    expect(messages[3].content).toBe('Hello')
  })

  it('returns 400 for missing message', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({ message: '' })

    const response = await POST(request as any)
    expect(response.status).toBe(400)
  })

  it('returns successful response with attachments', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'Describe this image',
      attachments: [
        { filename: 'img.png', contentType: 'image/png', base64Data: 'data:image/png;base64,abc' },
      ],
    })

    const response = await POST(request as any)
    expect(response.status).toBe(200)

    const data = await response.json()
    expect(data.content).toBe('AI response')
  })

  it('returns 400 when attachment count exceeds server limit', async () => {
    const { POST, MAX_ROUTE_ATTACHMENTS } = await import('@/app/api/generate/route')
    const attachments = Array.from({ length: MAX_ROUTE_ATTACHMENTS + 1 }, (_, i) => ({
      filename: `file-${i}.txt`,
      contentType: 'text/plain',
      textContent: 'x',
    }))
    const request = createRequest({ message: 'Too many', attachments })

    const response = await POST(request as any)
    expect(response.status).toBe(400)

    const data = await response.json()
    expect(data.error).toMatch(/too many attachments/i)
    expect(data.code).toBe('ATTACHMENT_LIMIT')
  })

  it('returns 400 when attachment payload is too large', async () => {
    const { POST, MAX_ROUTE_PAYLOAD_BYTES } = await import('@/app/api/generate/route')
    // Create a single attachment with base64Data exceeding the limit
    const largeData = 'data:image/png;base64,' + 'A'.repeat(MAX_ROUTE_PAYLOAD_BYTES + 1)
    const request = createRequest({
      message: 'Too big',
      attachments: [
        { filename: 'huge.png', contentType: 'image/png', base64Data: largeData },
      ],
    })

    const response = await POST(request as any)
    expect(response.status).toBe(400)

    const data = await response.json()
    expect(data.error).toMatch(/payload.*too large/i)
    expect(data.code).toBe('PAYLOAD_TOO_LARGE')
  })

  it('text-only request remains unaffected by attachment limits', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({ message: 'Just text, no files' })

    const response = await POST(request as any)
    expect(response.status).toBe(200)

    const data = await response.json()
    expect(data.content).toBe('AI response')
  })

  it('safely ignores attachments with unsupported MIME types', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'Check this PDF',
      attachments: [
        { filename: 'doc.pdf', contentType: 'application/pdf', textContent: '%PDF-garbage' },
      ],
    })

    // Route should process the request without error — unsupported attachments are skipped
    const response = await POST(request as any)
    expect(response.status).toBe(200)

    // The user message should still go through (just without the unsupported attachment content)
    const messages = mockCreate.mock.calls[0][0].messages
    const userMsg = messages.find((m: any) => m.role === 'user')
    expect(typeof userMsg.content).toBe('string')
    expect(userMsg.content).toBe('Check this PDF')
  })

  it('processes supported attachments and skips unsupported ones in the same request', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'Review these',
      attachments: [
        { filename: 'notes.txt', contentType: 'text/plain', textContent: 'Some notes' },
        { filename: 'archive.zip', contentType: 'application/zip', textContent: 'PK-garbage' },
        { filename: 'photo.png', contentType: 'image/png', base64Data: 'data:image/png;base64,abc' },
      ],
    })

    const response = await POST(request as any)
    expect(response.status).toBe(200)

    const messages = mockCreate.mock.calls[0][0].messages
    const userMsg = messages.find((m: any) => m.role === 'user')
    // Should be multipart (has an image) — zip should be excluded
    expect(Array.isArray(userMsg.content)).toBe(true)
    const textPart = userMsg.content.find((p: any) => p.type === 'text')
    expect(textPart.text).toContain('Some notes')
    expect(textPart.text).not.toContain('PK-garbage')
    const imagePart = userMsg.content.find((p: any) => p.type === 'image_url')
    expect(imagePart.image_url.url).toBe('data:image/png;base64,abc')
  })
})
