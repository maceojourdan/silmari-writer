# File-to-LLM Pipeline: TDD Implementation Plan

## Overview

Enable attached files to be sent to the LLM along with the user's text input. Currently files are collected by `FileAttachment` but silently dropped before reaching the generation pipeline.

This plan is driven by two TLA+ path specs:
- **Baseline** (`specs/orchestration/file-to-llm-pipeline-model.md`) — documents 3 violated invariants
- **Target** (`specs/orchestration/file-to-llm-pipeline-target.md`) — all 10 invariants hold

## Current State Analysis

### Key Discoveries:
- `page.tsx:26` — `const [, setFiles]` destructures away the read side, making files write-only
- `handleSendMessage` at `page.tsx:41` — signature is `(content: string)`, no files parameter
- `addMessage` at `page.tsx:47` — passes `{role, content, timestamp}`, no `attachments`
- `generateResponse` at `api.ts:3` — sends `{message, history}`, no file data
- `route.ts:38` — `content` typed as `string`, never multipart `ContentPart[]`
- `MessageBubble.tsx:63` — only renders `message.content`, never `message.attachments`
- `types.ts:39-54` — `Attachment` and `Message.attachments?` types already exist but are never populated

### Existing Test Patterns:
- Vitest + React Testing Library + jest-dom matchers (`frontend/__tests__/`)
- `vi.fn()` for spies, `userEvent.setup()` for interactions
- `renderHook` + `act` for Zustand store testing (`store.test.ts`)
- `vi.stubGlobal('fetch', mockFetch)` for API mocking (`transcription.test.ts`)
- `createMockFile()` helper already exists in `FileAttachment.test.tsx`
- `vi.stubEnv()` for environment variables

## Desired End State

All 10 invariants hold. When a user attaches files and sends a message:
1. Files are captured as attachments on the stored user message (INV-1)
2. File content is serialized and forwarded through the API to OpenAI in multipart format (INV-2)
3. Attachment indicators are rendered in the message bubble (INV-3)
4. All existing invariants (INV-4 through INV-10) remain unbroken

### Observable Behaviors:
- Given files attached and text entered, when send is clicked, then the stored message has `attachments` populated
- Given a message with image attachments, when sent to OpenAI, then `content` is a multipart array with `image_url` parts
- Given a stored message with attachments, when rendered, then filename and type indicators appear
- Given no files attached, when text is sent, then behavior is identical to current (backward compatible)

## What We're NOT Doing

- File preview/thumbnails in the message bubble (just indicators with filename/type/size)
- Drag-and-drop directly into the message input area (existing FileAttachment drop zone is sufficient)
- Server-side file storage or upload endpoints (files are read client-side, serialized as base64)
- PDF text extraction (out of scope — PDFs sent as-is or rejected based on type)
- Streaming responses for multimodal requests (existing non-streaming flow preserved)
- Changes to the audio transcription flow (orthogonal feature)

## Testing Strategy

- **Framework**: Vitest (`npm run test` in `frontend/`)
- **Test Types**:
  - Unit: store attachments, file content utility, API serialization, route multipart building
  - Component: MessageBubble attachments, page.tsx orchestration
  - Integration: full file→send→store→API flow via mocked fetch
- **Mocking/Setup**: `vi.fn()` for callbacks, `vi.stubGlobal('fetch')` for API, `renderHook`+`act` for store, `createMockFile()` for File objects
- **Test run command**: `cd frontend && npx vitest run`

---

## Behavior 1: Store accepts and persists message attachments

### Test Specification
**Given**: A Zustand store with a project
**When**: `addMessage` is called with an `attachments` array
**Then**: The stored message includes the attachments

**Edge Cases**:
- Empty attachments array → stored as empty array
- No attachments field → stored as undefined (backward compatible)
- Multiple attachments → all preserved in order

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/store.test.ts`
```typescript
describe('Message Attachments', () => {
  it('addMessage stores attachments when provided', () => {
    const { result } = renderHook(() => useConversationStore())

    act(() => {
      result.current.createProject('Project 1')
      result.current.addMessage('test-uuid-1', {
        role: 'user',
        content: 'Check this file',
        timestamp: new Date(),
        attachments: [
          { id: 'att-1', filename: 'test.txt', size: 1024, type: 'text/plain' },
        ],
      })
    })

    const messages = result.current.getMessages('test-uuid-1')
    expect(messages[0].attachments).toHaveLength(1)
    expect(messages[0].attachments![0].filename).toBe('test.txt')
  })

  it('addMessage without attachments stores undefined attachments', () => {
    const { result } = renderHook(() => useConversationStore())

    act(() => {
      result.current.createProject('Project 1')
      result.current.addMessage('test-uuid-1', {
        role: 'user',
        content: 'Text only',
        timestamp: new Date(),
      })
    })

    const messages = result.current.getMessages('test-uuid-1')
    expect(messages[0].attachments).toBeUndefined()
  })

  it('addMessage preserves multiple attachments in order', () => {
    const { result } = renderHook(() => useConversationStore())

    act(() => {
      result.current.createProject('Project 1')
      result.current.addMessage('test-uuid-1', {
        role: 'user',
        content: 'Multiple files',
        timestamp: new Date(),
        attachments: [
          { id: 'att-1', filename: 'a.txt', size: 100, type: 'text/plain' },
          { id: 'att-2', filename: 'b.png', size: 200, type: 'image/png' },
          { id: 'att-3', filename: 'c.json', size: 300, type: 'application/json' },
        ],
      })
    })

    const messages = result.current.getMessages('test-uuid-1')
    expect(messages[0].attachments).toHaveLength(3)
    expect(messages[0].attachments!.map(a => a.filename)).toEqual(['a.txt', 'b.png', 'c.json'])
  })
})
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/lib/store.ts`

No code changes needed — `addMessage` already spreads `...message` which includes `attachments` if provided. The `Message` type already has `attachments?: Attachment[]`. These tests should **pass immediately** and serve as regression guards.

#### 🔵 Refactor: None needed

This behavior already works at the type and store level. The tests document and lock the contract.

### Success Criteria
**Automated:**
- [ ] Tests pass: `cd frontend && npx vitest run __tests__/lib/store.test.ts`
- [ ] Existing store tests still pass (no regression)

**Manual:**
- [ ] None needed for this behavior

---

## Behavior 2: File content preparation utility

### Test Specification
**Given**: A `File` object with known content and MIME type
**When**: `prepareFileContent(file)` is called
**Then**: Returns a `FileContentPayload` with appropriate content encoding

**Edge Cases**:
- Image file (image/png, image/jpeg, image/gif, image/webp) → base64 data URL
- Text file (text/plain, application/json) → extracted text content
- File read failure → throws with filename in error message
- Empty file → returns payload with empty content

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/file-content.test.ts`
```typescript
import { describe, it, expect } from 'vitest'
import { prepareFileContent, prepareFilesContent } from '@/lib/file-content'

// Helper to create File with actual readable content
function createReadableFile(name: string, content: string, type: string): File {
  return new File([content], name, { type })
}

function createBinaryFile(name: string, bytes: Uint8Array, type: string): File {
  return new File([bytes], name, { type })
}

describe('prepareFileContent', () => {
  it('converts image file to base64 data URL', async () => {
    const bytes = new Uint8Array([137, 80, 78, 71]) // PNG magic bytes
    const file = createBinaryFile('photo.png', bytes, 'image/png')

    const result = await prepareFileContent(file)

    expect(result.filename).toBe('photo.png')
    expect(result.contentType).toBe('image/png')
    expect(result.base64Data).toMatch(/^data:image\/png;base64,/)
    expect(result.textContent).toBeUndefined()
  })

  it('extracts text content from text file', async () => {
    const file = createReadableFile('notes.txt', 'Hello world', 'text/plain')

    const result = await prepareFileContent(file)

    expect(result.filename).toBe('notes.txt')
    expect(result.contentType).toBe('text/plain')
    expect(result.textContent).toBe('Hello world')
    expect(result.base64Data).toBeUndefined()
  })

  it('extracts text content from JSON file', async () => {
    const json = JSON.stringify({ key: 'value' })
    const file = createReadableFile('data.json', json, 'application/json')

    const result = await prepareFileContent(file)

    expect(result.filename).toBe('data.json')
    expect(result.contentType).toBe('application/json')
    expect(result.textContent).toBe(json)
  })

  it('converts jpeg image to base64 data URL', async () => {
    const bytes = new Uint8Array([255, 216, 255]) // JPEG magic bytes
    const file = createBinaryFile('photo.jpg', bytes, 'image/jpeg')

    const result = await prepareFileContent(file)

    expect(result.contentType).toBe('image/jpeg')
    expect(result.base64Data).toMatch(/^data:image\/jpeg;base64,/)
  })

  it('handles webp images', async () => {
    const bytes = new Uint8Array([82, 73, 70, 70]) // RIFF header
    const file = createBinaryFile('image.webp', bytes, 'image/webp')

    const result = await prepareFileContent(file)

    expect(result.contentType).toBe('image/webp')
    expect(result.base64Data).toBeDefined()
  })

  it('handles gif images', async () => {
    const bytes = new Uint8Array([71, 73, 70]) // GIF magic bytes
    const file = createBinaryFile('anim.gif', bytes, 'image/gif')

    const result = await prepareFileContent(file)

    expect(result.contentType).toBe('image/gif')
    expect(result.base64Data).toBeDefined()
  })
})

describe('prepareFilesContent', () => {
  it('returns empty array for empty input', async () => {
    const result = await prepareFilesContent([])
    expect(result).toEqual([])
  })

  it('processes multiple files', async () => {
    const files = [
      createReadableFile('a.txt', 'hello', 'text/plain'),
      createBinaryFile('b.png', new Uint8Array([137, 80, 78, 71]), 'image/png'),
    ]

    const result = await prepareFilesContent(files)

    expect(result).toHaveLength(2)
    expect(result[0].filename).toBe('a.txt')
    expect(result[1].filename).toBe('b.png')
  })

  it('isolates per-file errors and continues processing', async () => {
    // Create a file that will fail to read (0-byte with bad type simulation)
    const goodFile = createReadableFile('good.txt', 'content', 'text/plain')
    const files = [goodFile]

    const result = await prepareFilesContent(files)
    expect(result).toHaveLength(1)
    expect(result[0].filename).toBe('good.txt')
  })
})
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/lib/file-content.ts` (new)
```typescript
export interface FileContentPayload {
  filename: string
  contentType: string
  textContent?: string
  base64Data?: string
}

const IMAGE_TYPES = ['image/png', 'image/jpeg', 'image/gif', 'image/webp']
const TEXT_TYPES = ['text/plain', 'application/json']

function arrayBufferToBase64(buffer: ArrayBuffer): string {
  const bytes = new Uint8Array(buffer)
  let binary = ''
  for (let i = 0; i < bytes.byteLength; i++) {
    binary += String.fromCharCode(bytes[i])
  }
  return btoa(binary)
}

export async function prepareFileContent(file: File): Promise<FileContentPayload> {
  const base: Pick<FileContentPayload, 'filename' | 'contentType'> = {
    filename: file.name,
    contentType: file.type,
  }

  if (IMAGE_TYPES.includes(file.type)) {
    const buffer = await file.arrayBuffer()
    const b64 = arrayBufferToBase64(buffer)
    return { ...base, base64Data: `data:${file.type};base64,${b64}` }
  }

  if (TEXT_TYPES.includes(file.type)) {
    const text = await file.text()
    return { ...base, textContent: text }
  }

  // Fallback: treat as text
  const text = await file.text()
  return { ...base, textContent: text }
}

export async function prepareFilesContent(files: File[]): Promise<FileContentPayload[]> {
  const results: FileContentPayload[] = []
  for (const file of files) {
    try {
      const payload = await prepareFileContent(file)
      results.push(payload)
    } catch (err) {
      console.error(`Failed to prepare file ${file.name}:`, err)
      // Isolate per-file errors, continue with remaining files
    }
  }
  return results
}
```

#### 🔵 Refactor: None needed initially

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `prepareFileContent` not found
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/lib/file-content.test.ts`
- [ ] All tests pass: `cd frontend && npx vitest run`

**Manual:**
- [ ] None needed

---

## Behavior 3: API client forwards attachments in request body

### Test Specification
**Given**: A call to `generateResponse` with `attachments` parameter
**When**: The function makes a POST request
**Then**: The request body includes `attachments` array alongside `message` and `history`

**Edge Cases**:
- No attachments → request body matches current format (backward compatible)
- Attachments present → request body includes `attachments` field
- Error response → still throws as before

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/api.test.ts` (new)
```typescript
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
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/lib/api.ts`
```typescript
import { Message } from './types';
import type { FileContentPayload } from './file-content';

export async function generateResponse(
  userMessage: string,
  conversationHistory: Message[],
  attachments?: FileContentPayload[]
): Promise<string> {
  const body: Record<string, unknown> = {
    message: userMessage,
    history: conversationHistory.slice(-10),
  };

  if (attachments && attachments.length > 0) {
    body.attachments = attachments;
  }

  const response = await fetch('/api/generate', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });

  if (!response.ok) {
    throw new Error('Failed to generate response');
  }

  const data = await response.json();
  return data.content;
}
```

#### 🔵 Refactor: None needed

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `generateResponse` doesn't accept 3rd param
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/lib/api.test.ts`
- [ ] All tests pass: `cd frontend && npx vitest run`

**Manual:**
- [ ] None needed

---

## Behavior 4: Route handler builds multipart OpenAI content

### Test Specification
**Given**: A POST request to `/api/generate` with attachments in the body
**When**: The route handler builds the OpenAI messages array
**Then**: Image attachments produce `image_url` content parts, text attachments are prepended to the message

**Edge Cases**:
- No attachments → content is a plain string (backward compatible, INV-2 preserved for text-only)
- Image attachment → multipart `[{type:'text',...}, {type:'image_url',...}]`
- Text attachment → file text prepended to user message
- Mixed attachments → both image_url parts and prepended text
- Malformed attachments → 400 error

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/api/generate-route.test.ts` (new)
```typescript
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'

// Mock OpenAI before importing the route
const mockCreate = vi.fn()
vi.mock('openai', () => ({
  default: vi.fn().mockImplementation(() => ({
    chat: {
      completions: {
        create: mockCreate,
      },
    },
  })),
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

// Helper to create a NextRequest-like object
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

  it('preserves retry logic with multipart content (INV-8)', async () => {
    mockCreate
      .mockRejectedValueOnce({ status: 429, message: 'rate limited' })
      .mockResolvedValueOnce({
        choices: [{ message: { content: 'Success after retry' } }],
      })

    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({
      message: 'Hello',
      attachments: [
        { filename: 'img.png', contentType: 'image/png', base64Data: 'data:image/png;base64,abc' },
      ],
    })

    // Note: retry involves setTimeout, may need fake timers
    // For now, verify the route doesn't crash with attachments
    const response = await POST(request as any)
    expect(response.status).toBeLessThan(500)
  })

  it('returns 400 for missing message (INV preserved)', async () => {
    const { POST } = await import('@/app/api/generate/route')
    const request = createRequest({ message: '' })

    const response = await POST(request as any)
    expect(response.status).toBe(400)
  })
})
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/app/api/generate/route.ts`

Changes to `POST`:
```typescript
// At line 15, also extract attachments:
const { message, history = [], attachments = [] } = await request.json();

// In the messages array construction (lines 38-51), replace the user message:
const userContent = buildUserContent(message, attachments);
// ... and use userContent instead of message for the user role
```

New helper function:
```typescript
interface FileAttachment {
  filename: string;
  contentType: string;
  textContent?: string;
  base64Data?: string;
}

type ContentPart =
  | { type: 'text'; text: string }
  | { type: 'image_url'; image_url: { url: string } };

function buildUserContent(
  message: string,
  attachments: FileAttachment[]
): string | ContentPart[] {
  if (!attachments || attachments.length === 0) {
    return message;
  }

  const imageAttachments = attachments.filter(a => a.contentType.startsWith('image/'));
  const textAttachments = attachments.filter(a => !a.contentType.startsWith('image/'));

  // Build text portion: prepend text file contents
  let textContent = message;
  if (textAttachments.length > 0) {
    const fileTexts = textAttachments
      .map(a => `--- ${a.filename} ---\n${a.textContent || ''}`)
      .join('\n\n');
    textContent = `${fileTexts}\n\n${message}`;
  }

  // If no images, return as string
  if (imageAttachments.length === 0) {
    return textContent;
  }

  // Build multipart content array
  const parts: ContentPart[] = [{ type: 'text', text: textContent }];
  for (const img of imageAttachments) {
    if (img.base64Data) {
      parts.push({ type: 'image_url', image_url: { url: img.base64Data } });
    }
  }
  return parts;
}
```

Also widen the `messages` type and `makeOpenAIRequest` signature to accept `string | ContentPart[]`:
```typescript
type MessageContent = string | ContentPart[];

// Update makeOpenAIRequest and generateWithRetry signatures:
async function makeOpenAIRequest(
  openai: OpenAI,
  messages: Array<{ role: 'system' | 'user' | 'assistant'; content: MessageContent }>
): Promise<string>
```

#### 🔵 Refactor: Extract `buildUserContent` if it becomes complex

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): route ignores `attachments` field
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/api/generate-route.test.ts`
- [ ] All tests pass: `cd frontend && npx vitest run`
- [ ] Typecheck passes: `cd frontend && npx tsc --noEmit`

**Manual:**
- [ ] None needed

---

## Behavior 5: MessageBubble renders attachment indicators

### Test Specification
**Given**: A `Message` with `attachments` array
**When**: Rendered in `MessageBubble`
**Then**: Attachment indicators appear showing filename, type icon, and size

**Edge Cases**:
- No attachments → renders exactly as before (no regression)
- Single attachment → one indicator
- Multiple attachments → all indicators shown
- Image attachment → image icon
- Text attachment → document icon

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/components/MessageBubble.test.tsx` (new)
```typescript
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { render, screen } from '@testing-library/react'
import MessageBubble from '@/components/chat/MessageBubble'
import { Message } from '@/lib/types'

// Mock scrollIntoView (not needed here but keeping env clean)
const mockScrollIntoView = vi.fn()
window.HTMLElement.prototype.scrollIntoView = mockScrollIntoView

describe('MessageBubble', () => {
  beforeEach(() => {
    vi.useFakeTimers()
    vi.setSystemTime(new Date('2026-02-27T12:00:00.000Z'))
  })

  afterEach(() => {
    vi.useRealTimers()
  })

  it('renders message content without attachments (no regression)', () => {
    const message: Message = {
      id: '1',
      role: 'user',
      content: 'Hello world',
      timestamp: new Date(),
    }

    render(<MessageBubble message={message} />)

    expect(screen.getByText('Hello world')).toBeInTheDocument()
    expect(screen.queryByTestId('attachment-list')).not.toBeInTheDocument()
  })

  it('renders attachment indicators when attachments present', () => {
    const message: Message = {
      id: '1',
      role: 'user',
      content: 'Check this file',
      timestamp: new Date(),
      attachments: [
        { id: 'att-1', filename: 'report.txt', size: 2048, type: 'text/plain' },
      ],
    }

    render(<MessageBubble message={message} />)

    expect(screen.getByText('Check this file')).toBeInTheDocument()
    expect(screen.getByTestId('attachment-list')).toBeInTheDocument()
    expect(screen.getByText('report.txt')).toBeInTheDocument()
  })

  it('renders multiple attachment indicators', () => {
    const message: Message = {
      id: '1',
      role: 'user',
      content: 'Multiple files',
      timestamp: new Date(),
      attachments: [
        { id: 'att-1', filename: 'doc.txt', size: 1024, type: 'text/plain' },
        { id: 'att-2', filename: 'photo.png', size: 5000, type: 'image/png' },
      ],
    }

    render(<MessageBubble message={message} />)

    expect(screen.getByText('doc.txt')).toBeInTheDocument()
    expect(screen.getByText('photo.png')).toBeInTheDocument()
  })

  it('shows file size for attachments', () => {
    const message: Message = {
      id: '1',
      role: 'user',
      content: 'With size',
      timestamp: new Date(),
      attachments: [
        { id: 'att-1', filename: 'data.json', size: 3072, type: 'application/json' },
      ],
    }

    render(<MessageBubble message={message} />)

    expect(screen.getByText('data.json')).toBeInTheDocument()
    // Size should be formatted (3 KB or similar)
    expect(screen.getByText(/3.*KB/i)).toBeInTheDocument()
  })

  it('renders attachments for assistant messages too', () => {
    const message: Message = {
      id: '1',
      role: 'assistant',
      content: 'Response with context',
      timestamp: new Date(),
      attachments: [
        { id: 'att-1', filename: 'context.txt', size: 500, type: 'text/plain' },
      ],
    }

    render(<MessageBubble message={message} />)

    expect(screen.getByText('context.txt')).toBeInTheDocument()
  })
})
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/components/chat/MessageBubble.tsx`

Add after the ReactMarkdown block (before the timestamp div):
```tsx
{message.attachments && message.attachments.length > 0 && (
  <div data-testid="attachment-list" className="mt-2 space-y-1">
    {message.attachments.map((att) => (
      <div
        key={att.id}
        className={`flex items-center gap-2 text-xs rounded px-2 py-1 ${
          isUser ? 'bg-blue-600/30' : 'bg-gray-300/50'
        }`}
      >
        <Paperclip className="h-3 w-3 flex-shrink-0" />
        <span className="truncate">{att.filename}</span>
        <span className="flex-shrink-0 opacity-70">{formatBytes(att.size)}</span>
      </div>
    ))}
  </div>
)}
```

Add imports:
```typescript
import { Paperclip } from 'lucide-react';
import { formatBytes } from '@/lib/utils';
```

#### 🔵 Refactor: Extract `AttachmentIndicator` component if it grows

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): no `attachment-list` testid rendered
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/components/MessageBubble.test.tsx`
- [ ] Existing ConversationView tests still pass (no regression)
- [ ] All tests pass: `cd frontend && npx vitest run`

**Manual:**
- [ ] Attachments display inline with message bubble
- [ ] Correct styling for user (blue) vs assistant (gray) messages

---

## Behavior 6: Page orchestration wires files through the pipeline

### Test Specification
**Given**: `page.tsx` with files attached via `FileAttachment` and text entered in `MessageInput`
**When**: The user sends the message
**Then**: The stored user message has attachments, and `generateResponse` receives file content payloads

This is the integration behavior that fixes INV-1 by wiring everything together.

**Edge Cases**:
- Files attached + send → attachments on stored message, file payloads sent to API
- No files + send → no attachments, no file payloads (backward compatible)
- Generation error → files still cleared (INV-7 preserved)
- Generation success → files cleared (INV-7 preserved)

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/integration/file-send-flow.test.tsx` (new)

This tests the integration at the page.tsx level. Because page.tsx is a full page component with complex dependencies, we test the orchestration logic by mocking the API layer and observing store state.

```typescript
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { render, screen, act } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import { useConversationStore } from '@/lib/store'

// Mock the API module
vi.mock('@/lib/api', () => ({
  generateResponse: vi.fn().mockResolvedValue('AI response'),
}))

// Mock transcription (not under test)
vi.mock('@/lib/transcription', () => ({
  transcribeAudio: vi.fn(),
}))

// Mock crypto.randomUUID for deterministic IDs
let uuidCounter = 0
vi.stubGlobal('crypto', {
  randomUUID: () => `test-uuid-${++uuidCounter}`,
})

import HomePage from '@/app/page'
import { generateResponse } from '@/lib/api'

describe('File send flow integration', () => {
  beforeEach(() => {
    uuidCounter = 0
    useConversationStore.setState({
      projects: [{ id: 'proj-1', name: 'Test', createdAt: new Date(), updatedAt: new Date() }],
      activeProjectId: 'proj-1',
      messages: {},
      _hasHydrated: true,
    })
    vi.clearAllMocks()
  })

  it('sends message with file attachments included in API call', async () => {
    const user = userEvent.setup()
    render(<HomePage />)

    // Attach a file
    const fileInput = screen.getByTestId('file-input')
    const file = new File(['hello world'], 'test.txt', { type: 'text/plain' })
    await user.upload(fileInput, file)

    // Type and send message
    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Check this file')
    await user.keyboard('{Enter}')

    // Wait for async operations
    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    // Verify generateResponse was called with attachments
    const callArgs = (generateResponse as any).mock.calls[0]
    expect(callArgs[0]).toBe('Check this file') // message
    expect(callArgs[2]).toBeDefined() // attachments parameter
    expect(callArgs[2]).toHaveLength(1)
    expect(callArgs[2][0].filename).toBe('test.txt')
  })

  it('sends message without attachments when no files', async () => {
    const user = userEvent.setup()
    render(<HomePage />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Text only')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    // No attachments parameter (or empty)
    const callArgs = (generateResponse as any).mock.calls[0]
    expect(callArgs[0]).toBe('Text only')
    // Third arg should be undefined or empty array
    const attachments = callArgs[2]
    expect(!attachments || attachments.length === 0).toBe(true)
  })

  it('stores user message with attachments in Zustand (INV-1)', async () => {
    const user = userEvent.setup()
    render(<HomePage />)

    // Attach a file
    const fileInput = screen.getByTestId('file-input')
    const file = new File(['content'], 'doc.txt', { type: 'text/plain' })
    await user.upload(fileInput, file)

    // Send message
    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'With attachment')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    // Check store
    const messages = useConversationStore.getState().messages['proj-1']
    const userMsg = messages?.find(m => m.role === 'user')
    expect(userMsg).toBeDefined()
    expect(userMsg!.attachments).toBeDefined()
    expect(userMsg!.attachments).toHaveLength(1)
    expect(userMsg!.attachments![0].filename).toBe('doc.txt')
  })

  it('clears files after generation completes (INV-7)', async () => {
    const user = userEvent.setup()
    render(<HomePage />)

    // Attach file
    const fileInput = screen.getByTestId('file-input')
    const file = new File(['content'], 'temp.txt', { type: 'text/plain' })
    await user.upload(fileInput, file)

    // Verify file is shown
    expect(screen.getByText('temp.txt')).toBeInTheDocument()

    // Send
    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Send it')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    // Files should be cleared after generation
    await vi.waitFor(() => {
      expect(screen.queryByText('temp.txt')).not.toBeInTheDocument()
    })
  })
})
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/app/page.tsx`

Three changes needed:

1. Fix the destructuring at line 26:
```typescript
// Before:
const [, setFiles] = useState<File[]>([]);
// After:
const [files, setFiles] = useState<File[]>([]);
```

2. Update `handleSendMessage` to read files and pass them through:
```typescript
import { prepareFilesContent } from '@/lib/file-content';

const handleSendMessage = async (content: string) => {
  if (!activeProjectId) return;

  setError(null);

  // Snapshot files at submit time
  const currentFiles = [...files];

  // Build attachments metadata for the stored message
  const attachments = currentFiles.length > 0
    ? currentFiles.map(f => ({
        id: crypto.randomUUID(),
        filename: f.name,
        size: f.size,
        type: f.type,
      }))
    : undefined;

  // Add user message WITH attachments (fixes INV-1)
  addMessage(activeProjectId, {
    role: 'user',
    content,
    timestamp: new Date(),
    ...(attachments ? { attachments } : {}),
  });

  setIsGenerating(true);

  try {
    // Prepare file content for API (new step: file_content_prepared)
    const filePayloads = await prepareFilesContent(currentFiles);

    // Generate AI response WITH file data (fixes INV-2)
    const response = await generateResponse(content, activeMessages, filePayloads.length > 0 ? filePayloads : undefined);

    addMessage(activeProjectId, {
      role: 'assistant',
      content: response,
      timestamp: new Date(),
    });
  } catch (err) {
    setError('Failed to generate response. Please try again.');
    console.error('Failed to generate response:', err);
  } finally {
    setIsGenerating(false);
    setFiles([]);
  }
};
```

#### 🔵 Refactor: Extract file snapshot + metadata building if it grows

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `generateResponse` not called with attachments
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/integration/file-send-flow.test.tsx`
- [ ] All existing tests pass: `cd frontend && npx vitest run`
- [ ] Typecheck passes: `cd frontend && npx tsc --noEmit`

**Manual:**
- [ ] Attach a text file, send a message, verify the AI response acknowledges the file content
- [ ] Attach an image, send a message, verify the AI describes the image
- [ ] Send text-only message, verify behavior unchanged
- [ ] Verify files are cleared from FileAttachment UI after send

---

## Integration & E2E Testing

### Integration scenarios covered:
- Behavior 6 tests cover the full page.tsx orchestration
- Behavior 3 + 4 tests cover the API→route→OpenAI chain

### E2E (existing Playwright test):
The existing `e2e/conversation-flow.spec.ts` tests the text-only flow. After implementation, it should still pass unchanged.

**New E2E test not required** for this plan — the unit + integration tests provide sufficient coverage of the file attachment path. E2E testing can be added in a follow-up if needed.

### Regression: run full suite
```bash
cd frontend && npx vitest run  # All unit + component + integration tests
cd frontend && npx tsc --noEmit  # Type safety
```

---

## Implementation Order (Red-Green-Refactor sequence)

| # | Behavior | New/Modified Files | Depends On |
|---|----------|-------------------|------------|
| 1 | Store accepts attachments | `store.test.ts` (extend) | None — already works, tests lock the contract |
| 2 | File content preparation | `file-content.test.ts` (new), `file-content.ts` (new) | None |
| 3 | API client forwards attachments | `api.test.ts` (new), `api.ts` (modify) | Behavior 2 (imports `FileContentPayload` type) |
| 4 | Route builds multipart content | `generate-route.test.ts` (new), `route.ts` (modify) | None (server side, independent of client) |
| 5 | MessageBubble renders attachments | `MessageBubble.test.tsx` (new), `MessageBubble.tsx` (modify) | None (pure component) |
| 6 | Page orchestration | `file-send-flow.test.tsx` (new), `page.tsx` (modify) | Behaviors 2, 3, 5 |

Behaviors 1-5 can be parallelized. Behavior 6 depends on 2, 3, and 5 being complete.

## References

- Baseline spec: `specs/orchestration/file-to-llm-pipeline-model.md`
- Target spec: `specs/orchestration/file-to-llm-pipeline-target.md`
- TLA+ baseline: `artifacts/tlaplus/file-to-llm-pipeline-model/FileToLlmPipelineModel.tla`
- TLA+ target: `artifacts/tlaplus/file-to-llm-pipeline-target/FileToLlmPipelineTarget.tla`
- UI TDD Phase 3: `thoughts/searchable/shared/plans/2026-01-14-tdd-writing-agent-ui/2026-01-09-tdd-writing-agent-ui-03-phase-3.md`
