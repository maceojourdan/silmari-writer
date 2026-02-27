import { describe, it, expect, vi, beforeEach } from 'vitest'
import { render, screen } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import { useConversationStore } from '@/lib/store'

// jsdom stubs
Element.prototype.scrollIntoView = vi.fn()

// Mock API module
vi.mock('@/lib/api', () => ({
  generateResponse: vi.fn().mockResolvedValue('AI response'),
}))

// Mock file-content module — return payloads matching input files
vi.mock('@/lib/file-content', () => ({
  prepareFilesContent: vi.fn().mockImplementation(async (files: File[]) =>
    files.map(f => ({ filename: f.name, contentType: f.type, textContent: 'mock content' }))
  ),
}))

// Mock transcription (not under test)
vi.mock('@/lib/transcription', () => ({
  transcribeAudio: vi.fn(),
}))

// Deterministic UUIDs
let uuidCounter = 0
vi.stubGlobal('crypto', {
  randomUUID: () => `test-uuid-${++uuidCounter}`,
})

import HomePage from '@/app/page'
import { generateResponse } from '@/lib/api'
import { prepareFilesContent } from '@/lib/file-content'

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

    // Wait for async send
    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    // prepareFilesContent should have been called with the files
    expect(prepareFilesContent).toHaveBeenCalledWith([file])

    // generateResponse should receive file payloads as third argument
    const callArgs = (generateResponse as ReturnType<typeof vi.fn>).mock.calls[0]
    expect(callArgs[0]).toBe('Check this file')
    expect(callArgs[2]).toBeDefined()
    expect(callArgs[2]).toHaveLength(1)
    expect(callArgs[2][0].filename).toBe('test.txt')
  })

  it('sends message without attachments when no files (backward compatible)', async () => {
    const user = userEvent.setup()
    render(<HomePage />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Text only')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    // No file payloads
    const callArgs = (generateResponse as ReturnType<typeof vi.fn>).mock.calls[0]
    expect(callArgs[0]).toBe('Text only')
    const attachments = callArgs[2]
    expect(!attachments || attachments.length === 0).toBe(true)
  })

  it('stores user message with attachments metadata in store (INV-1)', async () => {
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

    // Check store for user message with attachments
    const messages = useConversationStore.getState().messages['proj-1']
    const userMsg = messages?.find(m => m.role === 'user')
    expect(userMsg).toBeDefined()
    expect(userMsg!.attachments).toBeDefined()
    expect(userMsg!.attachments).toHaveLength(1)
    expect(userMsg!.attachments![0].filename).toBe('doc.txt')
  })

  it('clears files from FileAttachment after generation completes (INV-7)', async () => {
    const user = userEvent.setup()
    render(<HomePage />)

    // Attach file
    const fileInput = screen.getByTestId('file-input')
    const file = new File(['content'], 'temp.txt', { type: 'text/plain' })
    await user.upload(fileInput, file)

    // File should be shown with a remove button (FileAttachment list)
    expect(screen.getByRole('button', { name: /remove temp\.txt/i })).toBeInTheDocument()

    // Send
    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Send it')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    // Remove button should be gone (FileAttachment list cleared)
    await vi.waitFor(() => {
      expect(screen.queryByRole('button', { name: /remove temp\.txt/i })).not.toBeInTheDocument()
    })
  })
})
