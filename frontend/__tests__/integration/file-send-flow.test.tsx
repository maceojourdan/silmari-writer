import { beforeEach, describe, expect, it, vi } from 'vitest'
import { render, screen } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import HomePage from '@/app/page'
import { useConversationStore } from '@/lib/store'
import { generateResponse } from '@/lib/api'
import { prepareFilesContent, UnsupportedFileError } from '@/lib/file-content'

Element.prototype.scrollIntoView = vi.fn()

vi.mock('@/lib/api', () => ({
  generateResponse: vi.fn().mockResolvedValue('AI response'),
}))

vi.mock('@/lib/file-content', () => {
  class MockUnsupportedFileError extends Error {
    filename: string
    mimeType: string

    constructor(filename: string, mimeType: string) {
      super(`Unsupported file type: "${filename}" (${mimeType})`)
      this.name = 'UnsupportedFileError'
      this.filename = filename
      this.mimeType = mimeType
    }
  }

  return {
    prepareFilesContent: vi.fn(),
    UnsupportedFileError: MockUnsupportedFileError,
    validateAttachments: vi.fn(() => ({ valid: true })),
  }
})

vi.mock('@/lib/transcription', () => ({
  transcribeAudio: vi.fn(),
}))

describe('file send flow', () => {
  beforeEach(() => {
    vi.clearAllMocks()
    vi.mocked(prepareFilesContent).mockResolvedValue([])
    useConversationStore.setState({
      projects: [{ id: 'proj-1', name: 'Test Project', createdAt: new Date(), updatedAt: new Date() }],
      activeProjectId: 'proj-1',
      messages: {},
      buttonStates: {},
      _hasHydrated: true,
      readAloudEnabled: false,
      voiceSessionState: 'idle',
      editHistory: null,
    })
  })

  it('passes prepared file payloads into generateResponse', async () => {
    const user = userEvent.setup()
    const file = new File(['hello world'], 'test.txt', { type: 'text/plain' })
    vi.mocked(prepareFilesContent).mockResolvedValueOnce([
      { filename: 'test.txt', contentType: 'text/plain', textContent: 'hello world' },
    ])

    render(<HomePage />)

    await user.upload(screen.getByTestId('file-input'), file)
    await user.type(screen.getByRole('textbox', { name: /message input/i }), 'Check attachment')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    expect(prepareFilesContent).toHaveBeenCalledWith([file])
    expect(generateResponse).toHaveBeenCalledWith(
      'Check attachment',
      expect.any(Array),
      [{ filename: 'test.txt', contentType: 'text/plain', textContent: 'hello world' }],
    )
  })

  it('stores user attachment metadata and renders attachment list', async () => {
    const user = userEvent.setup()
    const file = new File(['file body'], 'doc.txt', { type: 'text/plain' })
    vi.mocked(prepareFilesContent).mockResolvedValueOnce([
      { filename: 'doc.txt', contentType: 'text/plain', textContent: 'file body' },
    ])

    render(<HomePage />)

    await user.upload(screen.getByTestId('file-input'), file)
    await user.type(screen.getByRole('textbox', { name: /message input/i }), 'Use this file')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    const messages = useConversationStore.getState().messages['proj-1']
    const userMessage = messages.find((m) => m.role === 'user')
    expect(userMessage?.attachments).toHaveLength(1)
    expect(userMessage?.attachments?.[0].filename).toBe('doc.txt')

    await vi.waitFor(() => {
      expect(screen.getByTestId('attachment-list')).toBeInTheDocument()
    })
    expect(screen.getByText('doc.txt')).toBeInTheDocument()
  })

  it('passes document rawBlob payload into generateResponse', async () => {
    const user = userEvent.setup()
    const file = new File(['%PDF-fake'], 'report.pdf', { type: 'application/pdf' })
    vi.mocked(prepareFilesContent).mockResolvedValueOnce([
      { filename: 'report.pdf', contentType: 'application/pdf', rawBlob: 'JVBER2Zha2U=' },
    ])

    render(<HomePage />)

    await user.upload(screen.getByTestId('file-input'), file)
    await user.type(screen.getByRole('textbox', { name: /message input/i }), 'Summarize this PDF')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(generateResponse).toHaveBeenCalled()
    })

    expect(generateResponse).toHaveBeenCalledWith(
      'Summarize this PDF',
      expect.any(Array),
      [{ filename: 'report.pdf', contentType: 'application/pdf', rawBlob: 'JVBER2Zha2U=' }],
    )
  })

  it('shows unsupported-file error and skips generation', async () => {
    const user = userEvent.setup()
    const file = new File(['data'], 'video.mp4', { type: 'video/mp4' })
    vi.mocked(prepareFilesContent).mockRejectedValueOnce(
      new UnsupportedFileError('video.mp4', 'video/mp4'),
    )

    render(<HomePage />)

    await user.upload(screen.getByTestId('file-input'), file)
    await user.type(screen.getByRole('textbox', { name: /message input/i }), 'Summarize this')
    await user.keyboard('{Enter}')

    await vi.waitFor(() => {
      expect(screen.getByRole('alert')).toHaveTextContent(/unsupported file type/i)
    })

    expect(generateResponse).not.toHaveBeenCalled()
    expect(screen.getByRole('textbox', { name: /message input/i })).not.toBeDisabled()
  })
})
