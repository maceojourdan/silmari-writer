import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { render, screen } from '@testing-library/react'
import MessageBubble from '@/components/chat/MessageBubble'
import { Message } from '@/lib/types'

// Mock scrollIntoView (keeping env clean)
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

  it('shows formatted file size for attachments', () => {
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
    expect(screen.getByText('3 KB')).toBeInTheDocument()
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
    expect(screen.getByTestId('attachment-list')).toBeInTheDocument()
  })
})
