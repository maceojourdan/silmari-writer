import { describe, it, expect, vi } from 'vitest'
import { render, screen } from '@testing-library/react'
import MessageBubble from '@/components/chat/MessageBubble'
import { Message } from '@/lib/types'

// Mock ButtonRibbon
vi.mock('@/components/chat/ButtonRibbon', () => ({
  default: ({ messageId, content }: { messageId: string; content: string }) => (
    <div data-testid="button-ribbon" data-message-id={messageId}>
      ButtonRibbon: {content}
    </div>
  ),
}))

describe('MessageBubble with ButtonRibbon', () => {
  const assistantMessage: Message = {
    id: 'msg-123',
    role: 'assistant',
    content: 'This is an assistant message',
    timestamp: new Date('2026-01-16T10:00:00Z'),
  }

  const userMessage: Message = {
    id: 'msg-456',
    role: 'user',
    content: 'This is a user message',
    timestamp: new Date('2026-01-16T09:00:00Z'),
  }

  it('shows ButtonRibbon for assistant messages', () => {
    render(<MessageBubble message={assistantMessage} />)

    const buttonRibbon = screen.getByTestId('button-ribbon')
    expect(buttonRibbon).toBeInTheDocument()
    expect(buttonRibbon).toHaveAttribute('data-message-id', 'msg-123')
  })

  it('does not show ButtonRibbon for user messages', () => {
    render(<MessageBubble message={userMessage} />)

    expect(screen.queryByTestId('button-ribbon')).not.toBeInTheDocument()
  })

  it('passes message content to ButtonRibbon', () => {
    render(<MessageBubble message={assistantMessage} />)

    const buttonRibbon = screen.getByTestId('button-ribbon')
    expect(buttonRibbon).toHaveTextContent('This is an assistant message')
  })

  it('maintains existing message rendering', () => {
    render(<MessageBubble message={assistantMessage} />)

    // Message content still visible (will appear in both message and mocked ButtonRibbon)
    const messages = screen.getAllByText(/this is an assistant message/i)
    expect(messages.length).toBeGreaterThan(0)

    // Avatar still present
    expect(screen.getByLabelText(/ai/i)).toBeInTheDocument()

    // Timestamp still present
    expect(screen.getByTestId('message-timestamp')).toBeInTheDocument()
  })
})
