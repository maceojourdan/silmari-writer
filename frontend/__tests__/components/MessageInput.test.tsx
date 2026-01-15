import { describe, it, expect, vi } from 'vitest'
import { render, screen, fireEvent } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import MessageInput from '@/components/chat/MessageInput'

describe('MessageInput', () => {
  it('renders a textarea', () => {
    render(<MessageInput onSendMessage={() => {}} />)
    expect(screen.getByRole('textbox')).toBeInTheDocument()
  })

  it('renders a send button', () => {
    render(<MessageInput onSendMessage={() => {}} />)
    expect(screen.getByRole('button', { name: /send/i })).toBeInTheDocument()
  })

  it('send button is disabled when textarea is empty', () => {
    render(<MessageInput onSendMessage={() => {}} />)
    const sendButton = screen.getByRole('button', { name: /send/i })
    expect(sendButton).toBeDisabled()
  })

  it('send button is enabled when textarea has content', async () => {
    const user = userEvent.setup()
    render(<MessageInput onSendMessage={() => {}} />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Hello world')

    const sendButton = screen.getByRole('button', { name: /send/i })
    expect(sendButton).not.toBeDisabled()
  })

  it('calls onSendMessage with content when send button is clicked', async () => {
    const onSendMessage = vi.fn()
    const user = userEvent.setup()
    render(<MessageInput onSendMessage={onSendMessage} />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Hello world')

    const sendButton = screen.getByRole('button', { name: /send/i })
    await user.click(sendButton)

    expect(onSendMessage).toHaveBeenCalledWith('Hello world')
  })

  it('clears textarea after send', async () => {
    const user = userEvent.setup()
    render(<MessageInput onSendMessage={() => {}} />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Hello world')

    const sendButton = screen.getByRole('button', { name: /send/i })
    await user.click(sendButton)

    expect(textarea).toHaveValue('')
  })

  it('Enter key triggers send', async () => {
    const onSendMessage = vi.fn()
    const user = userEvent.setup()
    render(<MessageInput onSendMessage={onSendMessage} />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Hello world')
    await user.keyboard('{Enter}')

    expect(onSendMessage).toHaveBeenCalledWith('Hello world')
  })

  it('Shift+Enter adds newline instead of sending', async () => {
    const onSendMessage = vi.fn()
    const user = userEvent.setup()
    render(<MessageInput onSendMessage={onSendMessage} />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, 'Line 1')
    await user.keyboard('{Shift>}{Enter}{/Shift}')
    await user.type(textarea, 'Line 2')

    expect(onSendMessage).not.toHaveBeenCalled()
    expect(textarea).toHaveValue('Line 1\nLine 2')
  })

  it('respects placeholder prop', () => {
    render(<MessageInput onSendMessage={() => {}} placeholder="Type here..." />)
    expect(screen.getByPlaceholderText('Type here...')).toBeInTheDocument()
  })

  it('respects disabled prop', () => {
    render(<MessageInput onSendMessage={() => {}} disabled />)
    expect(screen.getByRole('textbox')).toBeDisabled()
    expect(screen.getByRole('button', { name: /send/i })).toBeDisabled()
  })

  it('does not send empty message', async () => {
    const onSendMessage = vi.fn()
    const user = userEvent.setup()
    render(<MessageInput onSendMessage={onSendMessage} />)

    const textarea = screen.getByRole('textbox')
    await user.click(textarea)
    await user.keyboard('{Enter}')

    expect(onSendMessage).not.toHaveBeenCalled()
  })

  it('trims whitespace-only messages and does not send', async () => {
    const onSendMessage = vi.fn()
    const user = userEvent.setup()
    render(<MessageInput onSendMessage={onSendMessage} />)

    const textarea = screen.getByRole('textbox')
    await user.type(textarea, '   ')
    await user.keyboard('{Enter}')

    expect(onSendMessage).not.toHaveBeenCalled()
  })
})
