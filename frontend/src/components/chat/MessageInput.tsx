'use client'

import { useState, useRef, useEffect, KeyboardEvent } from 'react'
import { Send } from 'lucide-react'

interface MessageInputProps {
  onSendMessage: (content: string) => void
  placeholder?: string
  disabled?: boolean
}

export default function MessageInput({
  onSendMessage,
  placeholder = 'Type a message...',
  disabled = false,
}: MessageInputProps) {
  const [content, setContent] = useState('')
  const textareaRef = useRef<HTMLTextAreaElement>(null)

  // Auto-resize textarea based on content
  useEffect(() => {
    if (textareaRef.current) {
      textareaRef.current.style.height = 'auto'
      textareaRef.current.style.height = textareaRef.current.scrollHeight + 'px'
    }
  }, [content])

  const handleSubmit = () => {
    const trimmed = content.trim()
    if (!trimmed) return

    onSendMessage(trimmed)
    setContent('')
  }

  const handleKeyDown = (e: KeyboardEvent<HTMLTextAreaElement>) => {
    // Enter without Shift sends the message
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault()
      handleSubmit()
    }
    // Shift+Enter is handled by default (adds newline)
  }

  const isEmpty = content.trim() === ''
  const isDisabled = disabled || isEmpty

  return (
    <div className="flex items-end gap-2 p-2 border border-border rounded-lg bg-card">
      <textarea
        ref={textareaRef}
        value={content}
        onChange={(e) => setContent(e.target.value)}
        onKeyDown={handleKeyDown}
        placeholder={placeholder}
        disabled={disabled}
        rows={1}
        className="flex-1 resize-none bg-transparent border-none outline-none min-h-[40px] max-h-[200px] py-2 px-2"
        aria-label="Message input"
      />
      <button
        onClick={handleSubmit}
        disabled={isDisabled}
        aria-label="Send message"
        className="p-2 rounded-md bg-primary text-primary-foreground disabled:opacity-50 disabled:cursor-not-allowed hover:bg-primary/90 transition-colors"
      >
        <Send className="h-5 w-5" />
      </button>
    </div>
  )
}
