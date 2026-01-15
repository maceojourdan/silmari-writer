'use client'

import { useState } from 'react'
import MessageInput from '@/components/chat/MessageInput'
import FileAttachment from '@/components/chat/FileAttachment'

export default function TestPage() {
  const [messages, setMessages] = useState<string[]>([])
  const [files, setFiles] = useState<File[]>([])

  const handleSendMessage = (content: string) => {
    console.log('Sending:', content, 'with files:', files)
    setMessages((prev) => [...prev, content])
    setFiles([])
  }

  return (
    <div className="p-8 max-w-2xl mx-auto space-y-8">
      <h1 className="text-2xl font-bold">Phase 3: Message Input & File Attachments Test</h1>

      <section className="space-y-4">
        <h2 className="text-xl font-semibold">Message Input</h2>
        <p className="text-sm text-muted-foreground">
          Test the message input component. Enter sends, Shift+Enter adds newline.
        </p>
        <MessageInput onSendMessage={handleSendMessage} placeholder="Type a message..." />
      </section>

      <section className="space-y-4">
        <h2 className="text-xl font-semibold">File Attachments</h2>
        <p className="text-sm text-muted-foreground">
          Test file upload. Max 10MB per file. Drag and drop or click to attach.
        </p>
        <FileAttachment onFilesChange={setFiles} maxFiles={5} maxSizeBytes={10 * 1024 * 1024} />
      </section>

      {/* Message history */}
      {messages.length > 0 && (
        <section className="space-y-2">
          <h2 className="text-xl font-semibold">Sent Messages</h2>
          <ul className="space-y-2">
            {messages.map((msg, index) => (
              <li
                key={index}
                className="p-2 rounded-md bg-secondary/50 whitespace-pre-wrap font-mono text-sm"
              >
                {msg}
              </li>
            ))}
          </ul>
        </section>
      )}

      {/* Current files */}
      {files.length > 0 && (
        <section className="space-y-2">
          <h2 className="text-xl font-semibold">Current Files ({files.length})</h2>
          <ul className="text-sm text-muted-foreground">
            {files.map((file, index) => (
              <li key={index}>
                {file.name} ({(file.size / 1024).toFixed(2)} KB)
              </li>
            ))}
          </ul>
        </section>
      )}
    </div>
  )
}
