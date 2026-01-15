import { describe, it, expect, vi } from 'vitest'
import { render, screen, fireEvent } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import FileAttachment from '@/components/chat/FileAttachment'

// Helper to create mock File objects
function createMockFile(name: string, size: number, type: string = 'text/plain'): File {
  const file = new File(['x'.repeat(size)], name, { type })
  Object.defineProperty(file, 'size', { value: size })
  return file
}

describe('FileAttachment', () => {
  it('renders file input and attach button', () => {
    render(<FileAttachment onFilesChange={() => {}} />)
    expect(screen.getByRole('button', { name: /attach/i })).toBeInTheDocument()
  })

  it('renders drag-and-drop zone', () => {
    render(<FileAttachment onFilesChange={() => {}} />)
    expect(screen.getByTestId('dropzone')).toBeInTheDocument()
  })

  it('accepts files under 10MB', async () => {
    const onFilesChange = vi.fn()
    render(<FileAttachment onFilesChange={onFilesChange} />)

    const file = createMockFile('test.txt', 5 * 1024 * 1024) // 5MB
    const input = screen.getByTestId('file-input')

    await userEvent.upload(input, file)

    expect(onFilesChange).toHaveBeenCalled()
    const calledWith = onFilesChange.mock.calls[0][0]
    expect(calledWith).toHaveLength(1)
    expect(calledWith[0].name).toBe('test.txt')
  })

  it('rejects files over 10MB with error message', async () => {
    const onFilesChange = vi.fn()
    render(<FileAttachment onFilesChange={onFilesChange} />)

    const file = createMockFile('large.txt', 15 * 1024 * 1024) // 15MB
    const input = screen.getByTestId('file-input')

    await userEvent.upload(input, file)

    expect(screen.getByText(/exceeds 10 MB limit/i)).toBeInTheDocument()
    // File should not be added
    expect(onFilesChange).toHaveBeenCalledWith([])
  })

  it('accepts multiple files', async () => {
    const onFilesChange = vi.fn()
    render(<FileAttachment onFilesChange={onFilesChange} />)

    const files = [
      createMockFile('file1.txt', 1024),
      createMockFile('file2.txt', 2048),
      createMockFile('file3.txt', 3072),
    ]
    const input = screen.getByTestId('file-input')

    await userEvent.upload(input, files)

    expect(onFilesChange).toHaveBeenCalled()
    const calledWith = onFilesChange.mock.calls[0][0]
    expect(calledWith).toHaveLength(3)
  })

  it('displays file names and sizes in list', async () => {
    render(<FileAttachment onFilesChange={() => {}} />)

    const file = createMockFile('document.pdf', 5 * 1024 * 1024)
    const input = screen.getByTestId('file-input')

    await userEvent.upload(input, file)

    expect(screen.getByText('document.pdf')).toBeInTheDocument()
    expect(screen.getByText(/5 MB/i)).toBeInTheDocument()
  })

  it('allows removing files from list', async () => {
    const onFilesChange = vi.fn()
    render(<FileAttachment onFilesChange={onFilesChange} />)

    const file = createMockFile('test.txt', 1024)
    const input = screen.getByTestId('file-input')

    await userEvent.upload(input, file)

    // File should be displayed
    expect(screen.getByText('test.txt')).toBeInTheDocument()

    // Click remove button
    const removeButton = screen.getByRole('button', { name: /remove test.txt/i })
    await userEvent.click(removeButton)

    // File should be removed
    expect(screen.queryByText('test.txt')).not.toBeInTheDocument()
    // onFilesChange should be called with empty array
    expect(onFilesChange).toHaveBeenLastCalledWith([])
  })

  it('highlights drop zone on drag over', () => {
    render(<FileAttachment onFilesChange={() => {}} />)
    const dropzone = screen.getByTestId('dropzone')

    fireEvent.dragEnter(dropzone)

    expect(dropzone).toHaveAttribute('data-drag-active', 'true')
  })

  it('removes highlight when drag leaves', () => {
    render(<FileAttachment onFilesChange={() => {}} />)
    const dropzone = screen.getByTestId('dropzone')

    fireEvent.dragEnter(dropzone)
    expect(dropzone).toHaveAttribute('data-drag-active', 'true')

    fireEvent.dragLeave(dropzone)
    expect(dropzone).toHaveAttribute('data-drag-active', 'false')
  })

  it('accepts dropped files', async () => {
    const onFilesChange = vi.fn()
    render(<FileAttachment onFilesChange={onFilesChange} />)

    const file = createMockFile('dropped.txt', 1024)
    const dropzone = screen.getByTestId('dropzone')

    const dataTransfer = {
      files: [file],
      items: [{ kind: 'file', type: 'text/plain', getAsFile: () => file }],
      types: ['Files'],
    }

    fireEvent.drop(dropzone, { dataTransfer })

    expect(onFilesChange).toHaveBeenCalled()
  })

  it('respects maxFiles prop', async () => {
    const onFilesChange = vi.fn()
    render(<FileAttachment onFilesChange={onFilesChange} maxFiles={2} />)

    const files = [
      createMockFile('file1.txt', 1024),
      createMockFile('file2.txt', 1024),
      createMockFile('file3.txt', 1024),
    ]
    const input = screen.getByTestId('file-input')

    await userEvent.upload(input, files)

    // Only first 2 files should be accepted
    expect(onFilesChange).toHaveBeenCalled()
    const calledWith = onFilesChange.mock.calls[0][0]
    expect(calledWith).toHaveLength(2)
    expect(screen.getByText(/maximum 2 files/i)).toBeInTheDocument()
  })

  it('respects custom maxSizeBytes prop', async () => {
    const onFilesChange = vi.fn()
    render(<FileAttachment onFilesChange={onFilesChange} maxSizeBytes={5 * 1024 * 1024} />)

    const file = createMockFile('medium.txt', 6 * 1024 * 1024) // 6MB
    const input = screen.getByTestId('file-input')

    await userEvent.upload(input, file)

    expect(screen.getByText(/exceeds 5 MB limit/i)).toBeInTheDocument()
    expect(onFilesChange).toHaveBeenCalledWith([])
  })

  it('clears error when valid file is added', async () => {
    render(<FileAttachment onFilesChange={() => {}} />)

    // First add a file that's too large
    const largeFile = createMockFile('large.txt', 15 * 1024 * 1024)
    const input = screen.getByTestId('file-input')
    await userEvent.upload(input, largeFile)

    expect(screen.getByText(/exceeds 10 MB limit/i)).toBeInTheDocument()

    // Then add a valid file
    const validFile = createMockFile('valid.txt', 1024)
    await userEvent.upload(input, validFile)

    // Error should be cleared
    expect(screen.queryByText(/exceeds 10 MB limit/i)).not.toBeInTheDocument()
  })
})
