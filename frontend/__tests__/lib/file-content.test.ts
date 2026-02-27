import { describe, it, expect, vi } from 'vitest'
import {
  prepareFileContent,
  prepareFilesContent,
  validateAttachments,
  isSupportedMimeType,
  SUPPORTED_IMAGE_TYPES,
  SUPPORTED_TEXT_TYPES,
  MAX_ATTACHMENT_COUNT,
  MAX_FILE_SIZE_BYTES,
  MAX_TOTAL_SIZE_BYTES,
  UnsupportedFileError,
  type FileContentPayload,
} from '@/lib/file-content'

// Helper to create a File from string content
function makeFile(name: string, content: string, type: string): File {
  return new File([content], name, { type })
}

// Helper to create a File from binary (Uint8Array)
function makeBinaryFile(name: string, bytes: Uint8Array, type: string): File {
  return new File([bytes as unknown as BlobPart], name, { type })
}

// Helper to create a fake File-like object that will cause FileReader to fail.
// FileReader.readAsText requires an actual Blob; passing a non-Blob triggers an error.
function makeBrokenFile(name: string, type: string): File {
  return { name, type } as unknown as File
}

describe('prepareFileContent (single file)', () => {
  describe('image files', () => {
    it('returns base64 data URL for png', async () => {
      const bytes = new Uint8Array([0x89, 0x50, 0x4e, 0x47])
      const file = makeBinaryFile('diagram.png', bytes, 'image/png')
      const result = await prepareFileContent(file)

      expect(result.filename).toBe('diagram.png')
      expect(result.contentType).toBe('image/png')
      expect(result.base64Data).toMatch(/^data:image\/png;base64,/)
      expect(result.textContent).toBeUndefined()
    })

    it('returns base64 data URL for jpeg', async () => {
      const bytes = new Uint8Array([0xff, 0xd8, 0xff, 0xe0])
      const file = makeBinaryFile('photo.jpg', bytes, 'image/jpeg')
      const result = await prepareFileContent(file)

      expect(result.filename).toBe('photo.jpg')
      expect(result.contentType).toBe('image/jpeg')
      expect(result.base64Data).toMatch(/^data:image\/jpeg;base64,/)
    })

    it('returns base64 data URL for webp', async () => {
      const bytes = new Uint8Array([0x52, 0x49, 0x46, 0x46])
      const file = makeBinaryFile('image.webp', bytes, 'image/webp')
      const result = await prepareFileContent(file)

      expect(result.contentType).toBe('image/webp')
      expect(result.base64Data).toMatch(/^data:image\/webp;base64,/)
    })

    it('returns base64 data URL for gif', async () => {
      const bytes = new Uint8Array([0x47, 0x49, 0x46, 0x38])
      const file = makeBinaryFile('anim.gif', bytes, 'image/gif')
      const result = await prepareFileContent(file)

      expect(result.contentType).toBe('image/gif')
      expect(result.base64Data).toMatch(/^data:image\/gif;base64,/)
    })
  })

  describe('text files', () => {
    it('returns textContent for plain text', async () => {
      const file = makeFile('notes.txt', 'Hello world', 'text/plain')
      const result = await prepareFileContent(file)

      expect(result.filename).toBe('notes.txt')
      expect(result.contentType).toBe('text/plain')
      expect(result.textContent).toBe('Hello world')
      expect(result.base64Data).toBeUndefined()
    })

    it('returns textContent for JSON', async () => {
      const json = JSON.stringify({ key: 'value' })
      const file = makeFile('config.json', json, 'application/json')
      const result = await prepareFileContent(file)

      expect(result.filename).toBe('config.json')
      expect(result.contentType).toBe('application/json')
      expect(result.textContent).toBe(json)
      expect(result.base64Data).toBeUndefined()
    })
  })

  describe('empty files', () => {
    it('handles empty text file', async () => {
      const file = makeFile('empty.txt', '', 'text/plain')
      const result = await prepareFileContent(file)

      expect(result.filename).toBe('empty.txt')
      expect(result.contentType).toBe('text/plain')
      expect(result.textContent).toBe('')
    })

    it('handles empty image file', async () => {
      const file = makeBinaryFile('empty.png', new Uint8Array([]), 'image/png')
      const result = await prepareFileContent(file)

      expect(result.filename).toBe('empty.png')
      expect(result.contentType).toBe('image/png')
      expect(result.base64Data).toMatch(/^data:image\/png;base64,/)
    })
  })
})

describe('prepareFilesContent (batch)', () => {
  it('processes multiple files successfully', async () => {
    const files = [
      makeFile('readme.txt', 'Hello', 'text/plain'),
      makeBinaryFile('icon.png', new Uint8Array([0x89, 0x50]), 'image/png'),
      makeFile('data.json', '{"a":1}', 'application/json'),
    ]
    const results = await prepareFilesContent(files)

    expect(results).toHaveLength(3)
    expect(results[0].filename).toBe('readme.txt')
    expect(results[0].textContent).toBe('Hello')
    expect(results[1].filename).toBe('icon.png')
    expect(results[1].base64Data).toBeDefined()
    expect(results[2].filename).toBe('data.json')
    expect(results[2].textContent).toBe('{"a":1}')
  })

  it('isolates errors — successful files still return', async () => {
    const goodFile = makeFile('good.txt', 'ok', 'text/plain')
    const brokenFile = makeBrokenFile('broken.txt', 'text/plain')

    const results = await prepareFilesContent([goodFile, brokenFile])

    // Should have result for goodFile, brokenFile is skipped
    expect(results.length).toBe(1)
    expect(results[0].filename).toBe('good.txt')
    expect(results[0].textContent).toBe('ok')
  })

  it('returns empty array when all files fail', async () => {
    const broken1 = makeBrokenFile('a.txt', 'text/plain')
    const broken2 = makeBrokenFile('b.txt', 'text/plain')

    const results = await prepareFilesContent([broken1, broken2])
    expect(results).toEqual([])
  })

  it('returns empty array for empty input', async () => {
    const results = await prepareFilesContent([])
    expect(results).toEqual([])
  })
})

describe('validateAttachments', () => {
  it('accepts files within all limits', () => {
    const files = [
      makeFile('a.txt', 'hello', 'text/plain'),
      makeFile('b.txt', 'world', 'text/plain'),
    ]
    const result = validateAttachments(files)
    expect(result.valid).toBe(true)
    expect(result.error).toBeUndefined()
  })

  it('accepts empty files array', () => {
    const result = validateAttachments([])
    expect(result.valid).toBe(true)
    expect(result.error).toBeUndefined()
  })

  it('rejects when file count exceeds MAX_ATTACHMENT_COUNT', () => {
    const files = Array.from({ length: MAX_ATTACHMENT_COUNT + 1 }, (_, i) =>
      makeFile(`file-${i}.txt`, 'x', 'text/plain')
    )
    const result = validateAttachments(files)
    expect(result.valid).toBe(false)
    expect(result.error).toMatch(/maximum.*\d+.*files/i)
  })

  it('accepts exactly MAX_ATTACHMENT_COUNT files', () => {
    const files = Array.from({ length: MAX_ATTACHMENT_COUNT }, (_, i) =>
      makeFile(`file-${i}.txt`, 'x', 'text/plain')
    )
    const result = validateAttachments(files)
    expect(result.valid).toBe(true)
  })

  it('rejects when a single file exceeds MAX_FILE_SIZE_BYTES', () => {
    // Create a file that reports a size over the limit
    const bigFile = makeFile('huge.txt', 'x', 'text/plain')
    Object.defineProperty(bigFile, 'size', { value: MAX_FILE_SIZE_BYTES + 1 })

    const result = validateAttachments([bigFile])
    expect(result.valid).toBe(false)
    expect(result.error).toMatch(/huge\.txt.*exceeds/i)
  })

  it('accepts a file at exactly MAX_FILE_SIZE_BYTES', () => {
    const file = makeFile('exact.txt', 'x', 'text/plain')
    Object.defineProperty(file, 'size', { value: MAX_FILE_SIZE_BYTES })

    const result = validateAttachments([file])
    expect(result.valid).toBe(true)
  })

  it('rejects when aggregate size exceeds MAX_TOTAL_SIZE_BYTES', () => {
    // Use 4 files of 7MB each = 28MB total, each under 10MB per-file limit
    const sizePerFile = 7 * 1024 * 1024
    const files = Array.from({ length: 4 }, (_, i) => {
      const f = makeFile(`part-${i}.bin`, 'x', 'image/png')
      Object.defineProperty(f, 'size', { value: sizePerFile })
      return f
    })

    const result = validateAttachments(files)
    expect(result.valid).toBe(false)
    expect(result.error).toMatch(/total.*size.*exceeds/i)
  })

  it('accepts files whose aggregate size is exactly MAX_TOTAL_SIZE_BYTES', () => {
    // Use 5 files of 5MB each = 25MB total, each under the 10MB per-file limit
    const fileCount = 5
    const sizePerFile = MAX_TOTAL_SIZE_BYTES / fileCount
    const files = Array.from({ length: fileCount }, (_, i) => {
      const f = makeFile(`part-${i}.bin`, 'x', 'text/plain')
      Object.defineProperty(f, 'size', { value: sizePerFile })
      return f
    })

    const result = validateAttachments(files)
    expect(result.valid).toBe(true)
  })
})

describe('isSupportedMimeType', () => {
  it('accepts supported image types', () => {
    for (const type of SUPPORTED_IMAGE_TYPES) {
      expect(isSupportedMimeType(type)).toBe(true)
    }
  })

  it('accepts supported text types', () => {
    for (const type of SUPPORTED_TEXT_TYPES) {
      expect(isSupportedMimeType(type)).toBe(true)
    }
  })

  it('rejects application/pdf', () => {
    expect(isSupportedMimeType('application/pdf')).toBe(false)
  })

  it('rejects application/zip', () => {
    expect(isSupportedMimeType('application/zip')).toBe(false)
  })

  it('rejects application/octet-stream', () => {
    expect(isSupportedMimeType('application/octet-stream')).toBe(false)
  })

  it('rejects video/mp4', () => {
    expect(isSupportedMimeType('video/mp4')).toBe(false)
  })

  it('rejects empty string', () => {
    expect(isSupportedMimeType('')).toBe(false)
  })
})

describe('prepareFileContent MIME rejection', () => {
  it('throws UnsupportedFileError for PDF files', async () => {
    const file = makeBinaryFile('doc.pdf', new Uint8Array([0x25, 0x50, 0x44, 0x46]), 'application/pdf')
    await expect(prepareFileContent(file)).rejects.toThrow(UnsupportedFileError)
    await expect(prepareFileContent(file)).rejects.toThrow(/doc\.pdf/)
  })

  it('throws UnsupportedFileError for zip files', async () => {
    const file = makeBinaryFile('archive.zip', new Uint8Array([0x50, 0x4b]), 'application/zip')
    await expect(prepareFileContent(file)).rejects.toThrow(UnsupportedFileError)
  })

  it('throws UnsupportedFileError for binary octet-stream', async () => {
    const file = makeBinaryFile('data.bin', new Uint8Array([0x00, 0x01]), 'application/octet-stream')
    await expect(prepareFileContent(file)).rejects.toThrow(UnsupportedFileError)
  })

  it('error message includes the filename and MIME type', async () => {
    const file = makeBinaryFile('report.pdf', new Uint8Array([0x25]), 'application/pdf')
    try {
      await prepareFileContent(file)
      expect.unreachable('should have thrown')
    } catch (err) {
      expect(err).toBeInstanceOf(UnsupportedFileError)
      expect((err as UnsupportedFileError).message).toContain('report.pdf')
      expect((err as UnsupportedFileError).message).toContain('application/pdf')
      expect((err as UnsupportedFileError).filename).toBe('report.pdf')
      expect((err as UnsupportedFileError).mimeType).toBe('application/pdf')
    }
  })
})

describe('prepareFilesContent with unsupported files', () => {
  it('skips unsupported files and processes supported ones', async () => {
    const files = [
      makeFile('good.txt', 'hello', 'text/plain'),
      makeBinaryFile('bad.pdf', new Uint8Array([0x25]), 'application/pdf'),
      makeBinaryFile('good.png', new Uint8Array([0x89, 0x50]), 'image/png'),
    ]
    const results = await prepareFilesContent(files)
    expect(results).toHaveLength(2)
    expect(results[0].filename).toBe('good.txt')
    expect(results[1].filename).toBe('good.png')
  })
})
