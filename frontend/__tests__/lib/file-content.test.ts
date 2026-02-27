import { describe, expect, it } from 'vitest'
import {
  prepareFileContent,
  prepareFilesContent,
  validateAttachments,
  MAX_ATTACHMENT_COUNT,
  MAX_FILE_SIZE_BYTES,
  UnsupportedFileError,
} from '@/lib/file-content'

function makeFile(name: string, contents: string | Uint8Array, type: string): File {
  const blobPart: BlobPart =
    typeof contents === 'string' ? contents : (contents as unknown as BlobPart)
  return new File([blobPart], name, { type })
}

describe('file-content helpers', () => {
  it('prepares text file payloads', async () => {
    const file = makeFile('notes.txt', 'hello world', 'text/plain')
    const payload = await prepareFileContent(file)

    expect(payload).toEqual({
      filename: 'notes.txt',
      contentType: 'text/plain',
      textContent: 'hello world',
    })
  })

  it('prepares image payloads as data URL', async () => {
    const file = makeFile('image.png', new Uint8Array([0x89, 0x50, 0x4e, 0x47]), 'image/png')
    const payload = await prepareFileContent(file)

    expect(payload.filename).toBe('image.png')
    expect(payload.contentType).toBe('image/png')
    expect(payload.base64Data).toMatch(/^data:image\/png;base64,/)
  })

  it('throws UnsupportedFileError for unsupported MIME types', async () => {
    const file = makeFile('report.pdf', '%PDF', 'application/pdf')

    await expect(prepareFileContent(file)).rejects.toBeInstanceOf(UnsupportedFileError)
    await expect(prepareFileContent(file)).rejects.toThrow(/report\.pdf/i)
  })

  it('keeps deterministic ordering for batch payload preparation', async () => {
    const files = [
      makeFile('a.txt', 'A', 'text/plain'),
      makeFile('b.json', '{"b":1}', 'application/json'),
    ]
    const payloads = await prepareFilesContent(files)

    expect(payloads.map((p) => p.filename)).toEqual(['a.txt', 'b.json'])
  })

  it('fails fast when unsupported file appears in batch', async () => {
    const files = [
      makeFile('ok.txt', 'ok', 'text/plain'),
      makeFile('bad.pdf', '%PDF', 'application/pdf'),
    ]

    await expect(prepareFilesContent(files)).rejects.toBeInstanceOf(UnsupportedFileError)
  })

  it('rejects too many files in validation', () => {
    const files = Array.from({ length: MAX_ATTACHMENT_COUNT + 1 }, (_, i) =>
      makeFile(`f-${i}.txt`, 'x', 'text/plain'),
    )
    const result = validateAttachments(files)
    expect(result.valid).toBe(false)
    expect(result.error).toMatch(/maximum/i)
  })

  it('rejects oversized files in validation', () => {
    const file = makeFile('big.txt', 'x', 'text/plain')
    Object.defineProperty(file, 'size', { value: MAX_FILE_SIZE_BYTES + 1 })

    const result = validateAttachments([file])
    expect(result.valid).toBe(false)
    expect(result.error).toMatch(/exceeds/i)
  })
})
