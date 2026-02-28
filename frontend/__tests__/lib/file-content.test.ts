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

  it('routes application/json explicitly as text content', async () => {
    const file = makeFile('data.json', '{"key":"value"}', 'application/json')
    const payload = await prepareFileContent(file)

    expect(payload).toEqual({
      filename: 'data.json',
      contentType: 'application/json',
      textContent: '{"key":"value"}',
    })
  })

  it('routes text/csv as text content', async () => {
    const file = makeFile('data.csv', 'a,b,c\n1,2,3', 'text/csv')
    const payload = await prepareFileContent(file)

    expect(payload).toEqual({
      filename: 'data.csv',
      contentType: 'text/csv',
      textContent: 'a,b,c\n1,2,3',
    })
  })

  it('prepares PDF as rawBlob (not readAsText)', async () => {
    const pdfBytes = new Uint8Array([0x25, 0x50, 0x44, 0x46]) // %PDF
    const file = makeFile('report.pdf', pdfBytes, 'application/pdf')
    const payload = await prepareFileContent(file)

    expect(payload.filename).toBe('report.pdf')
    expect(payload.contentType).toBe('application/pdf')
    expect(payload.rawBlob).toBeDefined()
    expect(typeof payload.rawBlob).toBe('string')
    expect(payload.textContent).toBeUndefined()
    expect(payload.base64Data).toBeUndefined()
  })

  it('prepares DOCX as rawBlob', async () => {
    const docxBytes = new Uint8Array([0x50, 0x4b, 0x03, 0x04]) // PK zip header
    const file = makeFile('doc.docx', docxBytes, 'application/vnd.openxmlformats-officedocument.wordprocessingml.document')
    const payload = await prepareFileContent(file)

    expect(payload.filename).toBe('doc.docx')
    expect(payload.rawBlob).toBeDefined()
    expect(payload.textContent).toBeUndefined()
  })

  it('throws UnsupportedFileError for truly unsupported MIME types', async () => {
    const file = makeFile('video.mp4', 'data', 'video/mp4')

    await expect(prepareFileContent(file)).rejects.toBeInstanceOf(UnsupportedFileError)
    await expect(prepareFileContent(file)).rejects.toThrow(/video\.mp4/i)
  })

  it('rejects .zip files with UnsupportedFileError', async () => {
    const file = makeFile('archive.zip', 'PK', 'application/zip')

    await expect(prepareFileContent(file)).rejects.toBeInstanceOf(UnsupportedFileError)
    await expect(prepareFileContent(file)).rejects.toThrow(/archive\.zip/i)
  })

  it('keeps deterministic ordering for batch payload preparation', async () => {
    const files = [
      makeFile('a.txt', 'A', 'text/plain'),
      makeFile('b.json', '{"b":1}', 'application/json'),
    ]
    const payloads = await prepareFilesContent(files)

    expect(payloads.map((p) => p.filename)).toEqual(['a.txt', 'b.json'])
  })

  it('handles mixed batch with documents', async () => {
    const files = [
      makeFile('ok.txt', 'ok', 'text/plain'),
      makeFile('doc.pdf', new Uint8Array([0x25, 0x50, 0x44, 0x46]), 'application/pdf'),
    ]
    const payloads = await prepareFilesContent(files)

    expect(payloads).toHaveLength(2)
    expect(payloads[0].textContent).toBe('ok')
    expect(payloads[1].rawBlob).toBeDefined()
  })

  it('fails fast when unsupported file appears in batch', async () => {
    const files = [
      makeFile('ok.txt', 'ok', 'text/plain'),
      makeFile('bad.exe', 'MZ', 'application/x-msdownload'),
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
