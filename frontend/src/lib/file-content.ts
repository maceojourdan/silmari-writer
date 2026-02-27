// --- Attachment limits ---
export const MAX_ATTACHMENT_COUNT = 10
export const MAX_FILE_SIZE_BYTES = 10 * 1024 * 1024   // 10 MB per file
export const MAX_TOTAL_SIZE_BYTES = 25 * 1024 * 1024   // 25 MB aggregate

export interface AttachmentValidationResult {
  valid: boolean
  error?: string
}

export function validateAttachments(files: File[]): AttachmentValidationResult {
  if (files.length === 0) {
    return { valid: true }
  }

  if (files.length > MAX_ATTACHMENT_COUNT) {
    return { valid: false, error: `Maximum ${MAX_ATTACHMENT_COUNT} files allowed` }
  }

  let totalSize = 0
  for (const file of files) {
    if (file.size > MAX_FILE_SIZE_BYTES) {
      return {
        valid: false,
        error: `${file.name} exceeds the ${(MAX_FILE_SIZE_BYTES / (1024 * 1024)).toFixed(0)} MB per-file limit`,
      }
    }
    totalSize += file.size
  }

  if (totalSize > MAX_TOTAL_SIZE_BYTES) {
    return {
      valid: false,
      error: `Total attachment size exceeds the ${(MAX_TOTAL_SIZE_BYTES / (1024 * 1024)).toFixed(0)} MB limit`,
    }
  }

  return { valid: true }
}

// --- Supported MIME types ---
export const SUPPORTED_IMAGE_TYPES = new Set([
  'image/png',
  'image/jpeg',
  'image/gif',
  'image/webp',
])

export const SUPPORTED_TEXT_TYPES = new Set([
  'text/plain',
  'application/json',
])

export function isSupportedMimeType(mimeType: string): boolean {
  return SUPPORTED_IMAGE_TYPES.has(mimeType) || SUPPORTED_TEXT_TYPES.has(mimeType)
}

export class UnsupportedFileError extends Error {
  constructor(
    public readonly filename: string,
    public readonly mimeType: string,
  ) {
    super(`Unsupported file type: "${filename}" (${mimeType}). Only images (PNG, JPEG, GIF, WebP) and text (plain text, JSON) files are supported.`)
    this.name = 'UnsupportedFileError'
  }
}

export interface FileContentPayload {
  filename: string
  contentType: string
  textContent?: string
  base64Data?: string
}

function readAsDataURL(file: File): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader()
    reader.onload = () => resolve(reader.result as string)
    reader.onerror = () => reject(reader.error)
    reader.readAsDataURL(file)
  })
}

function readAsText(file: File): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader()
    reader.onload = () => resolve(reader.result as string)
    reader.onerror = () => reject(reader.error)
    reader.readAsText(file)
  })
}

export async function prepareFileContent(file: File): Promise<FileContentPayload> {
  const { name: filename, type: contentType } = file

  if (!isSupportedMimeType(contentType)) {
    throw new UnsupportedFileError(filename, contentType)
  }

  if (SUPPORTED_IMAGE_TYPES.has(contentType)) {
    const dataUrl = await readAsDataURL(file)
    return {
      filename,
      contentType,
      base64Data: dataUrl,
    }
  }

  const text = await readAsText(file)
  return {
    filename,
    contentType,
    textContent: text,
  }
}

export async function prepareFilesContent(files: File[]): Promise<FileContentPayload[]> {
  const results: FileContentPayload[] = []

  for (const file of files) {
    try {
      const payload = await prepareFileContent(file)
      results.push(payload)
    } catch (err) {
      console.error(`Failed to process file "${file.name}":`, err)
    }
  }

  return results
}
