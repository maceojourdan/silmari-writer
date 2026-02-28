import {
  SUPPORTED_IMAGE_TYPES,
  SUPPORTED_TEXT_TYPES,
  SUPPORTED_DOCUMENT_TYPES,
  isSupportedMimeType,
} from './attachment-types'

export { SUPPORTED_IMAGE_TYPES, SUPPORTED_TEXT_TYPES, SUPPORTED_DOCUMENT_TYPES, isSupportedMimeType }

export const MAX_ATTACHMENT_COUNT = 10
export const MAX_FILE_SIZE_BYTES = 10 * 1024 * 1024
export const MAX_TOTAL_SIZE_BYTES = 25 * 1024 * 1024

export interface AttachmentValidationResult {
  valid: boolean
  error?: string
}

export class UnsupportedFileError extends Error {
  filename: string
  mimeType: string

  constructor(filename: string, mimeType: string) {
    super(
      `Unsupported file type: "${filename}" (${mimeType}). Only images (PNG, JPEG, GIF, WebP), text (plain text, JSON, CSV), and documents (PDF, Word, Excel) are supported.`,
    )
    this.name = 'UnsupportedFileError'
    this.filename = filename
    this.mimeType = mimeType
  }
}

export interface FileContentPayload {
  filename: string
  contentType: string
  textContent?: string
  base64Data?: string
  rawBlob?: string
}

export function validateAttachments(files: File[]): AttachmentValidationResult {
  if (files.length === 0) {
    return { valid: true }
  }

  if (files.length > MAX_ATTACHMENT_COUNT) {
    return {
      valid: false,
      error: `Maximum ${MAX_ATTACHMENT_COUNT} files allowed`,
    }
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

function readAsDataURL(file: File): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader()
    reader.onload = () => resolve(reader.result as string)
    reader.onerror = () => reject(reader.error ?? new Error('Failed to read file as data URL'))
    reader.readAsDataURL(file)
  })
}

function readAsText(file: File): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader()
    reader.onload = () => resolve(reader.result as string)
    reader.onerror = () => reject(reader.error ?? new Error('Failed to read file as text'))
    reader.readAsText(file)
  })
}

function readAsArrayBuffer(file: File): Promise<ArrayBuffer> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader()
    reader.onload = () => resolve(reader.result as ArrayBuffer)
    reader.onerror = () => reject(reader.error ?? new Error('Failed to read file as array buffer'))
    reader.readAsArrayBuffer(file)
  })
}

function arrayBufferToBase64(buffer: ArrayBuffer): string {
  const bytes = new Uint8Array(buffer)
  let binary = ''
  for (let i = 0; i < bytes.byteLength; i++) {
    binary += String.fromCharCode(bytes[i])
  }
  return btoa(binary)
}

export async function prepareFileContent(file: File): Promise<FileContentPayload> {
  const filename = file.name
  const contentType = file.type

  if (SUPPORTED_IMAGE_TYPES.has(contentType)) {
    const base64Data = await readAsDataURL(file)
    return { filename, contentType, base64Data }
  }

  if (SUPPORTED_TEXT_TYPES.has(contentType)) {
    const textContent = await readAsText(file)
    return { filename, contentType, textContent }
  }

  if (SUPPORTED_DOCUMENT_TYPES.has(contentType)) {
    const buffer = await readAsArrayBuffer(file)
    const rawBlob = arrayBufferToBase64(buffer)
    return { filename, contentType, rawBlob }
  }

  throw new UnsupportedFileError(filename, contentType)
}

export async function prepareFilesContent(files: File[]): Promise<FileContentPayload[]> {
  const payloads: FileContentPayload[] = []

  for (const file of files) {
    payloads.push(await prepareFileContent(file))
  }

  return payloads
}
