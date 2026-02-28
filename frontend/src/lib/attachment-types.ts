export const SUPPORTED_IMAGE_TYPES = new Set([
  'image/png',
  'image/jpeg',
  'image/gif',
  'image/webp',
])

export const SUPPORTED_TEXT_TYPES = new Set([
  'text/plain',
  'text/csv',
  'application/json',
])

export const SUPPORTED_DOCUMENT_TYPES = new Set([
  'application/pdf',
  'application/msword',
  'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
  'application/vnd.ms-excel',
  'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
])

export const ALL_SUPPORTED_TYPES = new Set([
  ...SUPPORTED_IMAGE_TYPES,
  ...SUPPORTED_TEXT_TYPES,
  ...SUPPORTED_DOCUMENT_TYPES,
])

export function isSupportedMimeType(mimeType: string): boolean {
  return ALL_SUPPORTED_TYPES.has(mimeType)
}
