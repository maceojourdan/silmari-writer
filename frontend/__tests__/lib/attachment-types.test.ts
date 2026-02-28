import { describe, expect, it } from 'vitest'
import {
  SUPPORTED_IMAGE_TYPES,
  SUPPORTED_TEXT_TYPES,
  SUPPORTED_DOCUMENT_TYPES,
  ALL_SUPPORTED_TYPES,
  isSupportedMimeType,
} from '@/lib/attachment-types'

describe('attachment-types', () => {
  describe('SUPPORTED_IMAGE_TYPES', () => {
    it.each(['image/png', 'image/jpeg', 'image/gif', 'image/webp'])(
      'includes %s',
      (mime) => {
        expect(SUPPORTED_IMAGE_TYPES.has(mime)).toBe(true)
      },
    )

    it('does not include non-image types', () => {
      expect(SUPPORTED_IMAGE_TYPES.has('text/plain')).toBe(false)
      expect(SUPPORTED_IMAGE_TYPES.has('application/pdf')).toBe(false)
    })
  })

  describe('SUPPORTED_TEXT_TYPES', () => {
    it.each(['text/plain', 'text/csv', 'application/json'])(
      'includes %s',
      (mime) => {
        expect(SUPPORTED_TEXT_TYPES.has(mime)).toBe(true)
      },
    )

    it('does not include image types', () => {
      expect(SUPPORTED_TEXT_TYPES.has('image/png')).toBe(false)
    })
  })

  describe('SUPPORTED_DOCUMENT_TYPES', () => {
    it.each([
      'application/pdf',
      'application/msword',
      'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
      'application/vnd.ms-excel',
      'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
    ])('includes %s', (mime) => {
      expect(SUPPORTED_DOCUMENT_TYPES.has(mime)).toBe(true)
    })

    it('does not include image or text types', () => {
      expect(SUPPORTED_DOCUMENT_TYPES.has('image/png')).toBe(false)
      expect(SUPPORTED_DOCUMENT_TYPES.has('text/plain')).toBe(false)
    })
  })

  describe('ALL_SUPPORTED_TYPES', () => {
    it('is the union of image, text, and document types', () => {
      for (const mime of SUPPORTED_IMAGE_TYPES) {
        expect(ALL_SUPPORTED_TYPES.has(mime)).toBe(true)
      }
      for (const mime of SUPPORTED_TEXT_TYPES) {
        expect(ALL_SUPPORTED_TYPES.has(mime)).toBe(true)
      }
      for (const mime of SUPPORTED_DOCUMENT_TYPES) {
        expect(ALL_SUPPORTED_TYPES.has(mime)).toBe(true)
      }
    })

    it('has the correct cardinality', () => {
      expect(ALL_SUPPORTED_TYPES.size).toBe(
        SUPPORTED_IMAGE_TYPES.size + SUPPORTED_TEXT_TYPES.size + SUPPORTED_DOCUMENT_TYPES.size,
      )
    })
  })

  describe('isSupportedMimeType', () => {
    it('returns true for supported image types', () => {
      expect(isSupportedMimeType('image/png')).toBe(true)
      expect(isSupportedMimeType('image/jpeg')).toBe(true)
    })

    it('returns true for supported text types', () => {
      expect(isSupportedMimeType('text/plain')).toBe(true)
      expect(isSupportedMimeType('application/json')).toBe(true)
    })

    it('returns true for csv', () => {
      expect(isSupportedMimeType('text/csv')).toBe(true)
    })

    it('returns true for supported document types', () => {
      expect(isSupportedMimeType('application/pdf')).toBe(true)
      expect(isSupportedMimeType('application/msword')).toBe(true)
    })

    it('returns false for unsupported types', () => {
      expect(isSupportedMimeType('application/zip')).toBe(false)
      expect(isSupportedMimeType('video/mp4')).toBe(false)
      expect(isSupportedMimeType('')).toBe(false)
    })
  })
})
