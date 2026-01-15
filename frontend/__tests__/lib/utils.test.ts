import { describe, it, expect } from 'vitest'
import { formatBytes } from '@/lib/utils'

describe('formatBytes', () => {
  it('returns "0 Bytes" for 0', () => {
    expect(formatBytes(0)).toBe('0 Bytes')
  })

  it('formats bytes correctly', () => {
    expect(formatBytes(100)).toBe('100 Bytes')
    expect(formatBytes(1023)).toBe('1023 Bytes')
  })

  it('formats kilobytes correctly', () => {
    expect(formatBytes(1024)).toBe('1 KB')
    expect(formatBytes(1500)).toBe('1.46 KB')
    expect(formatBytes(10240)).toBe('10 KB')
  })

  it('formats megabytes correctly', () => {
    expect(formatBytes(1048576)).toBe('1 MB')
    expect(formatBytes(5242880)).toBe('5 MB')
    expect(formatBytes(10485760)).toBe('10 MB')
  })

  it('formats gigabytes correctly', () => {
    expect(formatBytes(1073741824)).toBe('1 GB')
    expect(formatBytes(5368709120)).toBe('5 GB')
  })
})
