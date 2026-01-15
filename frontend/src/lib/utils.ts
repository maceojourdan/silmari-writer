/**
 * Utility functions for the writing agent UI
 */

/**
 * Format bytes into a human-readable string
 * @param bytes - Number of bytes to format
 * @returns Formatted string (e.g., "1.46 KB", "5 MB")
 */
export function formatBytes(bytes: number): string {
  if (bytes === 0) return '0 Bytes'
  const k = 1024
  const sizes = ['Bytes', 'KB', 'MB', 'GB']
  const i = Math.floor(Math.log(bytes) / Math.log(k))
  return Math.round((bytes / Math.pow(k, i)) * 100) / 100 + ' ' + sizes[i]
}
