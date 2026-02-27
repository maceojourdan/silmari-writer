import { TranscriptionOptions, TranscriptionError, TranscriptionErrorCode } from './types'

// Constants
export const MAX_FILE_SIZE_MB = 25
export const MAX_FILE_SIZE_BYTES = MAX_FILE_SIZE_MB * 1024 * 1024

/**
 * Transcribes audio using the server-side API route
 * The API route handles the OpenAI Whisper call with the API key securely
 * Uses Vercel Blob storage to bypass the 4.5MB serverless function body limit
 *
 * @param audioBlob - Audio file as a Blob (max 25MB)
 * @param options - Optional transcription settings (language)
 * @returns Transcribed text
 * @throws TranscriptionError with appropriate error code
 */
export async function transcribeAudio(
  audioBlob: Blob,
  options?: TranscriptionOptions
): Promise<string> {
  // Validate file size client-side for immediate feedback
  if (audioBlob.size > MAX_FILE_SIZE_BYTES) {
    const actualSizeMB = (audioBlob.size / (1024 * 1024)).toFixed(1)
    throw new TranscriptionError(
      `File size ${actualSizeMB}MB exceeds ${MAX_FILE_SIZE_MB}MB limit. Try recording a shorter audio clip.`,
      'FILE_TOO_LARGE',
      false
    )
  }

  // Step 1: Upload to Vercel Blob
  let blobUrl: string
  try {
    const uploadFormData = new FormData()
    const extension = audioBlob.type.includes('mp4') ? 'mp4' : 'webm'
    uploadFormData.append('file', audioBlob, `recording-${Date.now()}.${extension}`)

    const uploadResponse = await fetch('/api/upload', {
      method: 'POST',
      body: uploadFormData,
    })

    if (!uploadResponse.ok) {
      const uploadData = await uploadResponse.json()
      throw new TranscriptionError(
        uploadData.error || 'Failed to upload file',
        uploadData.code || 'UPLOAD_ERROR',
        false
      )
    }

    const uploadData = await uploadResponse.json()
    blobUrl = uploadData.url
  } catch (error) {
    if (error instanceof TranscriptionError) {
      throw error
    }
    throw new TranscriptionError(
      `Upload failed: ${error instanceof Error ? error.message : 'Unknown error'}`,
      'UPLOAD_ERROR',
      true
    )
  }

  // Step 2: Transcribe from blob URL
  let response: Response
  try {
    const transcribePayload = {
      blobUrl,
      ...(options?.language ? { language: options.language } : {}),
    }

    response = await fetch('/api/transcribe', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(transcribePayload),
    })
  } catch (error) {
    throw new TranscriptionError(
      `Network error: ${error instanceof Error ? error.message : 'Unknown error'}`,
      'NETWORK',
      true
    )
  }

  let data: { text?: string; error?: string; code?: TranscriptionErrorCode; retryable?: boolean }
  try {
    data = await response.json()
  } catch {
    throw new TranscriptionError(
      'Invalid response from transcription service',
      'API_ERROR',
      true
    )
  }

  if (!response.ok) {
    throw new TranscriptionError(
      data.error || 'Transcription failed',
      data.code || 'API_ERROR',
      data.retryable ?? false
    )
  }

  if (!data.text) {
    throw new TranscriptionError(
      'Transcription returned empty result',
      'API_ERROR',
      true
    )
  }

  return data.text
}
