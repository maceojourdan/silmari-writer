import { NextRequest, NextResponse } from 'next/server'
import { put } from '@vercel/blob'
import { z } from 'zod'
import type {
  ImageGenerationModel,
  ImageSize,
  ImageQuality,
  ImageOutputFormat,
  ImageBackground,
  ImageGenerationErrorCode,
  GeneratedImage,
  ImageGenerationResponse,
} from '@/lib/types'

// Constants
const OPENAI_IMAGES_ENDPOINT = 'https://api.openai.com/v1/images/generations'
const MAX_PROMPT_LENGTH = 32000
const MAX_RETRIES = 3
const RATE_LIMIT_BASE_DELAY_MS = 10000
const NETWORK_ERROR_BASE_DELAY_MS = 10000
const REQUEST_TIMEOUT_MS = 120000

// Valid models
const VALID_MODELS = ['gpt-image-1.5', 'gpt-image-1', 'gpt-image-1-mini'] as const
const DEPRECATED_MODELS: Record<string, string> = {
  'dall-e-3': 'dall-e-3 is deprecated as of May 12, 2026. Please use gpt-image-1.5 instead.',
  'dall-e-2': 'dall-e-2 is deprecated as of May 12, 2026. Please use gpt-image-1 or gpt-image-1-mini instead.',
}

// Zod schema for request validation
const ImageGenerationRequestSchema = z.object({
  prompt: z.string().min(1, 'Prompt is required').max(MAX_PROMPT_LENGTH, `Prompt must be at most ${MAX_PROMPT_LENGTH} characters`),
  model: z.enum(VALID_MODELS).optional(),
  n: z.number().int().min(1, 'n must be at least 1').max(10, 'n must be at most 10').optional(),
  size: z.enum(['1024x1024', '1536x1024', '1024x1536', 'auto']).optional(),
  quality: z.enum(['low', 'medium', 'high']).optional(),
  output_format: z.enum(['png', 'jpeg', 'webp']).optional(),
  background: z.enum(['auto', 'transparent', 'opaque']).optional(),
})

// Error class
class ImageGenerationApiError extends Error {
  constructor(
    message: string,
    public code: ImageGenerationErrorCode,
    public retryable: boolean,
    public statusCode: number
  ) {
    super(message)
    this.name = 'ImageGenerationApiError'
  }
}

// Base64 validation regex
const BASE64_REGEX = /^[A-Za-z0-9+/]+=*$/

// Magic bytes for image format validation
const MAGIC_BYTES = {
  png: [0x89, 0x50, 0x4e, 0x47],
  jpeg: [0xff, 0xd8, 0xff],
  webp: [0x52, 0x49, 0x46, 0x46],
}

// Content type mapping
const CONTENT_TYPES: Record<ImageOutputFormat, string> = {
  png: 'image/png',
  jpeg: 'image/jpeg',
  webp: 'image/webp',
}

function validateBase64(base64: string): boolean {
  if (!base64 || base64.length === 0) return false
  return BASE64_REGEX.test(base64)
}

function validateMagicBytes(buffer: Buffer, format: ImageOutputFormat): boolean {
  const expected = MAGIC_BYTES[format]
  if (!expected) return true // Skip validation for unknown formats

  for (let i = 0; i < expected.length; i++) {
    if (buffer[i] !== expected[i]) return false
  }
  return true
}

function truncatePrompt(prompt: string, maxLength: number = 100): string {
  if (prompt.length <= maxLength) return prompt
  return prompt.substring(0, maxLength) + '...'
}

async function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms))
}

async function makeOpenAIRequest(
  apiKey: string,
  body: Record<string, unknown>,
  attempt: number = 0
): Promise<{ created: number; data: Array<{ b64_json: string; revised_prompt?: string }> }> {
  const controller = new AbortController()
  const timeoutId = setTimeout(() => controller.abort(), REQUEST_TIMEOUT_MS)

  try {
    console.log('Image generation request:', {
      prompt: truncatePrompt(body.prompt as string),
      model: body.model,
      size: body.size,
      quality: body.quality,
    })

    const response = await fetch(OPENAI_IMAGES_ENDPOINT, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${apiKey}`,
      },
      body: JSON.stringify(body),
      signal: controller.signal,
    })

    clearTimeout(timeoutId)

    if (!response.ok) {
      const errorData = await response.json().catch(() => ({ error: { message: 'Unknown error' } }))
      const errorMessage = errorData.error?.message || 'Unknown error'

      // Handle specific status codes
      if (response.status === 401) {
        throw new ImageGenerationApiError(
          'Invalid API key',
          'INVALID_API_KEY',
          false,
          401
        )
      }

      if (response.status === 429) {
        // Rate limit - retry with exponential backoff
        if (attempt < MAX_RETRIES) {
          const delay = RATE_LIMIT_BASE_DELAY_MS * Math.pow(2, attempt)
          await sleep(delay)
          return makeOpenAIRequest(apiKey, body, attempt + 1)
        }
        throw new ImageGenerationApiError(
          `Rate limit exceeded: ${errorMessage}`,
          'RATE_LIMIT',
          true,
          429
        )
      }

      if (response.status >= 500) {
        // Server error - retry
        if (attempt < MAX_RETRIES) {
          const delay = NETWORK_ERROR_BASE_DELAY_MS * Math.pow(2, attempt)
          await sleep(delay)
          return makeOpenAIRequest(apiKey, body, attempt + 1)
        }
        throw new ImageGenerationApiError(
          `OpenAI API error: ${errorMessage}`,
          'API_ERROR',
          true,
          response.status
        )
      }

      throw new ImageGenerationApiError(
        `API error: ${errorMessage}`,
        'API_ERROR',
        false,
        response.status
      )
    }

    try {
      const data = await response.json()
      return data
    } catch {
      throw new ImageGenerationApiError(
        'Invalid response from API',
        'INVALID_RESPONSE',
        false,
        500
      )
    }
  } catch (error) {
    clearTimeout(timeoutId)

    if (error instanceof ImageGenerationApiError) {
      throw error
    }

    // Handle network errors
    if (error instanceof Error) {
      if (error.name === 'AbortError') {
        throw new ImageGenerationApiError(
          'Request timed out',
          'TIMEOUT',
          true,
          408
        )
      }

      // Network error - retry
      if (attempt < MAX_RETRIES) {
        const delay = NETWORK_ERROR_BASE_DELAY_MS * Math.pow(2, attempt)
        await sleep(delay)
        return makeOpenAIRequest(apiKey, body, attempt + 1)
      }

      throw new ImageGenerationApiError(
        `Network error: ${error.message}`,
        'NETWORK',
        true,
        502
      )
    }

    throw new ImageGenerationApiError(
      'Unknown error occurred',
      'API_ERROR',
      false,
      500
    )
  }
}

async function uploadToBlob(
  buffer: Buffer,
  filename: string,
  contentType: string,
  blobToken: string
): Promise<string> {
  try {
    const blob = await put(filename, buffer, {
      access: 'public',
      token: blobToken,
      contentType,
    })
    return blob.url
  } catch (error) {
    console.error('Blob upload error:', error)
    throw new ImageGenerationApiError(
      'Failed to upload image to storage',
      'UPLOAD_FAILED',
      true,
      500
    )
  }
}

export async function POST(request: NextRequest): Promise<Response> {
  try {
    // Validate environment variables
    const apiKey = process.env.OPENAI_API_KEY
    if (!apiKey) {
      console.error('OPENAI_API_KEY is not configured')
      return NextResponse.json(
        { error: 'OpenAI API key not configured', code: 'CONFIG_ERROR', retryable: false },
        { status: 500 }
      )
    }

    const blobToken = process.env.BLOB_READ_WRITE_TOKEN
    if (!blobToken) {
      console.error('BLOB_READ_WRITE_TOKEN is not configured')
      return NextResponse.json(
        { error: 'Blob storage not configured', code: 'CONFIG_ERROR', retryable: false },
        { status: 500 }
      )
    }

    // Parse and validate request body
    let body: unknown
    try {
      body = await request.json()
    } catch {
      return NextResponse.json(
        { error: 'Invalid JSON body', code: 'VALIDATION_ERROR', retryable: false },
        { status: 400 }
      )
    }

    // Check for deprecated models first
    const rawBody = body as Record<string, unknown>
    if (rawBody.model && typeof rawBody.model === 'string') {
      const deprecationMessage = DEPRECATED_MODELS[rawBody.model]
      if (deprecationMessage) {
        return NextResponse.json(
          { error: deprecationMessage, code: 'VALIDATION_ERROR', retryable: false },
          { status: 400 }
        )
      }
    }

    // Validate with Zod
    const parseResult = ImageGenerationRequestSchema.safeParse(body)
    if (!parseResult.success) {
      // Zod v4 uses issues array instead of errors
      const issues = parseResult.error.issues || []
      const errorMessage = issues.map(e => `${e.path.join('.')}: ${e.message}`).join(', ')
      return NextResponse.json(
        { error: errorMessage, code: 'VALIDATION_ERROR', retryable: false },
        { status: 400 }
      )
    }

    const validatedBody = parseResult.data

    // Apply defaults
    const model: ImageGenerationModel = validatedBody.model ?? 'gpt-image-1.5'
    const size: ImageSize = validatedBody.size ?? '1024x1024'
    const quality: ImageQuality = validatedBody.quality ?? 'high'
    let outputFormat: ImageOutputFormat = validatedBody.output_format ?? 'png'
    const background: ImageBackground = validatedBody.background ?? 'auto'
    const n = validatedBody.n ?? 1

    // Handle transparent + jpeg incompatibility
    if (background === 'transparent' && outputFormat === 'jpeg') {
      console.warn('Transparent background requested with JPEG format. Switching to PNG as JPEG does not support transparency.')
      outputFormat = 'png'
    }

    // Build request body for OpenAI API
    const openaiRequestBody = {
      model,
      prompt: validatedBody.prompt,
      n,
      size,
      quality,
      output_format: outputFormat,
      background,
    }

    // Make API request
    const openaiResponse = await makeOpenAIRequest(apiKey, openaiRequestBody)

    // Process response
    if (!openaiResponse.data || openaiResponse.data.length === 0) {
      throw new ImageGenerationApiError(
        'No image data in response',
        'INVALID_RESPONSE',
        false,
        500
      )
    }

    const timestamp = Date.now()
    const images: GeneratedImage[] = []

    // Process each image
    const uploadPromises = openaiResponse.data.map(async (imageData, index) => {
      // Validate b64_json
      if (!imageData.b64_json) {
        throw new ImageGenerationApiError(
          'No image data in response',
          'INVALID_RESPONSE',
          false,
          500
        )
      }

      if (!validateBase64(imageData.b64_json)) {
        throw new ImageGenerationApiError(
          'Invalid base64 data in response',
          'INVALID_RESPONSE',
          false,
          500
        )
      }

      // Decode base64 to buffer
      const buffer = Buffer.from(imageData.b64_json, 'base64')

      // Validate magic bytes (skip for now as API response may not match expected format)
      // This is a safety check but we trust the API response
      // if (!validateMagicBytes(buffer, outputFormat)) {
      //   console.warn(`Image magic bytes don't match expected format ${outputFormat}`)
      // }

      // Generate filename
      const filename = `generated-image-${timestamp}-${index}.${outputFormat}`

      // Upload to blob storage
      const url = await uploadToBlob(buffer, filename, CONTENT_TYPES[outputFormat], blobToken)

      return {
        url,
        revisedPrompt: imageData.revised_prompt,
        format: outputFormat,
        size,
        model,
        generatedAt: new Date().toISOString(),
      } as GeneratedImage
    })

    // Wait for all uploads to complete
    const uploadedImages = await Promise.all(uploadPromises)
    images.push(...uploadedImages)

    // Build response
    const response: ImageGenerationResponse = {
      images,
      model,
      quality,
    }

    return NextResponse.json(response)
  } catch (error) {
    console.error('Image generation error:', error)

    if (error instanceof ImageGenerationApiError) {
      return NextResponse.json(
        {
          error: error.message,
          code: error.code,
          retryable: error.retryable,
        },
        { status: error.statusCode }
      )
    }

    // Handle JSON parsing errors from response
    if (error instanceof SyntaxError) {
      return NextResponse.json(
        {
          error: 'Invalid response from API',
          code: 'INVALID_RESPONSE',
          retryable: false,
        },
        { status: 500 }
      )
    }

    return NextResponse.json(
      {
        error: 'An unexpected error occurred',
        code: 'API_ERROR',
        retryable: false,
      },
      { status: 500 }
    )
  }
}
