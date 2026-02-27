import { NextRequest, NextResponse } from 'next/server'
import { put } from '@vercel/blob'

const MAX_FILE_SIZE_MB = 25
const MAX_FILE_SIZE_BYTES = MAX_FILE_SIZE_MB * 1024 * 1024
type BlobAccess = 'public' | 'private'

function getPreferredBlobAccess(): BlobAccess {
  const configured = process.env.BLOB_ACCESS
  return configured === 'public' || configured === 'private' ? configured : 'private'
}

function getRequiredBlobAccessFromError(error: unknown): BlobAccess | null {
  const message = error instanceof Error ? error.message : String(error)

  if (message.includes('access must be "public"')) {
    return 'public'
  }
  if (message.includes('access must be "private"')) {
    return 'private'
  }

  return null
}

async function uploadWithCompatibleAccess(
  filename: string,
  file: File,
  blobReadWriteToken: string
) {
  const preferredAccess = getPreferredBlobAccess()

  try {
    return await put(filename, file, {
      access: preferredAccess,
      token: blobReadWriteToken,
    } as unknown as Parameters<typeof put>[2])
  } catch (error) {
    const requiredAccess = getRequiredBlobAccessFromError(error)

    if (requiredAccess && requiredAccess !== preferredAccess) {
      console.warn(
        `Blob access mismatch: configured "${preferredAccess}", retrying with "${requiredAccess}"`
      )
      return put(filename, file, {
        access: requiredAccess,
        token: blobReadWriteToken,
      } as unknown as Parameters<typeof put>[2])
    }

    throw error
  }
}

export async function POST(request: NextRequest) {
  try {
    const formData = await request.formData()
    const file = formData.get('file') as File | null

    if (!file) {
      return NextResponse.json(
        { error: 'No file provided', code: 'NO_FILE' },
        { status: 400 }
      )
    }

    // Validate file size
    if (file.size > MAX_FILE_SIZE_BYTES) {
      return NextResponse.json(
        { error: `File size exceeds ${MAX_FILE_SIZE_MB}MB limit`, code: 'FILE_TOO_LARGE' },
        { status: 400 }
      )
    }

    // Validate Blob token
    const blobReadWriteToken = process.env.BLOB_READ_WRITE_TOKEN
    if (!blobReadWriteToken) {
      console.error('BLOB_READ_WRITE_TOKEN is not configured')
      return NextResponse.json(
        { error: 'Upload service not configured', code: 'CONFIG_ERROR' },
        { status: 500 }
      )
    }

    // Upload to Vercel Blob (default private, with access-mismatch fallback)
    const blob = await uploadWithCompatibleAccess(file.name, file, blobReadWriteToken)

    return NextResponse.json({ url: blob.url })
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error)
    console.error('Upload error:', message, error)
    return NextResponse.json(
      { error: `Upload failed: ${message}`, code: 'UPLOAD_ERROR' },
      { status: 500 }
    )
  }
}
