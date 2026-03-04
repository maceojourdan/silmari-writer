import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import {
  StartSessionAlreadyActiveError,
  StartSessionFromUrlErrorSchema,
} from '@/api_contracts/startSessionFromUrl';

const MAX_FILE_SIZE_BYTES = 10 * 1024 * 1024;
const RESUME_EXTENSIONS = new Set(['docx', 'doc', 'pdf', 'txt', 'md']);
const SCREENSHOT_EXTENSIONS = new Set(['png', 'jpg', 'jpeg', 'webp']);

function extensionFromFilename(filename: string): string {
  const parts = filename.toLowerCase().split('.');
  return parts.length > 1 ? parts.at(-1) ?? '' : '';
}

function isAllowedUploadExtension(filename: string): boolean {
  const ext = extensionFromFilename(filename);
  return RESUME_EXTENSIONS.has(ext) || SCREENSHOT_EXTENSIONS.has(ext);
}

export const StartSessionFromUploadRequestSchema = z.object({
  files: z.array(
    z.object({
      filename: z.string().min(1),
      url: z.string().url(),
      mimeType: z.string().min(1).optional(),
    }),
  ).min(1),
});

const RecallQuestionSchema = z.object({
  id: z.string().min(1),
  text: z.string().min(1),
  category: z.string().min(1),
  position: z.number().int().nonnegative(),
});

const QuestionProgressSchema = z.object({
  currentIndex: z.number().int().nonnegative(),
  total: z.number().int().nonnegative(),
  completed: z.array(z.string()),
  activeQuestionId: z.string().min(1).nullable(),
});

export const StartSessionFromUploadResponseSchema = z.object({
  sessionId: z.string().uuid(),
  state: z.literal('initialized'),
  inputMode: z.literal('file_upload'),
  resumeId: z.string().uuid().nullable().optional(),
  questions: z.array(RecallQuestionSchema).min(1),
  questionProgress: QuestionProgressSchema,
});

export type StartSessionFromUploadResponse = z.infer<typeof StartSessionFromUploadResponseSchema>;

async function uploadFile(file: File): Promise<{ filename: string; url: string; mimeType: string }> {
  const formData = new FormData();
  formData.append('file', file);

  const response = await fetch('/api/upload', {
    method: 'POST',
    body: formData,
  });

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(errorBody.error || `Upload failed with status ${response.status}`);
  }

  const data = await response.json();
  if (!data || typeof data.url !== 'string') {
    throw new Error('Upload response did not include a valid URL');
  }

  return {
    filename: file.name,
    url: data.url,
    mimeType: file.type,
  };
}

function validateFiles(files: File[]): void {
  if (files.length === 0) {
    throw new Error('Upload at least one resume or screenshot file to continue.');
  }

  for (const file of files) {
    if (!isAllowedUploadExtension(file.name)) {
      throw new Error(`Unsupported file type: ${file.name}`);
    }
    if (file.size > MAX_FILE_SIZE_BYTES) {
      throw new Error(`File too large: ${file.name}`);
    }
  }
}

export async function startSessionFromUpload(
  authToken: string,
  files: File[],
): Promise<StartSessionFromUploadResponse> {
  validateFiles(files);

  try {
    const uploadedFiles = await Promise.all(files.map((file) => uploadFile(file)));
    const payload = StartSessionFromUploadRequestSchema.parse({ files: uploadedFiles });

    const response = await fetch('/api/session/start-from-upload', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${authToken}`,
      },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      const parsedError = StartSessionFromUrlErrorSchema.safeParse(errorBody);

      if (
        response.status === 409
        && parsedError.success
        && parsedError.data.code === 'SESSION_ALREADY_ACTIVE'
      ) {
        throw new StartSessionAlreadyActiveError(parsedError.data.message);
      }

      throw new Error(
        parsedError.success
          ? parsedError.data.message
          : `File-upload session initialization failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = StartSessionFromUploadResponseSchema.safeParse(data);
    if (!parsed.success) {
      throw new Error(
        `Invalid response from session/start-from-upload: ${parsed.error.issues.map((issue) => issue.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'File-upload session initialization request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'startSessionFromUpload', module: 'api_contracts' },
    );
    throw error;
  }
}
