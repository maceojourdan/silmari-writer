import { z } from 'zod';
import { frontendLogger } from '@/logging/index';

export const IngestionChannelRequestSchema = z.object({
  channel: z.enum(['email', 'sms']),
  sender: z.string().min(1),
  body: z.string().min(1),
  providerName: z.string().min(1),
  providerMessageId: z.string().min(1),
  receivedAt: z.string().optional(),
});

export type IngestionChannelRequest = z.infer<typeof IngestionChannelRequestSchema>;

export const IngestionChannelResponseSchema = z.object({
  deepLink: z.string().min(1),
  channel: z.enum(['email', 'sms']),
  replyAttempted: z.literal(true),
  replyStatus: z.enum(['sent', 'failed_non_blocking']),
  contextSummary: z.string().min(1),
});

export type IngestionChannelResponse = z.infer<typeof IngestionChannelResponseSchema>;

export const IngestionChannelErrorSchema = z.object({
  code: z.string().min(1),
  message: z.string().min(1),
});

export class IngestionDuplicateError extends Error {
  code = 'DUPLICATE_INGESTION';
  statusCode = 409;

  constructor(message: string) {
    super(message);
    this.name = 'IngestionDuplicateError';
  }
}

export async function ingestChannelMessage(
  payload: IngestionChannelRequest,
  apiKey: string,
): Promise<IngestionChannelResponse> {
  const parsedPayload = IngestionChannelRequestSchema.parse(payload);

  try {
    const response = await fetch('/api/ingestion/channel', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'x-ingestion-api-key': apiKey,
      },
      body: JSON.stringify(parsedPayload),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      const parsedError = IngestionChannelErrorSchema.safeParse(errorBody);

      if (
        response.status === 409 &&
        parsedError.success &&
        parsedError.data.code === 'DUPLICATE_INGESTION'
      ) {
        throw new IngestionDuplicateError(parsedError.data.message);
      }

      throw new Error(
        parsedError.success
          ? parsedError.data.message
          : `Ingestion request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = IngestionChannelResponseSchema.safeParse(data);
    if (!parsed.success) {
      throw new Error(
        `Invalid response from ingestion/channel: ${parsed.error.issues.map((issue) => issue.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Channel ingestion API contract call failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'ingestChannelMessage', module: 'api_contracts' },
    );
    throw error;
  }
}

