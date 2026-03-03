import { beforeEach, describe, expect, it, vi } from 'vitest';
import {
  IngestionChannelRequestSchema,
  IngestionChannelResponseSchema,
  IngestionChannelErrorSchema,
  ingestChannelMessage,
  IngestionDuplicateError,
} from '../ingestionChannel';

vi.mock('@/logging/index', () => ({
  frontendLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
  },
}));

import { frontendLogger } from '@/logging/index';

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

const mockLogger = vi.mocked(frontendLogger);

describe('ingestChannelMessage API contract', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('validates request schema for inbound channel payload', () => {
    const parsed = IngestionChannelRequestSchema.safeParse({
      channel: 'sms',
      sender: '+15555551212',
      body: 'https://example.greenhouse.io/job/123',
      providerName: 'twilio',
      providerMessageId: 'SM-1',
    });
    expect(parsed.success).toBe(true);
  });

  it('validates success response schema', () => {
    const parsed = IngestionChannelResponseSchema.safeParse({
      deepLink: '/session/abc',
      channel: 'sms',
      replyAttempted: true,
      replyStatus: 'sent',
      contextSummary: 'Context extracted from example.greenhouse.io (sms).',
    });
    expect(parsed.success).toBe(true);
  });

  it('posts payload and returns parsed response', async () => {
    mockFetch.mockResolvedValue({
      ok: true,
      json: () => Promise.resolve({
        deepLink: '/session/abc',
        channel: 'sms',
        replyAttempted: true,
        replyStatus: 'sent',
        contextSummary: 'Context extracted from example.greenhouse.io (sms).',
      }),
    });

    const result = await ingestChannelMessage(
      {
        channel: 'sms',
        sender: '+15555551212',
        body: 'https://example.greenhouse.io/job/123',
        providerName: 'twilio',
        providerMessageId: 'SM-1',
      },
      'test-ingestion-key',
    );

    expect(result.deepLink).toBe('/session/abc');
    expect(mockFetch).toHaveBeenCalledWith(
      '/api/ingestion/channel',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          'x-ingestion-api-key': 'test-ingestion-key',
        }),
      }),
    );
  });

  it('throws IngestionDuplicateError for duplicate ingestion response', async () => {
    const errorPayload = {
      code: 'DUPLICATE_INGESTION',
      message: 'Inbound message is a duplicate ingestion',
    };
    expect(IngestionChannelErrorSchema.safeParse(errorPayload).success).toBe(true);

    mockFetch.mockResolvedValue({
      ok: false,
      status: 409,
      json: () => Promise.resolve(errorPayload),
    });

    await expect(
      ingestChannelMessage(
        {
          channel: 'sms',
          sender: '+15555551212',
          body: 'https://example.greenhouse.io/job/123',
          providerName: 'twilio',
          providerMessageId: 'SM-1',
        },
        'test-ingestion-key',
      ),
    ).rejects.toBeInstanceOf(IngestionDuplicateError);
  });

  it('logs and throws on malformed success response', async () => {
    mockFetch.mockResolvedValue({
      ok: true,
      json: () => Promise.resolve({ invalid: true }),
    });

    await expect(
      ingestChannelMessage(
        {
          channel: 'sms',
          sender: '+15555551212',
          body: 'https://example.greenhouse.io/job/123',
          providerName: 'twilio',
          providerMessageId: 'SM-1',
        },
        'test-ingestion-key',
      ),
    ).rejects.toThrow('Invalid response');

    expect(mockLogger.error).toHaveBeenCalled();
  });
});

