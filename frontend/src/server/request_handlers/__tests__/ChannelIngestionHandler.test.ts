import { beforeEach, describe, expect, it, vi } from 'vitest';

vi.mock('@/server/transformers/InboundMessageTransformer', () => ({
  InboundMessageTransformer: {
    parse: vi.fn(),
  },
}));

vi.mock('@/server/services/ChannelIngestionService', () => ({
  ChannelIngestionService: {
    resolveSender: vi.fn(),
    extractCanonicalUrl: vi.fn(),
    extractSourceDomain: vi.fn(),
    buildIdempotencyKeys: vi.fn(),
  },
}));

import { ChannelIngestionHandler } from '../ChannelIngestionHandler';
import { InboundMessageTransformer } from '@/server/transformers/InboundMessageTransformer';
import { ChannelIngestionService } from '@/server/services/ChannelIngestionService';
import { ChannelIngestionErrors } from '@/server/error_definitions/ChannelIngestionErrors';

const mockTransformer = vi.mocked(InboundMessageTransformer);
const mockService = vi.mocked(ChannelIngestionService);

describe('ChannelIngestionHandler.handle', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('normalizes payload, resolves sender, extracts canonical URL, and returns idempotency keys', async () => {
    mockTransformer.parse.mockReturnValue({
      channel: 'sms',
      sender: '+15555551212',
      body: 'job https://example.greenhouse.io/job/123',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      receivedAt: '2026-03-03T13:00:00.000Z',
    });
    mockService.resolveSender.mockResolvedValue({ id: 'user-1' });
    mockService.extractCanonicalUrl.mockReturnValue('https://example.greenhouse.io/job/123');
    mockService.extractSourceDomain.mockReturnValue('example.greenhouse.io');
    mockService.buildIdempotencyKeys.mockReturnValue({
      providerKey: 'twilio:SM-123',
      userUrlKey: 'user-1:https://example.greenhouse.io/job/123',
    });

    const result = await ChannelIngestionHandler.handle({
      channel: 'sms',
      sender: '(555) 555-1212',
      body: 'job https://example.greenhouse.io/job/123',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
    });

    expect(result).toMatchObject({
      channel: 'sms',
      userId: 'user-1',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
    });
    expect(result.dedupe.providerKey).toBe('twilio:SM-123');
    expect(mockService.resolveSender).toHaveBeenCalledTimes(1);
    expect(mockService.extractCanonicalUrl).toHaveBeenCalledWith(
      'job https://example.greenhouse.io/job/123',
      'user-1',
    );
  });

  it('rethrows service errors (unknown sender)', async () => {
    mockTransformer.parse.mockReturnValue({
      channel: 'email',
      sender: 'unknown@example.com',
      body: 'https://example.greenhouse.io/job/123',
      providerName: 'ses',
      providerMessageId: 'msg-1',
      receivedAt: '2026-03-03T13:00:00.000Z',
    });
    mockService.resolveSender.mockRejectedValue(
      ChannelIngestionErrors.UnknownSender('unknown sender'),
    );

    await expect(ChannelIngestionHandler.handle({})).rejects.toMatchObject({
      code: 'UNKNOWN_SENDER',
    });
  });
});

