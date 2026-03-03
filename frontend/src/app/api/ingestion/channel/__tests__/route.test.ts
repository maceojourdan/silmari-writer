import { beforeEach, describe, expect, it, vi } from 'vitest';
import { NextRequest } from 'next/server';

vi.mock('@/server/filters/ChannelServiceAuthFilter', () => ({
  ChannelServiceAuthFilter: {
    authorize: vi.fn(),
  },
}));

vi.mock('@/server/request_handlers/ChannelIngestionHandler', () => ({
  ChannelIngestionHandler: {
    handle: vi.fn(),
  },
}));

vi.mock('@/server/data_access_objects/ChannelIngestionDAO', () => ({
  ChannelIngestionDAO: {
    findByProviderMessage: vi.fn(),
    findByUserAndCanonicalUrl: vi.fn(),
    createIngestionMessage: vi.fn(),
    updateContextReady: vi.fn(),
    updateContextFailed: vi.fn(),
    updateReplyStatus: vi.fn(),
  },
}));

vi.mock('@/server/services/ChannelIngestionPipelineAdapter', () => ({
  ChannelIngestionPipelineAdapter: {
    initializeFromUrl: vi.fn(),
  },
}));

vi.mock('@/server/services/ChannelReplySender', () => ({
  ChannelReplySender: {
    sendSuccess: vi.fn(),
  },
}));

import { POST } from '../route';
import { ChannelServiceAuthFilter } from '@/server/filters/ChannelServiceAuthFilter';
import { ChannelIngestionHandler } from '@/server/request_handlers/ChannelIngestionHandler';
import { ChannelIngestionDAO } from '@/server/data_access_objects/ChannelIngestionDAO';
import { ChannelIngestionPipelineAdapter } from '@/server/services/ChannelIngestionPipelineAdapter';
import { ChannelReplySender } from '@/server/services/ChannelReplySender';
import { ChannelIngestionErrors } from '@/server/error_definitions/ChannelIngestionErrors';

const mockAuth = vi.mocked(ChannelServiceAuthFilter);
const mockHandler = vi.mocked(ChannelIngestionHandler);
const mockDao = vi.mocked(ChannelIngestionDAO);
const mockAdapter = vi.mocked(ChannelIngestionPipelineAdapter);
const mockReplySender = vi.mocked(ChannelReplySender);

function createRequest(
  body: unknown,
  headers: Record<string, string> = {},
): NextRequest {
  return new NextRequest('http://localhost/api/ingestion/channel', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      ...headers,
    },
    body: JSON.stringify(body),
  });
}

describe('POST /api/ingestion/channel', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('returns 200 with deep link and reply metadata on success', async () => {
    mockAuth.authorize.mockReturnValue(undefined);
    mockHandler.handle.mockResolvedValue({
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      receivedAt: '2026-03-03T13:00:00.000Z',
      dedupe: {
        providerKey: 'twilio:SM-123',
        userUrlKey: 'user-1:https://example.greenhouse.io/job/123',
      },
    });

    mockDao.findByProviderMessage.mockResolvedValue(null);
    mockDao.findByUserAndCanonicalUrl.mockResolvedValue(null);
    mockDao.createIngestionMessage.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      rawBody: 'job https://example.greenhouse.io/job/123',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      status: 'received',
      replyStatus: 'pending',
      replyErrorCode: null,
      sessionId: null,
      receivedAt: '2026-03-03T13:00:00.000Z',
      createdAt: '2026-03-03T13:00:00.000Z',
      updatedAt: '2026-03-03T13:00:00.000Z',
    });
    mockAdapter.initializeFromUrl.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440001',
      state: 'initialized',
      contextSummary: 'Context extracted from example.greenhouse.io (sms).',
    });
    mockReplySender.sendSuccess.mockResolvedValue('sent');

    const response = await POST(
      createRequest(
        {
          channel: 'sms',
          sender: '+15555551212',
          body: 'job https://example.greenhouse.io/job/123',
          providerName: 'twilio',
          providerMessageId: 'SM-123',
        },
        { 'x-ingestion-api-key': 'test-ingestion-key' },
      ),
    );

    const data = await response.json();
    expect(response.status).toBe(200);
    expect(data.deepLink).toBe('/session/550e8400-e29b-41d4-a716-446655440001');
    expect(data.replyAttempted).toBe(true);
    expect(data.replyStatus).toBe('sent');
  });

  it('returns 401 when service auth fails', async () => {
    mockAuth.authorize.mockImplementation(() => {
      throw ChannelIngestionErrors.Unauthorized();
    });

    const response = await POST(
      createRequest({
        channel: 'sms',
        sender: '+15555551212',
        body: 'job https://example.greenhouse.io/job/123',
        providerName: 'twilio',
        providerMessageId: 'SM-123',
      }),
    );

    const data = await response.json();
    expect(response.status).toBe(401);
    expect(data.code).toBe('UNAUTHORIZED_CHANNEL');
  });

  it('returns 409 when duplicate provider message is detected', async () => {
    mockAuth.authorize.mockReturnValue(undefined);
    mockHandler.handle.mockResolvedValue({
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      receivedAt: '2026-03-03T13:00:00.000Z',
      dedupe: {
        providerKey: 'twilio:SM-123',
        userUrlKey: 'user-1:https://example.greenhouse.io/job/123',
      },
    });
    mockDao.findByProviderMessage.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      rawBody: 'job https://example.greenhouse.io/job/123',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      status: 'context_ready',
      replyStatus: 'sent',
      replyErrorCode: null,
      sessionId: '550e8400-e29b-41d4-a716-446655440001',
      receivedAt: '2026-03-03T13:00:00.000Z',
      createdAt: '2026-03-03T13:00:00.000Z',
      updatedAt: '2026-03-03T13:00:00.000Z',
    });

    const response = await POST(
      createRequest(
        {
          channel: 'sms',
          sender: '+15555551212',
          body: 'job https://example.greenhouse.io/job/123',
          providerName: 'twilio',
          providerMessageId: 'SM-123',
        },
        { 'x-ingestion-api-key': 'test-ingestion-key' },
      ),
    );

    const data = await response.json();
    expect(response.status).toBe(409);
    expect(data.code).toBe('DUPLICATE_INGESTION');
  });

  it('returns 409 when duplicate canonical URL for user is detected', async () => {
    mockAuth.authorize.mockReturnValue(undefined);
    mockHandler.handle.mockResolvedValue({
      channel: 'email',
      sender: 'test@example.com',
      userId: 'user-1',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      providerName: 'ses',
      providerMessageId: 'msg-456',
      receivedAt: '2026-03-03T13:00:00.000Z',
      dedupe: {
        providerKey: 'ses:msg-456',
        userUrlKey: 'user-1:https://example.greenhouse.io/job/123',
      },
    });
    mockDao.findByProviderMessage.mockResolvedValue(null);
    mockDao.findByUserAndCanonicalUrl.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      rawBody: 'job https://example.greenhouse.io/job/123',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      status: 'context_ready',
      replyStatus: 'sent',
      replyErrorCode: null,
      sessionId: '550e8400-e29b-41d4-a716-446655440001',
      receivedAt: '2026-03-03T13:00:00.000Z',
      createdAt: '2026-03-03T13:00:00.000Z',
      updatedAt: '2026-03-03T13:00:00.000Z',
    });

    const response = await POST(
      createRequest(
        {
          channel: 'email',
          sender: 'test@example.com',
          body: 'job https://example.greenhouse.io/job/123',
          providerName: 'ses',
          providerMessageId: 'msg-456',
        },
        { 'x-ingestion-api-key': 'test-ingestion-key' },
      ),
    );

    const data = await response.json();
    expect(response.status).toBe(409);
    expect(data.code).toBe('DUPLICATE_INGESTION');
  });

  it('returns 200 when reply sender fails non-blocking', async () => {
    mockAuth.authorize.mockReturnValue(undefined);
    mockHandler.handle.mockResolvedValue({
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      receivedAt: '2026-03-03T13:00:00.000Z',
      dedupe: {
        providerKey: 'twilio:SM-123',
        userUrlKey: 'user-1:https://example.greenhouse.io/job/123',
      },
    });

    mockDao.findByProviderMessage.mockResolvedValue(null);
    mockDao.findByUserAndCanonicalUrl.mockResolvedValue(null);
    mockDao.createIngestionMessage.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      rawBody: 'job https://example.greenhouse.io/job/123',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      status: 'received',
      replyStatus: 'pending',
      replyErrorCode: null,
      sessionId: null,
      receivedAt: '2026-03-03T13:00:00.000Z',
      createdAt: '2026-03-03T13:00:00.000Z',
      updatedAt: '2026-03-03T13:00:00.000Z',
    });
    mockAdapter.initializeFromUrl.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440001',
      state: 'initialized',
      contextSummary: 'Context extracted from example.greenhouse.io (sms).',
    });
    mockReplySender.sendSuccess.mockResolvedValue('failed_non_blocking');

    const response = await POST(
      createRequest(
        {
          channel: 'sms',
          sender: '+15555551212',
          body: 'job https://example.greenhouse.io/job/123',
          providerName: 'twilio',
          providerMessageId: 'SM-123',
        },
        { 'x-ingestion-api-key': 'test-ingestion-key' },
      ),
    );

    const data = await response.json();
    expect(response.status).toBe(200);
    expect(data.replyStatus).toBe('failed_non_blocking');
  });

  it('returns 409 SESSION_ALREADY_ACTIVE when adapter reports active-session conflict', async () => {
    mockAuth.authorize.mockReturnValue(undefined);
    mockHandler.handle.mockResolvedValue({
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      receivedAt: '2026-03-03T13:00:00.000Z',
      dedupe: {
        providerKey: 'twilio:SM-123',
        userUrlKey: 'user-1:https://example.greenhouse.io/job/123',
      },
    });
    mockDao.findByProviderMessage.mockResolvedValue(null);
    mockDao.findByUserAndCanonicalUrl.mockResolvedValue(null);
    mockDao.createIngestionMessage.mockResolvedValue({
      id: '550e8400-e29b-41d4-a716-446655440000',
      providerName: 'twilio',
      providerMessageId: 'SM-123',
      channel: 'sms',
      sender: '+15555551212',
      userId: 'user-1',
      rawBody: 'job https://example.greenhouse.io/job/123',
      canonicalUrl: 'https://example.greenhouse.io/job/123',
      sourceDomain: 'example.greenhouse.io',
      status: 'received',
      replyStatus: 'pending',
      replyErrorCode: null,
      sessionId: null,
      receivedAt: '2026-03-03T13:00:00.000Z',
      createdAt: '2026-03-03T13:00:00.000Z',
      updatedAt: '2026-03-03T13:00:00.000Z',
    });
    mockAdapter.initializeFromUrl.mockRejectedValue(
      ChannelIngestionErrors.SessionAlreadyActive(),
    );

    const response = await POST(
      createRequest(
        {
          channel: 'sms',
          sender: '+15555551212',
          body: 'job https://example.greenhouse.io/job/123',
          providerName: 'twilio',
          providerMessageId: 'SM-123',
        },
        { 'x-ingestion-api-key': 'test-ingestion-key' },
      ),
    );

    const data = await response.json();
    expect(response.status).toBe(409);
    expect(data.code).toBe('SESSION_ALREADY_ACTIVE');
    expect(mockDao.updateContextFailed).toHaveBeenCalledTimes(1);
  });
});
