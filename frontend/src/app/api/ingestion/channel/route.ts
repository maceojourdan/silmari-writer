import { NextRequest, NextResponse } from 'next/server';
import { ChannelServiceAuthFilter } from '@/server/filters/ChannelServiceAuthFilter';
import { ChannelIngestionHandler } from '@/server/request_handlers/ChannelIngestionHandler';
import { ChannelIngestionDAO } from '@/server/data_access_objects/ChannelIngestionDAO';
import { ChannelIngestionPipelineAdapter } from '@/server/services/ChannelIngestionPipelineAdapter';
import { ChannelReplySender } from '@/server/services/ChannelReplySender';
import {
  ChannelIngestionError,
  ChannelIngestionErrors,
} from '@/server/error_definitions/ChannelIngestionErrors';
import { ChannelIngestionResponseSchema } from '@/server/data_structures/ChannelIngestion';
import { logger } from '@/server/logging/logger';

export async function POST(request: NextRequest) {
  let messageId: string | undefined;

  try {
    ChannelServiceAuthFilter.authorize(
      request.headers.get('x-ingestion-api-key'),
    );

    let payload: unknown;
    try {
      payload = await request.json();
    } catch {
      throw ChannelIngestionErrors.InvalidPayload(
        'Request body is not valid JSON',
      );
    }

    const result = await ChannelIngestionHandler.handle(payload);

    const duplicateByProvider = await ChannelIngestionDAO.findByProviderMessage(
      result.providerName,
      result.providerMessageId,
    );
    if (duplicateByProvider) {
      throw ChannelIngestionErrors.DuplicateIngestion(
        `Duplicate provider message: ${result.providerName}:${result.providerMessageId}`,
      );
    }

    const duplicateByUrl = await ChannelIngestionDAO.findByUserAndCanonicalUrl(
      result.userId,
      result.canonicalUrl,
    );
    if (duplicateByUrl) {
      throw ChannelIngestionErrors.DuplicateIngestion(
        `Duplicate URL for user: ${result.userId}:${result.canonicalUrl}`,
      );
    }

    const persisted = await ChannelIngestionDAO.createIngestionMessage({
      providerName: result.providerName,
      providerMessageId: result.providerMessageId,
      channel: result.channel,
      sender: result.sender,
      userId: result.userId,
      rawBody: (payload as { body?: string }).body ?? '',
      canonicalUrl: result.canonicalUrl,
      sourceDomain: result.sourceDomain,
      status: 'received',
      replyStatus: 'pending',
      receivedAt: result.receivedAt,
    });

    messageId = persisted.id;

    const initialized = await ChannelIngestionPipelineAdapter.initializeFromUrl({
      userId: result.userId,
      sourceUrl: result.canonicalUrl,
      channel: result.channel,
    });

    await ChannelIngestionDAO.updateContextReady(messageId, initialized.id);

    const deepLink = `/session/${initialized.id}`;
    const replyStatus = await ChannelReplySender.sendSuccess({
      channel: result.channel,
      recipient: result.sender,
      deepLink,
      contextSummary: initialized.contextSummary,
    });

    await ChannelIngestionDAO.updateReplyStatus(
      messageId,
      replyStatus === 'sent' ? 'sent' : 'failed_non_blocking',
      replyStatus === 'sent' ? undefined : 'CHANNEL_REPLY_FAILURE',
    );

    const responsePayload = {
      deepLink,
      channel: result.channel,
      replyAttempted: true as const,
      replyStatus,
      contextSummary: initialized.contextSummary,
    };

    const responseValidation = ChannelIngestionResponseSchema.safeParse(responsePayload);
    if (!responseValidation.success) {
      throw ChannelIngestionErrors.Internal('Failed to construct valid ingestion response');
    }

    return NextResponse.json(responseValidation.data, { status: 200 });
  } catch (error) {
    if (messageId && error instanceof ChannelIngestionError) {
      try {
        await ChannelIngestionDAO.updateContextFailed(messageId);
      } catch (innerError) {
        logger.error('Failed to mark ingestion message as context_failed', innerError, {
          path: '340-ingest-url-via-email-or-sms-channel',
          resource: 'api-e5f6',
          messageId,
        });
      }
    }

    if (error instanceof ChannelIngestionError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    logger.error('Unexpected channel ingestion route error', error, {
      path: '340-ingest-url-via-email-or-sms-channel',
      resource: 'api-e5f6',
    });
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'Unexpected channel ingestion route error' },
      { status: 500 },
    );
  }
}

