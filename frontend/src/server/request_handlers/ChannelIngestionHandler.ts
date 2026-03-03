import { InboundMessageTransformer } from '@/server/transformers/InboundMessageTransformer';
import { ChannelIngestionService } from '@/server/services/ChannelIngestionService';
import type { ChannelIngestionHandleResult } from '@/server/data_structures/ChannelIngestion';

export const ChannelIngestionHandler = {
  async handle(payload: unknown): Promise<ChannelIngestionHandleResult> {
    const normalized = InboundMessageTransformer.parse(payload);
    const user = await ChannelIngestionService.resolveSender(normalized);
    const canonicalUrl = ChannelIngestionService.extractCanonicalUrl(normalized.body, user.id);
    const sourceDomain = ChannelIngestionService.extractSourceDomain(canonicalUrl);
    const dedupe = ChannelIngestionService.buildIdempotencyKeys({
      providerName: normalized.providerName,
      providerMessageId: normalized.providerMessageId,
      userId: user.id,
      canonicalUrl,
    });

    return {
      channel: normalized.channel,
      sender: normalized.sender,
      userId: user.id,
      canonicalUrl,
      sourceDomain,
      providerName: normalized.providerName,
      providerMessageId: normalized.providerMessageId,
      receivedAt: normalized.receivedAt,
      dedupe,
    };
  },
} as const;

