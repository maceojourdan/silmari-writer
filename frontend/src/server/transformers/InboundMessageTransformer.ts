import type { NormalizedInboundMessage } from '@/server/data_structures/ChannelIngestion';
import { InboundChannelMessageSchema } from '@/server/data_structures/ChannelIngestion';
import { ChannelIngestionErrors } from '@/server/error_definitions/ChannelIngestionErrors';

function normalizePhone(input: string): string {
  return input.replace(/[^\d+]/g, '');
}

function normalizeEmail(input: string): string {
  return input.trim().toLowerCase();
}

export const InboundMessageTransformer = {
  parse(payload: unknown): NormalizedInboundMessage {
    const parsed = InboundChannelMessageSchema.safeParse(payload);
    if (!parsed.success) {
      const details = parsed.error.issues
        .map((issue) => `${issue.path.join('.')}: ${issue.message}`)
        .join('; ');
      throw ChannelIngestionErrors.InvalidPayload(
        `Invalid inbound channel payload: ${details}`,
      );
    }

    const raw = parsed.data;
    const normalizedSender = raw.channel === 'sms'
      ? normalizePhone(raw.sender)
      : normalizeEmail(raw.sender);

    if (!normalizedSender) {
      throw ChannelIngestionErrors.InvalidPayload(
        'Inbound sender must be present after normalization',
      );
    }

    return {
      channel: raw.channel,
      sender: normalizedSender,
      body: raw.body,
      providerName: raw.providerName.trim().toLowerCase(),
      providerMessageId: raw.providerMessageId.trim(),
      receivedAt: raw.receivedAt ?? new Date().toISOString(),
    };
  },
} as const;

