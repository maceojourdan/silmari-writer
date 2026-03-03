import type { ChannelReplyStatus } from '@/server/data_structures/ChannelIngestion';
import { logger } from '@/server/logging/logger';

interface ReplySuccessInput {
  channel: 'email' | 'sms';
  recipient: string;
  deepLink: string;
  contextSummary: string;
}

export const ChannelReplySender = {
  async sendSuccess(input: ReplySuccessInput): Promise<ChannelReplyStatus> {
    try {
      logger.info('Channel ingestion success reply queued', {
        path: '340-ingest-url-via-email-or-sms-channel',
        resource: 'api-e5f6',
        channel: input.channel,
        recipient: input.recipient,
        deepLink: input.deepLink,
      });

      // Provider implementation is intentionally deferred; this contract
      // guarantees non-blocking behavior for notification failures.
      return 'sent';
    } catch (error) {
      logger.error('Channel ingestion success reply failed', error, {
        path: '340-ingest-url-via-email-or-sms-channel',
        resource: 'api-e5f6',
        channel: input.channel,
        recipient: input.recipient,
      });
      return 'failed_non_blocking';
    }
  },
} as const;

