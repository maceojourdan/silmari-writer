import { ChannelIngestionErrors } from '@/server/error_definitions/ChannelIngestionErrors';

export const ChannelServiceAuthFilter = {
  authorize(apiKeyHeader: string | null | undefined): void {
    const configuredKey =
      process.env.CHANNEL_INGESTION_API_KEY ||
      (process.env.NODE_ENV === 'test' ? 'test-ingestion-key' : '');

    if (!configuredKey) {
      throw ChannelIngestionErrors.ServiceMisconfigured(
        'Missing CHANNEL_INGESTION_API_KEY configuration',
      );
    }

    if (!apiKeyHeader || apiKeyHeader.trim() === '' || apiKeyHeader !== configuredKey) {
      throw ChannelIngestionErrors.Unauthorized();
    }
  },
} as const;

