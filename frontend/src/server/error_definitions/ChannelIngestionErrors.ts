export type ChannelIngestionErrorCode =
  | 'UNAUTHORIZED_CHANNEL'
  | 'SERVICE_MISCONFIGURED'
  | 'INVALID_CHANNEL_PAYLOAD'
  | 'UNKNOWN_SENDER'
  | 'NO_VALID_URL'
  | 'INVALID_URL_DOMAIN'
  | 'DUPLICATE_INGESTION'
  | 'PIPELINE_INIT_FAILED'
  | 'INTERNAL_ERROR';

export class ChannelIngestionError extends Error {
  code: ChannelIngestionErrorCode;
  retryable: boolean;
  statusCode: number;

  constructor(
    message: string,
    code: ChannelIngestionErrorCode,
    statusCode: number,
    retryable = false,
  ) {
    super(message);
    this.name = 'ChannelIngestionError';
    this.code = code;
    this.statusCode = statusCode;
    this.retryable = retryable;
  }
}

export const ChannelIngestionErrors = {
  Unauthorized: (message = 'Invalid channel ingestion credentials') =>
    new ChannelIngestionError(message, 'UNAUTHORIZED_CHANNEL', 401, false),

  ServiceMisconfigured: (message = 'Channel ingestion service is not configured') =>
    new ChannelIngestionError(message, 'SERVICE_MISCONFIGURED', 500, false),

  InvalidPayload: (message = 'Invalid channel ingestion payload') =>
    new ChannelIngestionError(message, 'INVALID_CHANNEL_PAYLOAD', 400, false),

  UnknownSender: (message = 'Sender is not recognized') =>
    new ChannelIngestionError(message, 'UNKNOWN_SENDER', 404, false),

  NoValidUrl: (message = 'No valid URL found in inbound message') =>
    new ChannelIngestionError(message, 'NO_VALID_URL', 400, false),

  InvalidUrlDomain: (message = 'URL domain is not allowed for ingestion') =>
    new ChannelIngestionError(message, 'INVALID_URL_DOMAIN', 400, false),

  DuplicateIngestion: (message = 'Inbound message is a duplicate ingestion') =>
    new ChannelIngestionError(message, 'DUPLICATE_INGESTION', 409, false),

  PipelineInitFailed: (message = 'Failed to initialize session from inbound URL') =>
    new ChannelIngestionError(message, 'PIPELINE_INIT_FAILED', 500, true),

  Internal: (message = 'Unexpected channel ingestion failure') =>
    new ChannelIngestionError(message, 'INTERNAL_ERROR', 500, false),
} as const;

