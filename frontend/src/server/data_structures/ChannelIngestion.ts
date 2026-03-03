import { z } from 'zod';

export const ChannelTypeSchema = z.enum(['email', 'sms']);
export type ChannelType = z.infer<typeof ChannelTypeSchema>;

export const InboundChannelMessageSchema = z.object({
  channel: ChannelTypeSchema,
  sender: z.string().min(1),
  body: z.string().min(1),
  providerName: z.string().min(1),
  providerMessageId: z.string().min(1),
  receivedAt: z.string().optional(),
});

export type InboundChannelMessage = z.infer<typeof InboundChannelMessageSchema>;

export const NormalizedInboundMessageSchema = InboundChannelMessageSchema.extend({
  sender: z.string().min(1),
  receivedAt: z.string(),
});

export type NormalizedInboundMessage = z.infer<typeof NormalizedInboundMessageSchema>;

export const IngestionIdempotencyKeysSchema = z.object({
  providerKey: z.string().min(1),
  userUrlKey: z.string().min(1),
});

export type IngestionIdempotencyKeys = z.infer<typeof IngestionIdempotencyKeysSchema>;

export const ChannelIngestionHandleResultSchema = z.object({
  channel: ChannelTypeSchema,
  sender: z.string().min(1),
  userId: z.string().min(1),
  canonicalUrl: z.string().url(),
  sourceDomain: z.string().min(1),
  providerName: z.string().min(1),
  providerMessageId: z.string().min(1),
  receivedAt: z.string(),
  dedupe: IngestionIdempotencyKeysSchema,
});

export type ChannelIngestionHandleResult = z.infer<typeof ChannelIngestionHandleResultSchema>;

export const ChannelReplyStatusSchema = z.enum(['sent', 'failed_non_blocking']);
export type ChannelReplyStatus = z.infer<typeof ChannelReplyStatusSchema>;

export const ChannelIngestionResponseSchema = z.object({
  deepLink: z.string().min(1),
  channel: ChannelTypeSchema,
  replyAttempted: z.literal(true),
  replyStatus: ChannelReplyStatusSchema,
  contextSummary: z.string().min(1),
});

export type ChannelIngestionResponse = z.infer<typeof ChannelIngestionResponseSchema>;

export const ChannelIngestionErrorResponseSchema = z.object({
  code: z.string().min(1),
  message: z.string().min(1),
});

export type ChannelIngestionErrorResponse = z.infer<typeof ChannelIngestionErrorResponseSchema>;

export const IngestionMessageStatusSchema = z.enum([
  'received',
  'context_ready',
  'context_failed',
]);

export type IngestionMessageStatus = z.infer<typeof IngestionMessageStatusSchema>;

export const IngestionReplyStatusSchema = z.enum([
  'pending',
  'sent',
  'failed_non_blocking',
]);

export type IngestionReplyStatus = z.infer<typeof IngestionReplyStatusSchema>;

export const ChannelIngestionRecordSchema = z.object({
  id: z.string().uuid(),
  providerName: z.string().min(1),
  providerMessageId: z.string().min(1),
  channel: ChannelTypeSchema,
  sender: z.string().min(1),
  userId: z.string().min(1),
  rawBody: z.string().min(1),
  canonicalUrl: z.string().url(),
  sourceDomain: z.string().min(1),
  status: IngestionMessageStatusSchema,
  replyStatus: IngestionReplyStatusSchema,
  replyErrorCode: z.string().nullable().optional(),
  sessionId: z.string().uuid().nullable().optional(),
  receivedAt: z.string(),
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type ChannelIngestionRecord = z.infer<typeof ChannelIngestionRecordSchema>;

