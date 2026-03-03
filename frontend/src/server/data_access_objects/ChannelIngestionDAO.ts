import { supabase } from '@/lib/supabase';
import type {
  ChannelIngestionRecord,
  IngestionMessageStatus,
  IngestionReplyStatus,
} from '@/server/data_structures/ChannelIngestion';
import { ChannelIngestionErrors } from '@/server/error_definitions/ChannelIngestionErrors';

interface CreateIngestionMessageInput {
  providerName: string;
  providerMessageId: string;
  channel: 'email' | 'sms';
  sender: string;
  userId: string;
  rawBody: string;
  canonicalUrl: string;
  sourceDomain: string;
  status: IngestionMessageStatus;
  replyStatus?: IngestionReplyStatus;
  receivedAt: string;
}

interface MappedUser {
  id: string;
}

function mapIngestionRecord(data: Record<string, unknown>): ChannelIngestionRecord {
  return {
    id: data.id as string,
    providerName: data.provider_name as string,
    providerMessageId: data.provider_message_id as string,
    channel: data.channel as 'email' | 'sms',
    sender: data.sender as string,
    userId: data.user_id as string,
    rawBody: data.raw_body as string,
    canonicalUrl: data.canonical_url as string,
    sourceDomain: data.source_domain as string,
    status: data.status as IngestionMessageStatus,
    replyStatus: data.reply_status as IngestionReplyStatus,
    replyErrorCode: (data.reply_error_code as string | null | undefined) ?? null,
    sessionId: (data.session_id as string | null | undefined) ?? null,
    receivedAt: data.received_at as string,
    createdAt: data.created_at as string,
    updatedAt: data.updated_at as string,
  };
}

export const ChannelIngestionDAO = {
  async findUserByPhone(phoneNumber: string): Promise<MappedUser | null> {
    const { data, error } = await supabase
      .from('users')
      .select('id')
      .eq('phone_number', phoneNumber)
      .maybeSingle();

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed sender lookup by phone: ${error.message}`,
      );
    }

    if (!data) {
      return null;
    }

    return { id: data.id as string };
  },

  async findUserByEmail(email: string): Promise<MappedUser | null> {
    const { data, error } = await supabase
      .from('users')
      .select('id')
      .ilike('email', email)
      .maybeSingle();

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed sender lookup by email: ${error.message}`,
      );
    }

    if (!data) {
      return null;
    }

    return { id: data.id as string };
  },

  async findByProviderMessage(
    providerName: string,
    providerMessageId: string,
  ): Promise<ChannelIngestionRecord | null> {
    const { data, error } = await supabase
      .from('ingestion_messages')
      .select('*')
      .eq('provider_name', providerName)
      .eq('provider_message_id', providerMessageId)
      .maybeSingle();

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed provider dedupe lookup: ${error.message}`,
      );
    }

    return data ? mapIngestionRecord(data as Record<string, unknown>) : null;
  },

  async findByUserAndCanonicalUrl(
    userId: string,
    canonicalUrl: string,
  ): Promise<ChannelIngestionRecord | null> {
    const { data, error } = await supabase
      .from('ingestion_messages')
      .select('*')
      .eq('user_id', userId)
      .eq('canonical_url', canonicalUrl)
      .maybeSingle();

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed URL dedupe lookup: ${error.message}`,
      );
    }

    return data ? mapIngestionRecord(data as Record<string, unknown>) : null;
  },

  async createIngestionMessage(
    input: CreateIngestionMessageInput,
  ): Promise<ChannelIngestionRecord> {
    const { data, error } = await supabase
      .from('ingestion_messages')
      .insert({
        provider_name: input.providerName,
        provider_message_id: input.providerMessageId,
        channel: input.channel,
        sender: input.sender,
        user_id: input.userId,
        raw_body: input.rawBody,
        canonical_url: input.canonicalUrl,
        source_domain: input.sourceDomain,
        status: input.status,
        reply_status: input.replyStatus ?? 'pending',
        received_at: input.receivedAt,
      })
      .select('*')
      .single();

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed to create ingestion message: ${error.message}`,
      );
    }

    return mapIngestionRecord(data as Record<string, unknown>);
  },

  async updateContextReady(messageId: string, sessionId: string): Promise<void> {
    const { error } = await supabase
      .from('ingestion_messages')
      .update({
        status: 'context_ready',
        session_id: sessionId,
        updated_at: new Date().toISOString(),
      })
      .eq('id', messageId);

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed to update context readiness: ${error.message}`,
      );
    }
  },

  async updateContextFailed(messageId: string): Promise<void> {
    const { error } = await supabase
      .from('ingestion_messages')
      .update({
        status: 'context_failed',
        updated_at: new Date().toISOString(),
      })
      .eq('id', messageId);

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed to update context failure state: ${error.message}`,
      );
    }
  },

  async updateReplyStatus(
    messageId: string,
    replyStatus: IngestionReplyStatus,
    replyErrorCode?: string,
  ): Promise<void> {
    const { error } = await supabase
      .from('ingestion_messages')
      .update({
        reply_status: replyStatus,
        reply_error_code: replyErrorCode ?? null,
        updated_at: new Date().toISOString(),
      })
      .eq('id', messageId);

    if (error) {
      throw ChannelIngestionErrors.Internal(
        `Failed to update reply status: ${error.message}`,
      );
    }
  },
} as const;

