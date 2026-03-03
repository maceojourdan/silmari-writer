import { URL } from 'node:url';
import { ChannelIngestionDAO } from '@/server/data_access_objects/ChannelIngestionDAO';
import { ChannelIngestionErrors } from '@/server/error_definitions/ChannelIngestionErrors';
import type {
  IngestionIdempotencyKeys,
  NormalizedInboundMessage,
} from '@/server/data_structures/ChannelIngestion';

const URL_REGEX = /\bhttps?:\/\/[^\s<>"')]+/gi;

const KNOWN_JOB_DOMAIN_HINTS = [
  'linkedin.com',
  'greenhouse.io',
  'lever.co',
  'workday.com',
  'ashbyhq.com',
  'indeed.com',
  'ziprecruiter.com',
  'myworkdayjobs.com',
  'jobs.',
] as const;

function canonicalizeUrl(input: string): string {
  const parsed = new URL(input);
  parsed.hash = '';
  parsed.hostname = parsed.hostname.toLowerCase();
  parsed.pathname = parsed.pathname.replace(/\/+$/, '') || '/';
  parsed.searchParams.sort();
  return parsed.toString();
}

function isLikelyJobDomain(hostname: string): boolean {
  const host = hostname.toLowerCase();
  return KNOWN_JOB_DOMAIN_HINTS.some((hint) => host.includes(hint));
}

export const ChannelIngestionService = {
  async resolveSender(
    normalized: NormalizedInboundMessage,
  ): Promise<{ id: string }> {
    const user = normalized.channel === 'sms'
      ? await ChannelIngestionDAO.findUserByPhone(normalized.sender)
      : await ChannelIngestionDAO.findUserByEmail(normalized.sender);

    if (!user) {
      throw ChannelIngestionErrors.UnknownSender(
        `No user found for sender ${normalized.sender}`,
      );
    }

    return user;
  },

  extractCanonicalUrl(body: string, _userId: string): string {
    const matches = body.match(URL_REGEX);
    if (!matches || matches.length === 0) {
      throw ChannelIngestionErrors.NoValidUrl();
    }

    const firstUrl = matches[0];
    let canonicalUrl: string;
    try {
      canonicalUrl = canonicalizeUrl(firstUrl);
    } catch {
      throw ChannelIngestionErrors.NoValidUrl(
        `Unable to parse URL from message body: ${firstUrl}`,
      );
    }

    const hostname = new URL(canonicalUrl).hostname;
    if (!isLikelyJobDomain(hostname)) {
      throw ChannelIngestionErrors.InvalidUrlDomain(
        `Unsupported domain for ingestion: ${hostname}`,
      );
    }

    return canonicalUrl;
  },

  extractSourceDomain(canonicalUrl: string): string {
    return new URL(canonicalUrl).hostname.toLowerCase();
  },

  buildIdempotencyKeys(input: {
    providerName: string;
    providerMessageId: string;
    userId: string;
    canonicalUrl: string;
  }): IngestionIdempotencyKeys {
    return {
      providerKey: `${input.providerName}:${input.providerMessageId}`,
      userUrlKey: `${input.userId}:${input.canonicalUrl}`,
    };
  },
} as const;

