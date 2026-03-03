import { describe, expect, it } from 'vitest';
import { ChannelServiceAuthFilter } from '../ChannelServiceAuthFilter';

describe('ChannelServiceAuthFilter.authorize', () => {
  it('accepts valid service key', () => {
    process.env.CHANNEL_INGESTION_API_KEY = 'abc123';
    expect(() =>
      ChannelServiceAuthFilter.authorize('abc123'),
    ).not.toThrow();
  });

  it('rejects missing key header', () => {
    process.env.CHANNEL_INGESTION_API_KEY = 'abc123';
    expect(() =>
      ChannelServiceAuthFilter.authorize(undefined),
    ).toThrow(/Invalid channel ingestion credentials/);
  });

  it('rejects incorrect key header', () => {
    process.env.CHANNEL_INGESTION_API_KEY = 'abc123';
    expect(() =>
      ChannelServiceAuthFilter.authorize('wrong'),
    ).toThrow(/Invalid channel ingestion credentials/);
  });
});

