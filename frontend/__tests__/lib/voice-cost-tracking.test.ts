import { describe, it, expect } from 'vitest';

describe('Voice Cost Tracking', () => {
  it('should have pricing for gpt-realtime-mini model', async () => {
    const { REALTIME_PRICING } = await import('@/lib/voice-cost-tracking');
    expect(REALTIME_PRICING['gpt-realtime-mini']).toBeDefined();
    expect(REALTIME_PRICING['gpt-realtime-mini'].audioInputPerMillion).toBe(10);
    expect(REALTIME_PRICING['gpt-realtime-mini'].audioOutputPerMillion).toBe(20);
  });

  it('should have pricing for gpt-realtime model', async () => {
    const { REALTIME_PRICING } = await import('@/lib/voice-cost-tracking');
    expect(REALTIME_PRICING['gpt-realtime']).toBeDefined();
    expect(REALTIME_PRICING['gpt-realtime'].audioInputPerMillion).toBe(32);
    expect(REALTIME_PRICING['gpt-realtime'].audioOutputPerMillion).toBe(64);
  });

  it('should estimate Read Aloud session cost for given duration', async () => {
    const { estimateReadAloudCost } = await import('@/lib/voice-cost-tracking');
    const estimate = estimateReadAloudCost(60);
    expect(estimate.estimatedCost).toBeGreaterThan(0);
    expect(estimate.model).toBe('gpt-realtime-mini');
  });

  it('should estimate Voice Edit session cost for given duration', async () => {
    const { estimateVoiceEditCost } = await import('@/lib/voice-cost-tracking');
    const estimate = estimateVoiceEditCost(60);
    expect(estimate.estimatedCost).toBeGreaterThan(0);
    expect(estimate.model).toBe('gpt-realtime');
    const readAloudEstimate = (await import('@/lib/voice-cost-tracking')).estimateReadAloudCost(60);
    expect(estimate.estimatedCost).toBeGreaterThan(readAloudEstimate.estimatedCost);
  });
});
