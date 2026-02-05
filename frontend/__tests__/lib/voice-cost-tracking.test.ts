import { describe, it, expect } from 'vitest';

describe('Voice Cost Tracking', () => {
  it('should have pricing for gpt-4o-realtime-preview model', async () => {
    const { REALTIME_PRICING } = await import('@/lib/voice-cost-tracking');
    expect(REALTIME_PRICING['gpt-4o-realtime-preview']).toBeDefined();
    expect(REALTIME_PRICING['gpt-4o-realtime-preview'].audioInputPerMillion).toBe(40);
    expect(REALTIME_PRICING['gpt-4o-realtime-preview'].audioOutputPerMillion).toBe(80);
  });

  it('should estimate Read Aloud session cost for given duration', async () => {
    const { estimateReadAloudCost } = await import('@/lib/voice-cost-tracking');
    const estimate = estimateReadAloudCost(60);
    expect(estimate.estimatedCost).toBeGreaterThan(0);
    expect(estimate.model).toBe('gpt-4o-realtime-preview');
  });

  it('should estimate Voice Edit session cost for given duration', async () => {
    const { estimateVoiceEditCost } = await import('@/lib/voice-cost-tracking');
    const estimate = estimateVoiceEditCost(60);
    expect(estimate.estimatedCost).toBeGreaterThan(0);
    expect(estimate.model).toBe('gpt-4o-realtime-preview');
  });
});
