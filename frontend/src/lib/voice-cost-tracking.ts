interface RealtimeModelPricing {
  audioInputPerMillion: number;
  audioOutputPerMillion: number;
  textInputPerMillion: number;
  textOutputPerMillion: number;
}

export const REALTIME_PRICING: Record<string, RealtimeModelPricing> = {
  'gpt-realtime-mini': {
    audioInputPerMillion: 10,
    audioOutputPerMillion: 20,
    textInputPerMillion: 0.6,
    textOutputPerMillion: 2.4,
  },
  'gpt-realtime': {
    audioInputPerMillion: 32,
    audioOutputPerMillion: 64,
    textInputPerMillion: 4,
    textOutputPerMillion: 16,
  },
};

// Directional token rates (GA API)
const TOKENS_PER_MINUTE_AUDIO_INPUT = 600;
const TOKENS_PER_MINUTE_AUDIO_OUTPUT = 1200;

interface CostEstimate {
  estimatedCost: number;
  model: string;
  breakdown: { label: string; amount: number }[];
}

export function estimateReadAloudCost(durationMinutes: number): CostEstimate {
  const model = 'gpt-realtime-mini';
  const pricing = REALTIME_PRICING[model];
  const outputTokens = durationMinutes * TOKENS_PER_MINUTE_AUDIO_OUTPUT;
  const outputCost = (outputTokens / 1_000_000) * pricing.audioOutputPerMillion;

  return {
    estimatedCost: outputCost,
    model,
    breakdown: [{ label: 'Audio output', amount: outputCost }],
  };
}

export function estimateVoiceEditCost(durationMinutes: number): CostEstimate {
  const model = 'gpt-realtime';
  const pricing = REALTIME_PRICING[model];
  const inputTokens = durationMinutes * TOKENS_PER_MINUTE_AUDIO_INPUT;
  const outputTokens = durationMinutes * TOKENS_PER_MINUTE_AUDIO_OUTPUT;
  const inputCost = (inputTokens / 1_000_000) * pricing.audioInputPerMillion;
  const outputCost = (outputTokens / 1_000_000) * pricing.audioOutputPerMillion;

  return {
    estimatedCost: inputCost + outputCost,
    model,
    breakdown: [
      { label: 'Audio input', amount: inputCost },
      { label: 'Audio output', amount: outputCost },
    ],
  };
}
