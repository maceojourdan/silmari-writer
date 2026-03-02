import { describe, expect, it } from 'vitest';
import { mapSessionStateToStage } from '../stageMapper';

describe('stageMapper', () => {
  it('maps orient states to ORIENT stage', () => {
    expect(mapSessionStateToStage('INIT')).toBe('ORIENT');
    expect(mapSessionStateToStage('ORIENT')).toBe('ORIENT');
  });

  it('maps recall and review-adjacent states to RECALL_REVIEW stage', () => {
    expect(mapSessionStateToStage('IN_PROGRESS')).toBe('RECALL_REVIEW');
    expect(mapSessionStateToStage('RECALL')).toBe('RECALL_REVIEW');
    expect(mapSessionStateToStage('VERIFY')).toBe('RECALL_REVIEW');
    expect(mapSessionStateToStage('REVIEW')).toBe('RECALL_REVIEW');
  });

  it('maps draft/finalize states and falls back for unknown values', () => {
    expect(mapSessionStateToStage('DRAFT')).toBe('DRAFT');
    expect(mapSessionStateToStage('FINALIZE')).toBe('FINALIZE');
    expect(mapSessionStateToStage('FINALIZED')).toBe('FINALIZED');
    expect(mapSessionStateToStage('UNSUPPORTED_STATE')).toBe('UNKNOWN');
  });
});

