export type WorkflowStage =
  | 'ORIENT'
  | 'RECALL_REVIEW'
  | 'DRAFT'
  | 'FINALIZE'
  | 'FINALIZED'
  | 'UNKNOWN';

const STAGE_BY_STATE: Record<string, WorkflowStage> = {
  INIT: 'ORIENT',
  ORIENT: 'ORIENT',

  IN_PROGRESS: 'RECALL_REVIEW',
  RECALL: 'RECALL_REVIEW',
  COMPLETE: 'RECALL_REVIEW',
  VERIFY: 'RECALL_REVIEW',
  REVIEW: 'RECALL_REVIEW',

  DRAFT: 'DRAFT',
  DRAFT_ENABLED: 'DRAFT',
  ACTIVE: 'DRAFT',

  FINALIZE: 'FINALIZE',
  FINALIZED: 'FINALIZED',
};

export function mapSessionStateToStage(state: string): WorkflowStage {
  return STAGE_BY_STATE[state] ?? 'UNKNOWN';
}

export function isTerminalStage(stage: WorkflowStage): boolean {
  return stage === 'FINALIZED';
}

