// Voice mode constants
export const VOICE_MODES = {
  READ_ALOUD: 'read_aloud',
  VOICE_EDIT: 'voice_edit',
} as const;

export type VoiceMode = (typeof VOICE_MODES)[keyof typeof VOICE_MODES];

// Model mapping per voice mode
export const MODEL_MAP: Record<VoiceMode, string> = {
  read_aloud: 'gpt-4o-realtime-preview',
  voice_edit: 'gpt-4o-realtime-preview',
} as const;

// Session configuration
export const SESSION_LIMIT_MINUTES = 60;
export const DEFAULT_VOICE = 'alloy';

// Session states
export const VOICE_SESSION_STATES = {
  IDLE: 'idle',
  CONNECTING: 'connecting',
  CONNECTED: 'connected',
  RECONNECTING: 'reconnecting',
  ERROR: 'error',
  CLOSED: 'closed',
} as const;

export type VoiceSessionState = (typeof VOICE_SESSION_STATES)[keyof typeof VOICE_SESSION_STATES];

// Edit tracking types
export interface EditEntry {
  messageId: string;
  editedContent: string;
  editSummary?: string;
  timestamp: number;
}

export interface EditHistory {
  projectId: string;
  sessionId: string;
  originalSnapshots: Record<string, string>; // messageId -> original content
  edits: EditEntry[];
}

// Factory functions
export function createEditEntry(params: Omit<EditEntry, 'timestamp'>): EditEntry {
  return { ...params, timestamp: Date.now() };
}

export function createEditHistory(params: Pick<EditHistory, 'projectId' | 'sessionId'>): EditHistory {
  return { ...params, originalSnapshots: {}, edits: [] };
}

// Voice session token response
export interface VoiceSessionTokenResponse {
  token: string;
  model: string;
  sessionLimitMinutes: number;
}

// Voice edit instruction (Realtime API → Main LLM)
export interface VoiceEditInstruction {
  intent: string;         // What the user wants to change
  targetMessageId?: string; // Specific message, or null for model to decide
  fullInstruction: string;  // Complete edit instruction text
}
