# OpenAI Realtime Voice Chat Integration — TDD Implementation Plan

## Review Status

> **Reviewed**: 2026-02-05 — **Major revision applied** from REVIEW file.
> All critical API issues resolved: GA endpoints, correct model names, 60-min session limit, directional token rates.
> Warning-level improvements incorporated: error contracts, reconnection, TTSQueue fix, retry logic, atomic undo guard, mutual exclusion.

## Overview

Add voice chat capabilities to silmari-writer powered by the OpenAI Realtime API via WebRTC. Two features:

1. **Read Aloud (TTS)** — Session-level toggle that automatically reads all new agent responses aloud using `gpt-realtime-mini` (alloy voice). Messages queue (FIFO) when multiple arrive quickly.
2. **Voice-Driven Editing (Three-Layer)** — Document-level voice editing using a three-model architecture: Realtime API (`gpt-realtime`) as voice interface, Main Text LLM (`gpt-4o-mini`) for actual edits, and TTS (`gpt-realtime-mini`) for read-back. Edits span multiple assistant messages. Session-scoped undo.

### Three-Layer Voice Editing Architecture

```
User speaks edit instruction
  → Realtime API (gpt-realtime) captures voice, extracts intent
  → Sends structured edit instruction to Main Text LLM (gpt-4o-mini)
  → Main Text LLM processes edit against document (all assistant messages)
  → Edited text returned
  → Edit applied to store (replaceMessage) + pushed to edit history
  → TTS (gpt-realtime-mini) reads back the edited result
  → User hears result, can give more instructions via Realtime API
```

The Realtime API is a **voice interface layer**, NOT the editor. The Main Text LLM does actual text editing. This separation allows:
- Better edit quality (Main LLM has full document context in text)
- Lower Realtime API costs (voice I/O only, not text reasoning)
- Reuse of existing `/api/generate` patterns for the editing LLM

> **API Note**: This plan targets the OpenAI Realtime **GA** API (not the beta API deprecated Feb 27, 2026). Key differences from beta: `/v1/realtime/client_secrets` for tokens, `/v1/realtime/calls` with `FormData` for SDP exchange, model names `gpt-realtime-mini` / `gpt-realtime`, 60-minute session limit.

## Current State Analysis

### What Exists
- `AudioRecorder.tsx` — MediaRecorder-based recording → Whisper pipeline (remains for file uploads)
- `transcription.ts` / `transcribe/route.ts` — Whisper STT pipeline (unchanged)
- `store.ts` — Zustand with `replaceMessage()`, `buttonStates`, persistence. No voice state
- `EditMessageModal.tsx` — Text-based editing modal (partially implemented)
- `ButtonRibbon.tsx` — Message action buttons with blocking/non-blocking operation pattern
- `SSEClient` — Streaming patterns (event handling, reconnection, state management)
- `useButtonAnalytics` — Only custom hook in `/hooks/`
- `env.ts` — Zod env validation (`OPENAI_API_KEY`, `NODE_ENV`)
- `cost-tracking.ts` — Token-based pricing with thresholds

### Key Discoveries
- `store.ts:111-127` — `replaceMessage()` action exists and is the primary edit integration point
- `types.ts:49-56` — `Message` already has `isVoiceTranscription?: boolean`
- `types.ts:66` — `BlockingOperationType = 'regenerate' | 'sendToAPI' | 'edit'` (edit type exists)
- `messageActions.ts:19-67` — `regenerateMessage()` shows the pattern for calling `/api/generate` with context
- `page.tsx:41-72` — `handleSendMessage` shows message add + generate flow. New agent messages land via `addMessage()` at line 60
- `ConversationView.tsx:12-40` — Simple message list, no header/toolbar area currently
- `page.tsx:142` — `<ConversationView>` is rendered directly, no wrapper with controls
- No WebRTC, WebSocket, or session management hooks exist
- No header/toolbar component — conversation area goes directly from sidebar to messages
- Vitest + React Testing Library + Playwright. Mock patterns for MediaRecorder, navigator, fetch exist

## Desired End State

### Observable Behaviors
1. **Read Aloud toggle** visible in the conversation area. When ON, new agent responses automatically play as speech. Queue-based (FIFO).
2. **Voice Edit button** on message ribbon (or conversation-level). Activates three-layer voice editing with persistent Realtime API session.
3. **Session timer** (60 minutes) visible during active voice sessions. Session auto-closes on expiry.
4. **Undo** button available during voice edit sessions. Reverts last edit. Session-scoped.
5. **Cost tracking** extended for Realtime API pricing models.

### Verification via Tests
- Unit tests for all new hooks, utilities, store extensions, API routes
- Component tests for all new UI elements
- Integration tests for the three-layer editing flow
- All tests follow Red-Green-Refactor TDD cycles

## What We're NOT Doing
- No Web Speech API (`speechSynthesis`) fallback — Realtime API only
- No changes to existing Whisper transcription pipeline
- No pipeline integration (deferred — depends on stepwise pipeline implementation)
- No voice selection UI (hardcoded to `alloy`)
- No mobile-specific optimizations
- No offline support
- No automatic WebRTC reconnection (detect `disconnected`/`failed` states and notify user, but no auto-reconnect). The `RECONNECTING` session state is defined for future use but not wired in v1.

## Testing Strategy
- **Framework**: Vitest + React Testing Library (existing setup)
- **Test Location**: `frontend/__tests__/` matching existing directory structure
- **Mocking**: WebRTC APIs (`RTCPeerConnection`, `RTCDataChannel`), `navigator.mediaDevices`, `fetch`, `Audio` element, `setTimeout`/`setInterval`
- **Store Testing**: Direct Zustand store testing (existing pattern in `store.test.ts`)
- **API Route Testing**: Next.js route handler testing (existing pattern in `generate.test.ts`)
- **Integration**: Vitest-based integration tests (existing pattern in `ButtonInteractions.test.tsx`)

---

## Behavior 1: Voice Session Types and Constants

### Test Specification
**Given**: The voice chat feature is being developed
**When**: Types and constants are defined
**Then**: All voice-related types, constants, and enums are available for import

**Edge Cases**: Type correctness for all voice modes, session states, edit history entries

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/voice-types.test.ts`
```typescript
import { describe, it, expect } from 'vitest';

describe('Voice Types and Constants', () => {
  it('should export VoiceMode enum with read_aloud and voice_edit', async () => {
    const { VOICE_MODES } = await import('@/lib/voice-types');
    expect(VOICE_MODES.READ_ALOUD).toBe('read_aloud');
    expect(VOICE_MODES.VOICE_EDIT).toBe('voice_edit');
  });

  it('should export model mapping for each voice mode', async () => {
    const { MODEL_MAP } = await import('@/lib/voice-types');
    expect(MODEL_MAP.read_aloud).toBe('gpt-realtime-mini');
    expect(MODEL_MAP.voice_edit).toBe('gpt-realtime');
  });

  it('should export SESSION_LIMIT_MINUTES as 60', async () => {
    const { SESSION_LIMIT_MINUTES } = await import('@/lib/voice-types');
    expect(SESSION_LIMIT_MINUTES).toBe(60);
  });

  it('should export DEFAULT_VOICE as alloy', async () => {
    const { DEFAULT_VOICE } = await import('@/lib/voice-types');
    expect(DEFAULT_VOICE).toBe('alloy');
  });

  it('should export VoiceSessionState type with correct values', async () => {
    const { VOICE_SESSION_STATES } = await import('@/lib/voice-types');
    expect(VOICE_SESSION_STATES).toEqual({
      IDLE: 'idle',
      CONNECTING: 'connecting',
      CONNECTED: 'connected',
      RECONNECTING: 'reconnecting',
      ERROR: 'error',
      CLOSED: 'closed',
    });
  });

  it('should export EditEntry interface shape via factory function', async () => {
    const { createEditEntry } = await import('@/lib/voice-types');
    const entry = createEditEntry({
      messageId: 'msg-1',
      editedContent: 'new content',
      editSummary: 'Changed first paragraph',
    });
    expect(entry).toMatchObject({
      messageId: 'msg-1',
      editedContent: 'new content',
      editSummary: 'Changed first paragraph',
    });
    expect(entry.timestamp).toBeGreaterThan(0);
  });

  it('should export EditHistory interface shape via factory function', async () => {
    const { createEditHistory } = await import('@/lib/voice-types');
    const history = createEditHistory({
      projectId: 'proj-1',
      sessionId: 'session-1',
    });
    expect(history).toMatchObject({
      projectId: 'proj-1',
      sessionId: 'session-1',
      originalSnapshots: {},
      edits: [],
    });
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/lib/voice-types.ts`
```typescript
// Voice mode constants
export const VOICE_MODES = {
  READ_ALOUD: 'read_aloud',
  VOICE_EDIT: 'voice_edit',
} as const;

export type VoiceMode = (typeof VOICE_MODES)[keyof typeof VOICE_MODES];

// Model mapping per voice mode
export const MODEL_MAP: Record<VoiceMode, string> = {
  read_aloud: 'gpt-realtime-mini',
  voice_edit: 'gpt-realtime',
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
```

#### 🔵 Refactor
No refactoring needed — this is a foundational types file.

### Success Criteria
**Automated:**
- [x] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/lib/voice-types.test.ts`
- [x] Test passes (Green): `cd frontend && npx vitest run __tests__/lib/voice-types.test.ts`
- [x] All existing tests still pass: `cd frontend && npx vitest run`
- [x] TypeScript compiles: `cd frontend && npx tsc --noEmit`

---

## Behavior 2: Ephemeral Token API Route

### Test Specification
**Given**: A Next.js API route at `/api/voice/session`
**When**: A POST request is made with `{ mode: 'read_aloud' | 'voice_edit' }`
**Then**: Returns `{ token, model, sessionLimitMinutes }` using an ephemeral token from OpenAI's GA endpoint (`/v1/realtime/client_secrets`)

**Edge Cases**:
- Missing `OPENAI_API_KEY` → 500 error
- Invalid mode → defaults to `read_aloud`
- OpenAI API failure → 502 error with message
- `voice_edit` mode includes `instructions` and `tools` in session config

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/api/voice-session.test.ts`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

// Mock fetch for OpenAI API calls
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// Mock environment
const originalEnv = process.env;

function createRequest(body: Record<string, unknown>): NextRequest {
  return new NextRequest('http://localhost:3000/api/voice/session', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('POST /api/voice/session', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    process.env = { ...originalEnv, OPENAI_API_KEY: 'test-key' };
  });

  it('should return ephemeral token for read_aloud mode', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ value: 'ek_test_token_123', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud' }));
    const data = await response.json();

    expect(response.status).toBe(200);
    expect(data.token).toBe('ek_test_token_123');
    expect(data.model).toBe('gpt-realtime-mini');
    expect(data.sessionLimitMinutes).toBe(60);
  });

  it('should use gpt-realtime model for voice_edit mode', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ value: 'ek_edit_token_456', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({
      mode: 'voice_edit',
      instructions: 'Edit the document',
      tools: [{ type: 'function', name: 'send_edit_instruction' }],
    }));
    const data = await response.json();

    expect(data.model).toBe('gpt-realtime');

    // Verify OpenAI was called with correct GA endpoint and wrapped body
    expect(mockFetch).toHaveBeenCalledWith(
      'https://api.openai.com/v1/realtime/client_secrets',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          'Authorization': 'Bearer test-key',
        }),
        body: expect.stringContaining('gpt-realtime'),
      }),
    );
  });

  it('should include turn_detection for voice_edit mode', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ value: 'ek_token', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    await POST(createRequest({ mode: 'voice_edit' }));

    const fetchBody = JSON.parse(mockFetch.mock.calls[0][1].body);
    expect(fetchBody.session.turn_detection).toEqual({ type: 'server_vad' });
  });

  it('should NOT include turn_detection for read_aloud mode', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ value: 'ek_token', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    await POST(createRequest({ mode: 'read_aloud' }));

    const fetchBody = JSON.parse(mockFetch.mock.calls[0][1].body);
    expect(fetchBody.session.turn_detection).toBeNull();
  });

  it('should default to read_aloud when mode is invalid', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: async () => ({ value: 'ek_token', expires_at: 1234567890, session: {} }),
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'invalid_mode' }));
    const data = await response.json();

    expect(data.model).toBe('gpt-realtime-mini');
  });

  it('should return 500 when OPENAI_API_KEY is missing', async () => {
    delete process.env.OPENAI_API_KEY;

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud' }));

    expect(response.status).toBe(500);
    const data = await response.json();
    expect(data.error).toContain('configured');
  });

  it('should return 502 when OpenAI API fails', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: false,
      status: 500,
      text: async () => 'Internal Server Error',
    });

    const { POST } = await import('@/app/api/voice/session/route');
    const response = await POST(createRequest({ mode: 'read_aloud' }));

    expect(response.status).toBe(502);
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/app/api/voice/session/route.ts`
```typescript
import { NextRequest, NextResponse } from 'next/server';
import { MODEL_MAP, SESSION_LIMIT_MINUTES, DEFAULT_VOICE } from '@/lib/voice-types';
import type { VoiceMode } from '@/lib/voice-types';

export async function POST(request: NextRequest) {
  const apiKey = process.env.OPENAI_API_KEY;
  if (!apiKey) {
    return NextResponse.json(
      { error: 'Voice chat not configured' },
      { status: 500 },
    );
  }

  const body = await request.json();
  const mode: VoiceMode = body.mode in MODEL_MAP ? body.mode : 'read_aloud';
  const model = MODEL_MAP[mode];

  const sessionConfig: Record<string, unknown> = {
    model,
    voice: DEFAULT_VOICE,
    turn_detection: mode === 'voice_edit' ? { type: 'server_vad' } : null,
  };

  if (body.instructions) {
    sessionConfig.instructions = body.instructions;
  }
  if (body.tools) {
    sessionConfig.tools = body.tools;
  }

  // GA endpoint — wraps config in { session: ... }
  const response = await fetch('https://api.openai.com/v1/realtime/client_secrets', {
    method: 'POST',
    headers: {
      'Authorization': `Bearer ${apiKey}`,
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({ session: sessionConfig }),
  });

  if (!response.ok) {
    return NextResponse.json(
      { error: 'Failed to create voice session' },
      { status: 502 },
    );
  }

  // GA response: { value: "ek_...", expires_at: <unix_ts>, session: {...} }
  const data = await response.json();
  return NextResponse.json({
    token: data.value,
    model,
    sessionLimitMinutes: SESSION_LIMIT_MINUTES,
  });
}
```

#### 🔵 Refactor
- Extract error response helpers if pattern is repeated in later routes

### Success Criteria
**Automated:**
- [x] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/api/voice-session.test.ts`
- [x] Test passes (Green): `cd frontend && npx vitest run __tests__/api/voice-session.test.ts`
- [x] All existing tests still pass: `cd frontend && npx vitest run`
- [x] TypeScript compiles: `cd frontend && npx tsc --noEmit`

---

## Behavior 3: WebRTC Voice Session Connection

### Test Specification
**Given**: An ephemeral token from the API route
**When**: `createVoiceSession()` is called with token, model, and options
**Then**: A WebRTC `RTCPeerConnection` is established with OpenAI's Realtime API, audio output plays, and a data channel for events is available

**Edge Cases**:
- Microphone not needed for `read_aloud` (no `addTrack`)
- Microphone required for `voice_edit` (calls `getUserMedia` + `addTrack`)
- SDP offer/answer exchange succeeds (GA endpoint: `/v1/realtime/calls` with FormData)
- Session timeout fires at 60 minutes
- Cleanup releases all resources (tracks, peer connection, audio element, timer)
- `getUserMedia` rejection throws `VoiceSessionError` with `code: 'MICROPHONE_DENIED'`
- SDP exchange failure throws `VoiceSessionError` with `code: 'SDP_EXCHANGE_FAILED'`

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/voice-session.test.ts`
```typescript
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

// Mock RTCPeerConnection
const mockAddTrack = vi.fn();
const mockCreateDataChannel = vi.fn();
const mockCreateOffer = vi.fn();
const mockSetLocalDescription = vi.fn();
const mockSetRemoteDescription = vi.fn();
const mockClose = vi.fn();
let mockOnTrack: ((event: { streams: MediaStream[] }) => void) | null = null;

const MockRTCPeerConnection = vi.fn().mockImplementation(() => ({
  addTrack: mockAddTrack,
  createDataChannel: mockCreateDataChannel.mockReturnValue({
    onopen: null,
    onclose: null,
    onmessage: null,
    send: vi.fn(),
    readyState: 'open',
  }),
  createOffer: mockCreateOffer.mockResolvedValue({ sdp: 'mock-offer-sdp' }),
  setLocalDescription: mockSetLocalDescription.mockResolvedValue(undefined),
  setRemoteDescription: mockSetRemoteDescription.mockResolvedValue(undefined),
  close: mockClose,
  set ontrack(handler: (event: { streams: MediaStream[] }) => void) {
    mockOnTrack = handler;
  },
  get ontrack() { return mockOnTrack; },
  localDescription: { sdp: 'mock-offer-sdp' },
}));

vi.stubGlobal('RTCPeerConnection', MockRTCPeerConnection);

// Mock fetch for SDP exchange
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// Mock navigator.mediaDevices
const mockGetUserMedia = vi.fn();
vi.stubGlobal('navigator', {
  mediaDevices: { getUserMedia: mockGetUserMedia },
});

// Mock Audio element
const mockAudioEl = { autoplay: false, srcObject: null };
vi.spyOn(document, 'createElement').mockImplementation((tag: string) => {
  if (tag === 'audio') return mockAudioEl as unknown as HTMLElement;
  return document.createElement(tag);
});

describe('createVoiceSession', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.useFakeTimers();
    mockFetch.mockResolvedValue({
      ok: true,
      text: async () => 'mock-answer-sdp',
    });
    mockGetUserMedia.mockResolvedValue({
      getAudioTracks: () => [{ stop: vi.fn(), kind: 'audio' }],
      getTracks: () => [{ stop: vi.fn() }],
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('should create RTCPeerConnection and data channel', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    const session = await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime-mini',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(MockRTCPeerConnection).toHaveBeenCalled();
    expect(mockCreateDataChannel).toHaveBeenCalledWith('oai-events');
    expect(session.pc).toBeDefined();
    expect(session.dc).toBeDefined();
  });

  it('should set audio element autoplay and attach to ontrack', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime-mini',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(mockAudioEl.autoplay).toBe(true);
    // Simulate track event
    const mockStream = new MediaStream();
    mockOnTrack?.({ streams: [mockStream] });
    expect(mockAudioEl.srcObject).toBe(mockStream);
  });

  it('should NOT request microphone for read_aloud (needsMicrophone: false)', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime-mini',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(mockGetUserMedia).not.toHaveBeenCalled();
    expect(mockAddTrack).not.toHaveBeenCalled();
  });

  it('should request microphone for voice_edit (needsMicrophone: true)', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime',
      sessionLimitMinutes: 60,
      needsMicrophone: true,
    });

    expect(mockGetUserMedia).toHaveBeenCalledWith({ audio: true });
    expect(mockAddTrack).toHaveBeenCalled();
  });

  it('should perform SDP offer/answer exchange with OpenAI GA endpoint using FormData', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime-mini',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(mockCreateOffer).toHaveBeenCalled();
    expect(mockSetLocalDescription).toHaveBeenCalled();
    expect(mockFetch).toHaveBeenCalledWith(
      'https://api.openai.com/v1/realtime/calls',
      expect.objectContaining({
        method: 'POST',
        headers: expect.objectContaining({
          'Authorization': 'Bearer ek_test',
        }),
        body: expect.any(FormData),
      }),
    );
    expect(mockSetRemoteDescription).toHaveBeenCalledWith({
      type: 'answer',
      sdp: 'mock-answer-sdp',
    });
  });

  it('should set up session timeout that closes connection', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    const session = await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime-mini',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    });

    expect(session.sessionTimeout).toBeDefined();

    // Advance timer to 60 minutes
    vi.advanceTimersByTime(60 * 60 * 1000);

    expect(mockClose).toHaveBeenCalled();
  });

  it('should throw VoiceSessionError when getUserMedia is rejected', async () => {
    mockGetUserMedia.mockRejectedValueOnce(new DOMException('Permission denied'));

    const { createVoiceSession, VoiceSessionError } = await import('@/lib/voice-session');
    await expect(createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime',
      sessionLimitMinutes: 60,
      needsMicrophone: true,
    })).rejects.toThrow(VoiceSessionError);
  });

  it('should throw VoiceSessionError when SDP exchange fails', async () => {
    mockFetch.mockResolvedValueOnce({ ok: false, status: 500, text: async () => 'Error' });

    const { createVoiceSession, VoiceSessionError } = await import('@/lib/voice-session');
    await expect(createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime-mini',
      sessionLimitMinutes: 60,
      needsMicrophone: false,
    })).rejects.toThrow(VoiceSessionError);
  });

  it('should return cleanup function that releases all resources', async () => {
    const { createVoiceSession } = await import('@/lib/voice-session');
    const session = await createVoiceSession({
      token: 'ek_test',
      model: 'gpt-realtime',
      sessionLimitMinutes: 60,
      needsMicrophone: true,
    });

    session.close();

    expect(mockClose).toHaveBeenCalled();
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/lib/voice-session.ts`
```typescript
export class VoiceSessionError extends Error {
  code: string;
  retryable: boolean;

  constructor(message: string, code: string, retryable = false) {
    super(message);
    this.name = 'VoiceSessionError';
    this.code = code;
    this.retryable = retryable;
  }
}

export interface VoiceSessionOptions {
  token: string;
  model: string;
  sessionLimitMinutes: number;
  needsMicrophone: boolean;
}

export interface VoiceSession {
  pc: RTCPeerConnection;
  dc: RTCDataChannel;
  audioEl: HTMLAudioElement;
  stream: MediaStream | null;
  sessionTimeout: ReturnType<typeof setTimeout>;
  close: () => void;
}

export async function createVoiceSession(options: VoiceSessionOptions): Promise<VoiceSession> {
  const { token, model, sessionLimitMinutes, needsMicrophone } = options;
  const pc = new RTCPeerConnection();

  // Audio output
  const audioEl = document.createElement('audio');
  audioEl.autoplay = true;
  pc.ontrack = (event) => {
    audioEl.srcObject = event.streams[0];
  };

  // Microphone input (only for voice editing)
  let stream: MediaStream | null = null;
  if (needsMicrophone) {
    try {
      stream = await navigator.mediaDevices.getUserMedia({ audio: true });
      pc.addTrack(stream.getAudioTracks()[0], stream);
    } catch (err) {
      pc.close();
      throw new VoiceSessionError(
        `Microphone access denied: ${(err as Error).message}`,
        'MICROPHONE_DENIED',
        false,
      );
    }
  }

  // Data channel for API events
  const dc = pc.createDataChannel('oai-events');

  // SDP exchange — GA endpoint uses FormData
  const offer = await pc.createOffer();
  await pc.setLocalDescription(offer);

  const formData = new FormData();
  formData.append('sdp', new Blob([pc.localDescription!.sdp!], { type: 'application/sdp' }));
  formData.append('session', new Blob([JSON.stringify({ type: 'realtime', model })], { type: 'application/json' }));

  const sdpResponse = await fetch('https://api.openai.com/v1/realtime/calls', {
    method: 'POST',
    headers: { 'Authorization': `Bearer ${token}` },
    body: formData,
  });

  if (!sdpResponse.ok) {
    pc.close();
    stream?.getTracks().forEach((t) => t.stop());
    throw new VoiceSessionError(
      'SDP exchange failed',
      'SDP_EXCHANGE_FAILED',
      true,
    );
  }

  const answerSdp = await sdpResponse.text();
  await pc.setRemoteDescription({ type: 'answer', sdp: answerSdp });

  // Session timer
  const sessionTimeout = setTimeout(() => {
    close();
  }, sessionLimitMinutes * 60 * 1000);

  function close() {
    clearTimeout(sessionTimeout);
    pc.close();
    stream?.getTracks().forEach((t) => t.stop());
  }

  return { pc, dc, audioEl, stream, sessionTimeout, close };
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/lib/voice-session.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/lib/voice-session.test.ts`
- [ ] All existing tests still pass: `cd frontend && npx vitest run`

---

## Behavior 4: Voice Store Extensions

### Test Specification
**Given**: The Zustand conversation store
**When**: Voice-related state and actions are added
**Then**: `readAloudEnabled`, `voiceSessionState`, `editHistory`, and related actions are available

**Key state additions:**
- `readAloudEnabled: boolean` — Toggle for Read Aloud
- `voiceSessionState: VoiceSessionState` — Current session state
- `editHistory: EditHistory | null` — Session-scoped edit tracking
- Actions: `setReadAloud()`, `setVoiceSessionState()`, `pushEdit()`, `popEdit()`, `clearEditHistory()`, `snapshotOriginal()`

**Edge Cases**:
- `editHistory` is NOT persisted to localStorage (session-scoped)
- `readAloudEnabled` is NOT persisted (reset to false on page reload — avoids auto-connect issue on rehydration)
- `voiceSessionState` is NOT persisted (session-scoped)
- `popEdit()` returns previous content from stack, or original if stack empty
- `snapshotOriginal()` only snapshots if message not yet in `originalSnapshots`

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/voice-store.test.ts`
```typescript
import { describe, it, expect, beforeEach } from 'vitest';
import { useConversationStore } from '@/lib/store';

describe('Voice Store Extensions', () => {
  beforeEach(() => {
    const { setState } = useConversationStore;
    setState({
      projects: [],
      activeProjectId: null,
      messages: {},
      buttonStates: {},
      readAloudEnabled: false,
      voiceSessionState: 'idle',
      editHistory: null,
    });
  });

  describe('readAloudEnabled', () => {
    it('should default to false', () => {
      const state = useConversationStore.getState();
      expect(state.readAloudEnabled).toBe(false);
    });

    it('should be togglable via setReadAloud', () => {
      const { setReadAloud } = useConversationStore.getState();
      setReadAloud(true);
      expect(useConversationStore.getState().readAloudEnabled).toBe(true);
      setReadAloud(false);
      expect(useConversationStore.getState().readAloudEnabled).toBe(false);
    });
  });

  describe('voiceSessionState', () => {
    it('should default to idle', () => {
      expect(useConversationStore.getState().voiceSessionState).toBe('idle');
    });

    it('should update via setVoiceSessionState', () => {
      const { setVoiceSessionState } = useConversationStore.getState();
      setVoiceSessionState('connecting');
      expect(useConversationStore.getState().voiceSessionState).toBe('connecting');
      setVoiceSessionState('connected');
      expect(useConversationStore.getState().voiceSessionState).toBe('connected');
    });
  });

  describe('editHistory', () => {
    it('should default to null', () => {
      expect(useConversationStore.getState().editHistory).toBeNull();
    });

    it('should initialize via initEditHistory', () => {
      const { initEditHistory } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');
      const history = useConversationStore.getState().editHistory;
      expect(history).toMatchObject({
        projectId: 'proj-1',
        sessionId: 'session-1',
        originalSnapshots: {},
        edits: [],
      });
    });

    it('should snapshot original content only once per message', () => {
      const { initEditHistory, snapshotOriginal } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');

      snapshotOriginal('msg-1', 'Original text');
      snapshotOriginal('msg-1', 'Should not overwrite');

      const history = useConversationStore.getState().editHistory!;
      expect(history.originalSnapshots['msg-1']).toBe('Original text');
    });

    it('should push edits to the edit stack', () => {
      const { initEditHistory, pushEdit } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');

      pushEdit({
        messageId: 'msg-1',
        editedContent: 'Edited version 1',
        editSummary: 'Changed intro',
      });

      const history = useConversationStore.getState().editHistory!;
      expect(history.edits).toHaveLength(1);
      expect(history.edits[0].editedContent).toBe('Edited version 1');
    });

    it('should pop the last edit and return previous content', () => {
      const { initEditHistory, snapshotOriginal, pushEdit, popEdit } =
        useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');
      snapshotOriginal('msg-1', 'Original');

      pushEdit({ messageId: 'msg-1', editedContent: 'Edit 1' });
      pushEdit({ messageId: 'msg-1', editedContent: 'Edit 2' });

      const result = popEdit();
      expect(result).toEqual({
        messageId: 'msg-1',
        previousContent: 'Edit 1',
      });

      const result2 = popEdit();
      expect(result2).toEqual({
        messageId: 'msg-1',
        previousContent: 'Original',
      });
    });

    it('should return null from popEdit when no edits remain', () => {
      const { initEditHistory, popEdit } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');

      expect(popEdit()).toBeNull();
    });

    it('should clear edit history', () => {
      const { initEditHistory, pushEdit, clearEditHistory } =
        useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');
      pushEdit({ messageId: 'msg-1', editedContent: 'Edit 1' });

      clearEditHistory();
      expect(useConversationStore.getState().editHistory).toBeNull();
    });
  });
});
```

#### 🟢 Green: Minimal Implementation

Extend `store.ts` with the new voice state and actions. The implementation adds to the existing `ConversationState` interface and Zustand store.

**Changes to**: `frontend/src/lib/store.ts`
- Add `readAloudEnabled`, `voiceSessionState`, `editHistory` to state
- Add `setReadAloud()`, `setVoiceSessionState()`, `initEditHistory()`, `snapshotOriginal()`, `pushEdit()`, `popEdit()`, `clearEditHistory()` actions
- Exclude `editHistory`, `voiceSessionState`, and `readAloudEnabled` from persistence (add to `partialize`)

#### 🔵 Refactor
- Consider extracting voice state into a separate Zustand slice if the store becomes too large
- The `popEdit()` logic for finding previous content by walking the stack backwards is a candidate for extraction into a helper

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/lib/voice-store.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/lib/voice-store.test.ts`
- [ ] All existing store tests still pass: `cd frontend && npx vitest run __tests__/lib/store.test.ts`
- [ ] Existing persistence tests still pass (editHistory not in localStorage)

---

## Behavior 5: useRealtimeSession Hook

### Test Specification
**Given**: A React component that needs to manage a WebRTC voice session
**When**: `useRealtimeSession()` is called with a voice mode
**Then**: The hook manages session lifecycle (connect, disconnect, auto-close on timer), exposes session state, data channel event handling, and TTS queue

**Key behaviors:**
- `connect(mode)` — Fetches token from `/api/voice/session`, creates WebRTC session
- `disconnect()` — Closes session, releases resources
- `sendText(text)` — Sends text for TTS via data channel (Read Aloud)
- `sessionState` — Current state (idle, connecting, connected, error, closed)
- `timeRemaining` — Countdown in seconds
- Auto-closes on 60-minute timer
- `onDataChannelMessage` callback for event handling

**Edge Cases**:
- Double-connect prevention (ignore if already connecting/connected)
- Cleanup on unmount
- Error state on connection failure
- Debounce/cooldown on `connect()` to prevent rapid session creation
- Detect `pc.onconnectionstatechange` for `'disconnected'`/`'failed'` → set error state and notify user

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/hooks/useRealtimeSession.test.ts`
```typescript
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { renderHook, act, waitFor } from '@testing-library/react';

// Mock voice-session module
const mockCreateVoiceSession = vi.fn();
const mockClose = vi.fn();
vi.mock('@/lib/voice-session', () => ({
  createVoiceSession: (...args: unknown[]) => mockCreateVoiceSession(...args),
}));

// Mock fetch for token endpoint
const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

// Mock store
const mockSetVoiceSessionState = vi.fn();
vi.mock('@/lib/store', () => ({
  useConversationStore: Object.assign(
    vi.fn(() => ({
      voiceSessionState: 'idle',
      setVoiceSessionState: mockSetVoiceSessionState,
    })),
    { getState: vi.fn(() => ({ setVoiceSessionState: mockSetVoiceSessionState })) },
  ),
}));

describe('useRealtimeSession', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    vi.useFakeTimers();

    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        token: 'ek_test',
        model: 'gpt-realtime-mini',
        sessionLimitMinutes: 60,
      }),
    });

    const mockDc = {
      onopen: null as (() => void) | null,
      onclose: null as (() => void) | null,
      onmessage: null as ((event: { data: string }) => void) | null,
      send: vi.fn(),
      readyState: 'open',
    };

    mockCreateVoiceSession.mockResolvedValue({
      pc: { close: vi.fn() },
      dc: mockDc,
      audioEl: { autoplay: true, srcObject: null },
      stream: null,
      sessionTimeout: setTimeout(() => {}, 60 * 60 * 1000),
      close: mockClose,
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('should start in idle state', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    expect(result.current.sessionState).toBe('idle');
    expect(result.current.timeRemaining).toBeNull();
  });

  it('should connect and transition to connected state', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockFetch).toHaveBeenCalledWith('/api/voice/session', expect.any(Object));
    expect(mockCreateVoiceSession).toHaveBeenCalledWith(
      expect.objectContaining({
        token: 'ek_test',
        model: 'gpt-realtime-mini',
        needsMicrophone: false,
      }),
    );
    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('connecting');
    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('connected');
  });

  it('should request microphone for voice_edit mode', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('voice_edit');
    });

    expect(mockCreateVoiceSession).toHaveBeenCalledWith(
      expect.objectContaining({ needsMicrophone: true }),
    );
  });

  it('should disconnect and clean up resources', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    act(() => {
      result.current.disconnect();
    });

    expect(mockClose).toHaveBeenCalled();
    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('idle');
  });

  it('should prevent double-connect', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    // Should only have been called once
    expect(mockCreateVoiceSession).toHaveBeenCalledTimes(1);
  });

  it('should clean up on unmount', async () => {
    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result, unmount } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    unmount();

    expect(mockClose).toHaveBeenCalled();
  });

  it('should set error state on connection failure', async () => {
    mockFetch.mockRejectedValueOnce(new Error('Network error'));

    const { useRealtimeSession } = await import('@/hooks/useRealtimeSession');
    const { result } = renderHook(() => useRealtimeSession());

    await act(async () => {
      await result.current.connect('read_aloud');
    });

    expect(mockSetVoiceSessionState).toHaveBeenCalledWith('error');
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/hooks/useRealtimeSession.ts`
```typescript
import { useRef, useEffect, useCallback, useState } from 'react';
import { createVoiceSession, VoiceSession } from '@/lib/voice-session';
import { useConversationStore } from '@/lib/store';
import type { VoiceMode } from '@/lib/voice-types';
import { VOICE_MODES } from '@/lib/voice-types';

export function useRealtimeSession() {
  const sessionRef = useRef<VoiceSession | null>(null);
  const connectingRef = useRef(false);
  const [timeRemaining, setTimeRemaining] = useState<number | null>(null);
  const timerRef = useRef<ReturnType<typeof setInterval> | null>(null);

  const { voiceSessionState, setVoiceSessionState } = useConversationStore();

  const connect = useCallback(async (mode: VoiceMode, options?: {
    instructions?: string;
    tools?: unknown[];
  }) => {
    // Prevent double-connect
    if (sessionRef.current || connectingRef.current) return;
    connectingRef.current = true;

    setVoiceSessionState('connecting');

    try {
      const response = await fetch('/api/voice/session', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          mode,
          instructions: options?.instructions,
          tools: options?.tools,
        }),
      });

      if (!response.ok) throw new Error('Failed to create session');

      const { token, model, sessionLimitMinutes } = await response.json();

      const session = await createVoiceSession({
        token,
        model,
        sessionLimitMinutes,
        needsMicrophone: mode === VOICE_MODES.VOICE_EDIT,
      });

      sessionRef.current = session;
      setVoiceSessionState('connected');

      // Start countdown timer
      const endTime = Date.now() + sessionLimitMinutes * 60 * 1000;
      timerRef.current = setInterval(() => {
        const remaining = Math.max(0, Math.floor((endTime - Date.now()) / 1000));
        setTimeRemaining(remaining);
        if (remaining <= 0) {
          disconnect();
        }
      }, 1000);
    } catch {
      setVoiceSessionState('error');
    } finally {
      connectingRef.current = false;
    }
  }, [setVoiceSessionState]);

  const disconnect = useCallback(() => {
    if (timerRef.current) {
      clearInterval(timerRef.current);
      timerRef.current = null;
    }
    sessionRef.current?.close();
    sessionRef.current = null;
    setTimeRemaining(null);
    setVoiceSessionState('idle');
  }, [setVoiceSessionState]);

  const sendEvent = useCallback((event: Record<string, unknown>) => {
    const dc = sessionRef.current?.dc;
    if (dc && dc.readyState === 'open') {
      dc.send(JSON.stringify(event));
    }
  }, []);

  // Cleanup on unmount
  useEffect(() => {
    return () => {
      disconnect();
    };
  }, [disconnect]);

  return {
    sessionState: voiceSessionState,
    timeRemaining,
    connect,
    disconnect,
    sendEvent,
    dataChannel: sessionRef.current?.dc ?? null,
  };
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/hooks/useRealtimeSession.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/hooks/useRealtimeSession.test.ts`
- [ ] All existing tests still pass: `cd frontend && npx vitest run`

---

## Behavior 6: Read Aloud Toggle Component

### Test Specification
**Given**: A `ReadAloudToggle` component in the conversation area
**When**: The user clicks the toggle
**Then**: It toggles `readAloudEnabled` in the store, connects/disconnects the Realtime session

**Edge Cases**:
- Toggle ON → initiates connection → shows connecting state → shows connected state
- Toggle OFF → disconnects session
- Disabled state during connection
- Error state display

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/components/ReadAloudToggle.test.tsx`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

const mockConnect = vi.fn();
const mockDisconnect = vi.fn();

vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    sessionState: 'idle',
    timeRemaining: null,
    connect: mockConnect,
    disconnect: mockDisconnect,
  }),
}));

const mockSetReadAloud = vi.fn();
vi.mock('@/lib/store', () => ({
  useConversationStore: vi.fn(() => ({
    readAloudEnabled: false,
    setReadAloud: mockSetReadAloud,
  })),
}));

describe('ReadAloudToggle', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should render a toggle button with "Read Aloud" label', async () => {
    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    expect(screen.getByRole('button', { name: /read aloud/i })).toBeInTheDocument();
  });

  it('should show OFF state by default', async () => {
    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    const button = screen.getByRole('button', { name: /read aloud/i });
    expect(button).toHaveAttribute('aria-pressed', 'false');
  });

  it('should call setReadAloud(true) and connect on click when OFF', async () => {
    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    const user = userEvent.setup();
    await user.click(screen.getByRole('button', { name: /read aloud/i }));

    expect(mockSetReadAloud).toHaveBeenCalledWith(true);
    expect(mockConnect).toHaveBeenCalledWith('read_aloud');
  });

  it('should show ON state and disconnect on click when ON', async () => {
    vi.mocked(await import('@/lib/store')).useConversationStore.mockReturnValue({
      readAloudEnabled: true,
      setReadAloud: mockSetReadAloud,
    } as unknown as ReturnType<typeof import('@/lib/store').useConversationStore>);

    const { default: ReadAloudToggle } = await import(
      '@/components/chat/ReadAloudToggle'
    );
    render(<ReadAloudToggle />);

    const user = userEvent.setup();
    await user.click(screen.getByRole('button', { name: /read aloud/i }));

    expect(mockSetReadAloud).toHaveBeenCalledWith(false);
    expect(mockDisconnect).toHaveBeenCalled();
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/components/chat/ReadAloudToggle.tsx`
```typescript
'use client';

import { Volume2, VolumeX } from 'lucide-react';
import { useConversationStore } from '@/lib/store';
import { useRealtimeSession } from '@/hooks/useRealtimeSession';
import { VOICE_MODES } from '@/lib/voice-types';

export default function ReadAloudToggle() {
  const { readAloudEnabled, setReadAloud } = useConversationStore();
  const { connect, disconnect, sessionState } = useRealtimeSession();

  const isConnecting = sessionState === 'connecting';

  const handleToggle = () => {
    if (readAloudEnabled) {
      setReadAloud(false);
      disconnect();
    } else {
      setReadAloud(true);
      connect(VOICE_MODES.READ_ALOUD);
    }
  };

  return (
    <button
      onClick={handleToggle}
      disabled={isConnecting}
      aria-pressed={readAloudEnabled}
      aria-label="Read Aloud"
      className={`flex items-center gap-1.5 px-3 py-1.5 rounded-md text-sm transition-colors ${
        readAloudEnabled
          ? 'bg-primary text-primary-foreground'
          : 'bg-muted text-muted-foreground hover:bg-muted/80'
      } ${isConnecting ? 'opacity-50 cursor-not-allowed' : ''}`}
    >
      {readAloudEnabled ? (
        <Volume2 className="h-4 w-4" />
      ) : (
        <VolumeX className="h-4 w-4" />
      )}
      Read Aloud
    </button>
  );
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/components/ReadAloudToggle.test.tsx`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/components/ReadAloudToggle.test.tsx`
- [ ] All existing tests still pass: `cd frontend && npx vitest run`

---

## Behavior 7: TTS Queue for Read Aloud

### Test Specification
**Given**: Read Aloud is enabled and a WebRTC session is connected
**When**: New agent messages arrive
**Then**: Messages are queued and played in FIFO order. The next message plays after the current one finishes.

**Edge Cases**:
- Multiple messages arriving quickly → all queued in order
- Session disconnects mid-queue → queue cleared
- Empty content messages → skipped

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/tts-queue.test.ts`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';

describe('TTSQueue', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should enqueue text and process immediately if idle', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('Hello world');

    expect(mockSendEvent).toHaveBeenCalledWith(
      expect.objectContaining({
        type: 'conversation.item.create',
      }),
    );
    expect(mockSendEvent).toHaveBeenCalledWith(
      expect.objectContaining({
        type: 'response.create',
      }),
    );
  });

  it('should queue multiple messages and process them in order', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('First message');
    queue.enqueue('Second message');
    queue.enqueue('Third message');

    // Only first should be sent immediately
    const createCalls = mockSendEvent.mock.calls.filter(
      ([e]: [{ type: string }]) => e.type === 'conversation.item.create',
    );
    expect(createCalls).toHaveLength(1);
    expect(createCalls[0][0].item.content[0].text).toBe('First message');
  });

  it('should process next message when current finishes', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('First');
    queue.enqueue('Second');

    // Simulate response.done event
    queue.handleResponseDone();

    const createCalls = mockSendEvent.mock.calls.filter(
      ([e]: [{ type: string }]) => e.type === 'conversation.item.create',
    );
    expect(createCalls).toHaveLength(2);
    expect(createCalls[1][0].item.content[0].text).toBe('Second');
  });

  it('should skip empty content', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('');
    queue.enqueue('   ');

    expect(mockSendEvent).not.toHaveBeenCalled();
  });

  it('should clear queue on reset', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    queue.enqueue('First');
    queue.enqueue('Second');
    queue.reset();
    queue.handleResponseDone();

    // Only the initial first message should have been sent
    const createCalls = mockSendEvent.mock.calls.filter(
      ([e]: [{ type: string }]) => e.type === 'conversation.item.create',
    );
    expect(createCalls).toHaveLength(1);
  });

  it('should report queue length', async () => {
    const { TTSQueue } = await import('@/lib/tts-queue');
    const mockSendEvent = vi.fn();
    const queue = new TTSQueue(mockSendEvent);

    expect(queue.length).toBe(0);
    queue.enqueue('First');
    expect(queue.length).toBe(0); // Processing, not queued
    queue.enqueue('Second');
    expect(queue.length).toBe(1); // One waiting
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/lib/tts-queue.ts`
```typescript
type SendEventFn = (event: Record<string, unknown>) => void;

export class TTSQueue {
  private queue: string[] = [];
  private isProcessing = false;
  private sendEvent: SendEventFn;

  constructor(sendEvent: SendEventFn) {
    this.sendEvent = sendEvent;
  }

  /** Update sendEvent reference (e.g., when session reconnects) */
  setSendEvent(sendEvent: SendEventFn): void {
    this.sendEvent = sendEvent;
  }

  enqueue(text: string): void {
    if (!text.trim()) return;

    if (!this.isProcessing) {
      this.isProcessing = true;
      this.playText(text);
    } else {
      this.queue.push(text);
    }
  }

  handleResponseDone(): void {
    if (this.queue.length > 0) {
      const next = this.queue.shift()!;
      this.playText(next);
    } else {
      this.isProcessing = false;
    }
  }

  reset(): void {
    this.queue = [];
    // isProcessing remains true until handleResponseDone clears it
  }

  get length(): number {
    return this.queue.length;
  }

  private playText(text: string): void {
    this.sendEvent({
      type: 'conversation.item.create',
      item: {
        type: 'message',
        role: 'user',
        content: [{ type: 'input_text', text }],
      },
    });
    this.sendEvent({
      type: 'response.create',
      response: {
        modalities: ['audio'],
      },
    });
  }
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/lib/tts-queue.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/lib/tts-queue.test.ts`
- [ ] All existing tests still pass: `cd frontend && npx vitest run`

---

## Behavior 8: Auto-Read New Agent Messages

### Test Specification
**Given**: Read Aloud is enabled and the TTS session is connected
**When**: A new assistant message is added to the store
**Then**: The message content is automatically enqueued in the TTS queue

This behavior integrates the Read Aloud toggle, the session hook, the TTS queue, and the store's `addMessage` flow. It is primarily tested as an integration behavior in the page component.

**Edge Cases**:
- Only assistant messages trigger TTS (not user messages)
- Messages added while Read Aloud is OFF are not queued
- Messages from before enabling Read Aloud are not retroactively read

**Important**: `handleResponseDone()` must be wired to the data channel's `response.done` events in the page integration (Behavior 13). Without this wiring, the TTS queue processes only the first message and stalls.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/hooks/useAutoReadAloud.test.ts`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { renderHook } from '@testing-library/react';

const mockEnqueue = vi.fn();
vi.mock('@/lib/tts-queue', () => ({
  TTSQueue: vi.fn().mockImplementation(() => ({
    enqueue: mockEnqueue,
    handleResponseDone: vi.fn(),
    reset: vi.fn(),
    length: 0,
  })),
}));

describe('useAutoReadAloud', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should enqueue new assistant messages when readAloudEnabled is true', async () => {
    const { useAutoReadAloud } = await import('@/hooks/useAutoReadAloud');
    const { result } = renderHook(() =>
      useAutoReadAloud({
        readAloudEnabled: true,
        isConnected: true,
        sendEvent: vi.fn(),
      }),
    );

    result.current.onNewAssistantMessage('Hello from the agent');

    expect(mockEnqueue).toHaveBeenCalledWith('Hello from the agent');
  });

  it('should NOT enqueue when readAloudEnabled is false', async () => {
    const { useAutoReadAloud } = await import('@/hooks/useAutoReadAloud');
    const { result } = renderHook(() =>
      useAutoReadAloud({
        readAloudEnabled: false,
        isConnected: true,
        sendEvent: vi.fn(),
      }),
    );

    result.current.onNewAssistantMessage('Hello');

    expect(mockEnqueue).not.toHaveBeenCalled();
  });

  it('should NOT enqueue when session is not connected', async () => {
    const { useAutoReadAloud } = await import('@/hooks/useAutoReadAloud');
    const { result } = renderHook(() =>
      useAutoReadAloud({
        readAloudEnabled: true,
        isConnected: false,
        sendEvent: vi.fn(),
      }),
    );

    result.current.onNewAssistantMessage('Hello');

    expect(mockEnqueue).not.toHaveBeenCalled();
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/hooks/useAutoReadAloud.ts`
```typescript
import { useRef, useCallback, useEffect } from 'react';
import { TTSQueue } from '@/lib/tts-queue';

interface UseAutoReadAloudOptions {
  readAloudEnabled: boolean;
  isConnected: boolean;
  sendEvent: (event: Record<string, unknown>) => void;
}

export function useAutoReadAloud({ readAloudEnabled, isConnected, sendEvent }: UseAutoReadAloudOptions) {
  const queueRef = useRef<TTSQueue | null>(null);

  if (!queueRef.current) {
    queueRef.current = new TTSQueue(sendEvent);
  }

  // Keep sendEvent reference current (fixes stale closure from constructor capture)
  useEffect(() => {
    queueRef.current?.setSendEvent(sendEvent);
  }, [sendEvent]);

  const onNewAssistantMessage = useCallback(
    (content: string) => {
      if (readAloudEnabled && isConnected && queueRef.current) {
        queueRef.current.enqueue(content);
      }
    },
    [readAloudEnabled, isConnected],
  );

  const handleResponseDone = useCallback(() => {
    queueRef.current?.handleResponseDone();
  }, []);

  const resetQueue = useCallback(() => {
    queueRef.current?.reset();
  }, []);

  return { onNewAssistantMessage, handleResponseDone, resetQueue };
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/hooks/useAutoReadAloud.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/hooks/useAutoReadAloud.test.ts`

---

## Behavior 9: Voice Session Timer Component

### Test Specification
**Given**: A `VoiceSessionTimer` component
**When**: A voice session is active
**Then**: Displays remaining time in MM:SS format. Shows warning colors as time runs low.

**Edge Cases**:
- Not rendered when `timeRemaining` is null
- Yellow at < 5 minutes
- Red at < 1 minute

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/components/VoiceSessionTimer.test.tsx`
```typescript
import { describe, it, expect } from 'vitest';
import { render, screen } from '@testing-library/react';

describe('VoiceSessionTimer', () => {
  it('should not render when timeRemaining is null', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    const { container } = render(<VoiceSessionTimer timeRemaining={null} />);
    expect(container.firstChild).toBeNull();
  });

  it('should display time in MM:SS format', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={1234} />);
    expect(screen.getByText('20:34')).toBeInTheDocument();
  });

  it('should show normal color when time > 5 minutes', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={600} />);
    const timer = screen.getByTestId('voice-session-timer');
    expect(timer.className).toContain('text-muted-foreground');
  });

  it('should show warning color when time <= 5 minutes', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={299} />);
    const timer = screen.getByTestId('voice-session-timer');
    expect(timer.className).toContain('text-yellow');
  });

  it('should show critical color when time <= 1 minute', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={59} />);
    const timer = screen.getByTestId('voice-session-timer');
    expect(timer.className).toContain('text-red');
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/components/chat/VoiceSessionTimer.tsx`
```typescript
import { Clock } from 'lucide-react';

interface VoiceSessionTimerProps {
  timeRemaining: number | null;
}

function formatTime(seconds: number): string {
  const m = Math.floor(seconds / 60);
  const s = seconds % 60;
  return `${m}:${s.toString().padStart(2, '0')}`;
}

function getTimerColor(seconds: number): string {
  if (seconds <= 60) return 'text-red-500';
  if (seconds <= 300) return 'text-yellow-500';
  return 'text-muted-foreground';
}

export default function VoiceSessionTimer({ timeRemaining }: VoiceSessionTimerProps) {
  if (timeRemaining === null) return null;

  return (
    <div
      data-testid="voice-session-timer"
      className={`flex items-center gap-1 text-sm font-mono ${getTimerColor(timeRemaining)}`}
    >
      <Clock className="h-3.5 w-3.5" />
      {formatTime(timeRemaining)}
    </div>
  );
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/components/VoiceSessionTimer.test.tsx`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/components/VoiceSessionTimer.test.tsx`

---

## Behavior 10: Voice Edit Instruction Processing (Main LLM)

### Test Specification
**Given**: A voice edit instruction from the Realtime API
**When**: The instruction is sent to the Main Text LLM via a new API route
**Then**: The Main LLM applies the edit to the specified message content and returns the edited text

This is the middle layer of the three-layer architecture: Realtime API extracts the user's intent as a structured instruction, and the Main LLM applies it to the document text.

**Edge Cases**:
- Edit instruction with specific target message
- Edit instruction without target (LLM decides based on context)
- Failed edit (LLM can't understand instruction) → returns original content with error

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/api/voice-edit.test.ts`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { NextRequest } from 'next/server';

const mockCreate = vi.fn();
vi.mock('openai', () => ({
  default: vi.fn().mockImplementation(() => ({
    chat: {
      completions: {
        create: mockCreate,
      },
    },
  })),
}));

function createRequest(body: Record<string, unknown>): NextRequest {
  return new NextRequest('http://localhost:3000/api/voice/edit', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

describe('POST /api/voice/edit', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    process.env.OPENAI_API_KEY = 'test-key';
  });

  it('should apply edit instruction to message content', async () => {
    mockCreate.mockResolvedValueOnce({
      choices: [{
        message: {
          content: JSON.stringify({
            edited_content: 'The quick brown fox jumped gracefully over the lazy dog.',
            edit_summary: 'Added adverb "gracefully"',
          }),
        },
      }],
    });

    const { POST } = await import('@/app/api/voice/edit/route');
    const response = await POST(createRequest({
      instruction: 'Add the word gracefully before "over"',
      messageContent: 'The quick brown fox jumped over the lazy dog.',
      messageId: 'msg-1',
    }));

    const data = await response.json();
    expect(response.status).toBe(200);
    expect(data.editedContent).toBe(
      'The quick brown fox jumped gracefully over the lazy dog.',
    );
    expect(data.editSummary).toBe('Added adverb "gracefully"');
    expect(data.messageId).toBe('msg-1');
  });

  it('should include document context when provided', async () => {
    mockCreate.mockResolvedValueOnce({
      choices: [{
        message: {
          content: JSON.stringify({
            edited_content: 'Updated content',
            edit_summary: 'Applied edit',
          }),
        },
      }],
    });

    const { POST } = await import('@/app/api/voice/edit/route');
    await POST(createRequest({
      instruction: 'Fix the typo in the introduction',
      messageContent: 'The intrduction explains the concept.',
      messageId: 'msg-1',
      documentContext: [
        { messageId: 'msg-0', content: 'Title: My Essay' },
        { messageId: 'msg-1', content: 'The intrduction explains the concept.' },
      ],
    }));

    // Verify the LLM received document context
    const callArgs = mockCreate.mock.calls[0][0];
    const systemMessage = callArgs.messages.find(
      (m: { role: string }) => m.role === 'system',
    );
    expect(systemMessage.content).toContain('My Essay');
  });

  it('should return 500 when OPENAI_API_KEY is missing', async () => {
    delete process.env.OPENAI_API_KEY;

    const { POST } = await import('@/app/api/voice/edit/route');
    const response = await POST(createRequest({
      instruction: 'Fix typo',
      messageContent: 'Content',
      messageId: 'msg-1',
    }));

    expect(response.status).toBe(500);
  });

  it('should return 400 when required fields are missing', async () => {
    const { POST } = await import('@/app/api/voice/edit/route');
    const response = await POST(createRequest({
      instruction: 'Fix typo',
      // missing messageContent and messageId
    }));

    expect(response.status).toBe(400);
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/app/api/voice/edit/route.ts`
```typescript
import { NextRequest, NextResponse } from 'next/server';
import OpenAI from 'openai';

interface DocumentContextItem {
  messageId: string;
  content: string;
}

export async function POST(request: NextRequest) {
  const apiKey = process.env.OPENAI_API_KEY;
  if (!apiKey) {
    return NextResponse.json({ error: 'Not configured' }, { status: 500 });
  }

  const body = await request.json();
  const { instruction, messageContent, messageId, documentContext } = body;

  if (!instruction || !messageContent || !messageId) {
    return NextResponse.json(
      { error: 'Missing required fields: instruction, messageContent, messageId' },
      { status: 400 },
    );
  }

  const openai = new OpenAI({ apiKey });

  const systemPrompt = buildSystemPrompt(messageContent, messageId, documentContext);

  try {
    const completion = await openai.chat.completions.create({
      model: 'gpt-4o-mini',
      temperature: 0.3,
      messages: [
        { role: 'system', content: systemPrompt },
        { role: 'user', content: instruction },
      ],
      response_format: { type: 'json_object' },
    });

    let result: { edited_content?: string; edit_summary?: string };
    try {
      result = JSON.parse(completion.choices[0].message.content ?? '{}');
    } catch {
      // LLM returned non-JSON — return original content
      return NextResponse.json({
        editedContent: messageContent,
        editSummary: 'Edit could not be applied (invalid response)',
        messageId,
      });
    }

    return NextResponse.json({
      editedContent: result.edited_content ?? messageContent,
      editSummary: result.edit_summary ?? '',
      messageId,
    });
  } catch (err) {
    const status = (err as { status?: number }).status;
    if (status === 429) {
      return NextResponse.json({ error: 'Rate limited' }, { status: 503 });
    }
    return NextResponse.json({ error: 'Edit failed' }, { status: 502 });
  }
}

function buildSystemPrompt(
  messageContent: string,
  messageId: string,
  documentContext?: DocumentContextItem[],
): string {
  let context = '';
  if (documentContext?.length) {
    context = `\n\nFULL DOCUMENT CONTEXT:\n${documentContext
      .map((d) => `[Message ${d.messageId}]:\n${d.content}`)
      .join('\n\n---\n\n')}`;
  }

  return `You are a precise text editing assistant. Apply the user's edit instruction to the target message.

TARGET MESSAGE (ID: ${messageId}):
${messageContent}
${context}

Respond with a JSON object containing:
- "edited_content": The complete edited text of the target message
- "edit_summary": A brief summary of what was changed

Important:
- Return the COMPLETE edited text, not just the changed parts
- Preserve all formatting (markdown, line breaks, etc.)
- Only change what the instruction asks for
- If the instruction is unclear, make your best interpretation`;
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/api/voice-edit.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/api/voice-edit.test.ts`
- [ ] All existing tests still pass: `cd frontend && npx vitest run`

---

## Behavior 11: Voice Edit Session Orchestration

### Test Specification
**Given**: The user activates voice edit mode
**When**: The Realtime API session is established with voice editing configuration
**Then**: The session handles the three-layer flow: voice → intent extraction → Main LLM edit → TTS read-back → undo support

This is the orchestration hook that wires together:
1. Realtime API connection (voice_edit mode)
2. Data channel message handling for `send_edit_instruction` function calls
3. Forwarding instructions to `/api/voice/edit`
4. Applying edits via store's `replaceMessage()` + `pushEdit()`
5. TTS read-back of edited text
6. Undo via `popEdit()` + `replaceMessage()`

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/hooks/useVoiceEdit.test.ts`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { renderHook, act } from '@testing-library/react';

const mockConnect = vi.fn();
const mockDisconnect = vi.fn();
const mockSendEvent = vi.fn();
let mockDcOnMessage: ((event: { data: string }) => void) | null = null;

vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    sessionState: 'connected',
    timeRemaining: 2000,
    connect: mockConnect,
    disconnect: mockDisconnect,
    sendEvent: mockSendEvent,
    dataChannel: {
      set onmessage(handler: ((event: { data: string }) => void) | null) {
        mockDcOnMessage = handler;
      },
      get onmessage() { return mockDcOnMessage; },
    },
  }),
}));

const mockReplaceMessage = vi.fn();
const mockInitEditHistory = vi.fn();
const mockSnapshotOriginal = vi.fn();
const mockPushEdit = vi.fn();
const mockPopEdit = vi.fn();
const mockClearEditHistory = vi.fn();

vi.mock('@/lib/store', () => ({
  useConversationStore: Object.assign(
    vi.fn(() => ({
      activeProjectId: 'proj-1',
      replaceMessage: mockReplaceMessage,
      initEditHistory: mockInitEditHistory,
      snapshotOriginal: mockSnapshotOriginal,
      pushEdit: mockPushEdit,
      popEdit: mockPopEdit,
      clearEditHistory: mockClearEditHistory,
      getMessages: vi.fn(() => [
        { id: 'msg-1', role: 'assistant', content: 'Original text', timestamp: new Date() },
      ]),
    })),
    { getState: vi.fn() },
  ),
}));

const mockFetch = vi.fn();
vi.stubGlobal('fetch', mockFetch);

describe('useVoiceEdit', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockFetch.mockResolvedValue({
      ok: true,
      json: async () => ({
        editedContent: 'Edited text',
        editSummary: 'Changed something',
        messageId: 'msg-1',
      }),
    });
  });

  it('should start a voice edit session with document context', async () => {
    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    const { result } = renderHook(() => useVoiceEdit());

    await act(async () => {
      await result.current.startEditing();
    });

    expect(mockConnect).toHaveBeenCalledWith('voice_edit', expect.objectContaining({
      instructions: expect.stringContaining('editing assistant'),
      tools: expect.arrayContaining([
        expect.objectContaining({ name: 'send_edit_instruction' }),
      ]),
    }));
    expect(mockInitEditHistory).toHaveBeenCalledWith('proj-1', expect.any(String));
  });

  it('should handle send_edit_instruction function call from Realtime API', async () => {
    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    renderHook(() => useVoiceEdit());

    // Simulate Realtime API function call
    const functionCallEvent = {
      data: JSON.stringify({
        type: 'response.function_call_arguments.done',
        name: 'send_edit_instruction',
        arguments: JSON.stringify({
          instruction: 'Fix the typo',
          target_message_id: 'msg-1',
        }),
      }),
    };

    await act(async () => {
      mockDcOnMessage?.(functionCallEvent);
    });

    // Should have called the edit API
    expect(mockFetch).toHaveBeenCalledWith('/api/voice/edit', expect.any(Object));

    // Should have applied the edit
    expect(mockSnapshotOriginal).toHaveBeenCalledWith('msg-1', 'Original text');
    expect(mockPushEdit).toHaveBeenCalledWith(expect.objectContaining({
      messageId: 'msg-1',
      editedContent: 'Edited text',
    }));
    expect(mockReplaceMessage).toHaveBeenCalled();
  });

  it('should undo the last edit', async () => {
    mockPopEdit.mockReturnValueOnce({
      messageId: 'msg-1',
      previousContent: 'Original text',
    });

    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    const { result } = renderHook(() => useVoiceEdit());

    act(() => {
      result.current.undo();
    });

    expect(mockPopEdit).toHaveBeenCalled();
    expect(mockReplaceMessage).toHaveBeenCalledWith(
      'proj-1',
      'msg-1',
      expect.objectContaining({ content: 'Original text' }),
    );
  });

  it('should clean up edit history on stop', async () => {
    const { useVoiceEdit } = await import('@/hooks/useVoiceEdit');
    const { result } = renderHook(() => useVoiceEdit());

    act(() => {
      result.current.stopEditing();
    });

    expect(mockDisconnect).toHaveBeenCalled();
    expect(mockClearEditHistory).toHaveBeenCalled();
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/hooks/useVoiceEdit.ts`
```typescript
import { useCallback, useEffect, useRef } from 'react';
import { useRealtimeSession } from '@/hooks/useRealtimeSession';
import { useConversationStore } from '@/lib/store';
import { VOICE_MODES, createEditEntry } from '@/lib/voice-types';

const EDIT_TOOL = {
  type: 'function' as const,
  name: 'send_edit_instruction',
  description:
    'Send an edit instruction to apply to the document. Call this when the user describes an edit they want to make.',
  parameters: {
    type: 'object',
    properties: {
      instruction: {
        type: 'string',
        description: 'The edit instruction to apply',
      },
      target_message_id: {
        type: 'string',
        description: 'The ID of the message to edit, if specified by the user',
      },
    },
    required: ['instruction'],
  },
};

export function useVoiceEdit() {
  const { connect, disconnect, sendEvent, dataChannel } = useRealtimeSession();
  const {
    activeProjectId,
    replaceMessage,
    getMessages,
    initEditHistory,
    snapshotOriginal,
    pushEdit,
    popEdit,
    clearEditHistory,
  } = useConversationStore();

  const sessionIdRef = useRef<string | null>(null);

  const startEditing = useCallback(async () => {
    if (!activeProjectId) return;

    const sessionId = crypto.randomUUID();
    sessionIdRef.current = sessionId;
    initEditHistory(activeProjectId, sessionId);

    const messages = getMessages(activeProjectId);
    const assistantMessages = messages.filter((m) => m.role === 'assistant');
    const documentPreview = assistantMessages
      .map((m) => `[Message ${m.id}]: ${m.content.slice(0, 200)}...`)
      .join('\n');

    await connect(VOICE_MODES.VOICE_EDIT, {
      instructions: `You are a voice editing assistant. The user will speak edit instructions for their document. When the user describes an edit, call send_edit_instruction with the instruction text.\n\nDOCUMENT MESSAGES:\n${documentPreview}`,
      tools: [EDIT_TOOL],
    });
  }, [activeProjectId, connect, getMessages, initEditHistory]);

  const handleEditInstruction = useCallback(
    async (instruction: string, targetMessageId?: string) => {
      if (!activeProjectId) return;

      const messages = getMessages(activeProjectId);
      const targetMessage = targetMessageId
        ? messages.find((m) => m.id === targetMessageId)
        : messages.filter((m) => m.role === 'assistant').at(-1);

      if (!targetMessage) return;

      snapshotOriginal(targetMessage.id, targetMessage.content);

      const documentContext = messages
        .filter((m) => m.role === 'assistant')
        .map((m) => ({ messageId: m.id, content: m.content }));

      const response = await fetch('/api/voice/edit', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          instruction,
          messageContent: targetMessage.content,
          messageId: targetMessage.id,
          documentContext,
        }),
      });

      if (!response.ok) {
        // Notify user via TTS that the edit failed
        sendEvent({
          type: 'conversation.item.create',
          item: {
            type: 'message',
            role: 'assistant',
            content: [{ type: 'input_text', text: 'Sorry, I could not apply that edit. Please try again.' }],
          },
        });
        sendEvent({ type: 'response.create', response: { modalities: ['audio'] } });
        return;
      }

      const { editedContent, editSummary, messageId } = await response.json();

      pushEdit(
        createEditEntry({
          messageId,
          editedContent,
          editSummary,
        }),
      );

      replaceMessage(activeProjectId, messageId, {
        ...targetMessage,
        content: editedContent,
      });

      // TTS read-back of the edit summary
      sendEvent({
        type: 'conversation.item.create',
        item: {
          type: 'message',
          role: 'assistant',
          content: [
            {
              type: 'input_text',
              text: `Edit applied: ${editSummary || 'Changes made'}. Here is the updated text: ${editedContent.slice(0, 500)}`,
            },
          ],
        },
      });
      sendEvent({ type: 'response.create', response: { modalities: ['audio'] } });
    },
    [activeProjectId, getMessages, snapshotOriginal, pushEdit, replaceMessage, sendEvent],
  );

  // Listen for data channel messages
  useEffect(() => {
    if (!dataChannel) return;

    const handleMessage = async (event: MessageEvent) => {
      const msg = JSON.parse(event.data);
      if (
        msg.type === 'response.function_call_arguments.done' &&
        msg.name === 'send_edit_instruction'
      ) {
        const args = JSON.parse(msg.arguments);
        await handleEditInstruction(args.instruction, args.target_message_id);
      }
    };

    dataChannel.onmessage = handleMessage;
    return () => {
      dataChannel.onmessage = null;
    };
  }, [dataChannel, handleEditInstruction]);

  const undo = useCallback(() => {
    if (!activeProjectId) return;

    const result = popEdit();
    if (!result) return;

    const messages = getMessages(activeProjectId);
    const targetMessage = messages.find((m) => m.id === result.messageId);
    if (!targetMessage) return;

    replaceMessage(activeProjectId, result.messageId, {
      ...targetMessage,
      content: result.previousContent,
    });
  }, [activeProjectId, popEdit, getMessages, replaceMessage]);

  const stopEditing = useCallback(() => {
    disconnect();
    clearEditHistory();
    sessionIdRef.current = null;
  }, [disconnect, clearEditHistory]);

  return { startEditing, stopEditing, undo };
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/hooks/useVoiceEdit.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/hooks/useVoiceEdit.test.ts`
- [ ] All existing tests still pass: `cd frontend && npx vitest run`

---

## Behavior 12: Voice Edit Panel Component

### Test Specification
**Given**: A `VoiceEditPanel` component rendered in the conversation area
**When**: The user activates voice editing
**Then**: Shows editing controls (start/stop, undo), session timer, and voice activity indicator

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/components/VoiceEditPanel.test.tsx`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';

const mockStartEditing = vi.fn();
const mockStopEditing = vi.fn();
const mockUndo = vi.fn();

vi.mock('@/hooks/useVoiceEdit', () => ({
  useVoiceEdit: () => ({
    startEditing: mockStartEditing,
    stopEditing: mockStopEditing,
    undo: mockUndo,
  }),
}));

vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    sessionState: 'idle',
    timeRemaining: null,
  }),
}));

vi.mock('@/lib/store', () => ({
  useConversationStore: vi.fn(() => ({
    editHistory: null,
  })),
}));

describe('VoiceEditPanel', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should render a Start Voice Edit button when idle', async () => {
    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    expect(screen.getByRole('button', { name: /voice edit/i })).toBeInTheDocument();
  });

  it('should call startEditing when Start button is clicked', async () => {
    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    const user = userEvent.setup();
    await user.click(screen.getByRole('button', { name: /voice edit/i }));

    expect(mockStartEditing).toHaveBeenCalled();
  });

  it('should show stop and undo buttons when session is active', async () => {
    vi.mocked(await import('@/hooks/useRealtimeSession')).useRealtimeSession
      .mockReturnValue({
        sessionState: 'connected',
        timeRemaining: 2100,
      } as ReturnType<typeof import('@/hooks/useRealtimeSession').useRealtimeSession>);

    vi.mocked(await import('@/lib/store')).useConversationStore.mockReturnValue({
      editHistory: { edits: [{ messageId: 'msg-1', editedContent: 'text', timestamp: 1 }] },
    } as unknown as ReturnType<typeof import('@/lib/store').useConversationStore>);

    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    expect(screen.getByRole('button', { name: /stop/i })).toBeInTheDocument();
    expect(screen.getByRole('button', { name: /undo/i })).toBeInTheDocument();
  });

  it('should disable undo when no edits in history', async () => {
    vi.mocked(await import('@/hooks/useRealtimeSession')).useRealtimeSession
      .mockReturnValue({
        sessionState: 'connected',
        timeRemaining: 2100,
      } as ReturnType<typeof import('@/hooks/useRealtimeSession').useRealtimeSession>);

    vi.mocked(await import('@/lib/store')).useConversationStore.mockReturnValue({
      editHistory: { edits: [] },
    } as unknown as ReturnType<typeof import('@/lib/store').useConversationStore>);

    const { default: VoiceEditPanel } = await import(
      '@/components/chat/VoiceEditPanel'
    );
    render(<VoiceEditPanel />);

    expect(screen.getByRole('button', { name: /undo/i })).toBeDisabled();
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/components/chat/VoiceEditPanel.tsx`
```typescript
'use client';

import { Mic, Square, Undo2 } from 'lucide-react';
import { useVoiceEdit } from '@/hooks/useVoiceEdit';
import { useRealtimeSession } from '@/hooks/useRealtimeSession';
import { useConversationStore } from '@/lib/store';
import VoiceSessionTimer from './VoiceSessionTimer';

export default function VoiceEditPanel() {
  const { startEditing, stopEditing, undo } = useVoiceEdit();
  const { sessionState, timeRemaining } = useRealtimeSession();
  const { editHistory } = useConversationStore();

  const isActive = sessionState === 'connected';
  const isConnecting = sessionState === 'connecting';
  const hasEdits = (editHistory?.edits.length ?? 0) > 0;

  if (!isActive && !isConnecting) {
    return (
      <button
        onClick={startEditing}
        aria-label="Voice Edit"
        className="flex items-center gap-1.5 px-3 py-1.5 rounded-md text-sm bg-muted text-muted-foreground hover:bg-muted/80"
      >
        <Mic className="h-4 w-4" />
        Voice Edit
      </button>
    );
  }

  return (
    <div className="flex items-center gap-2">
      <VoiceSessionTimer timeRemaining={timeRemaining} />

      <button
        onClick={undo}
        disabled={!hasEdits}
        aria-label="Undo"
        className="flex items-center gap-1 px-2 py-1 rounded text-sm text-muted-foreground hover:bg-muted disabled:opacity-50 disabled:cursor-not-allowed"
      >
        <Undo2 className="h-3.5 w-3.5" />
        Undo
      </button>

      <button
        onClick={stopEditing}
        aria-label="Stop"
        className="flex items-center gap-1 px-2 py-1 rounded text-sm bg-red-100 text-red-700 hover:bg-red-200"
      >
        <Square className="h-3.5 w-3.5" />
        Stop
      </button>

      {isConnecting && (
        <span className="text-sm text-muted-foreground animate-pulse">
          Connecting...
        </span>
      )}
    </div>
  );
}
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/components/VoiceEditPanel.test.tsx`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/components/VoiceEditPanel.test.tsx`

---

## Behavior 13: Page Integration (Read Aloud + Voice Edit Controls)

### Test Specification
**Given**: The main conversation page
**When**: Voice controls are integrated
**Then**: Read Aloud toggle and Voice Edit panel are visible in the conversation area. New agent messages trigger TTS when Read Aloud is ON.

This behavior integrates all previous behaviors into `page.tsx`. The test focuses on the wiring, not re-testing individual components.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/e2e/VoiceIntegration.test.tsx`
```typescript
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { render, screen } from '@testing-library/react';

// Mock all voice-related modules
vi.mock('@/hooks/useRealtimeSession', () => ({
  useRealtimeSession: () => ({
    sessionState: 'idle',
    timeRemaining: null,
    connect: vi.fn(),
    disconnect: vi.fn(),
    sendEvent: vi.fn(),
    dataChannel: null,
  }),
}));

vi.mock('@/hooks/useAutoReadAloud', () => ({
  useAutoReadAloud: () => ({
    onNewAssistantMessage: vi.fn(),
    handleResponseDone: vi.fn(),
    resetQueue: vi.fn(),
  }),
}));

vi.mock('@/hooks/useVoiceEdit', () => ({
  useVoiceEdit: () => ({
    startEditing: vi.fn(),
    stopEditing: vi.fn(),
    undo: vi.fn(),
  }),
}));

vi.mock('@/lib/store', () => ({
  useConversationStore: vi.fn(() => ({
    projects: [{ id: 'proj-1', name: 'Test' }],
    activeProjectId: 'proj-1',
    createProject: vi.fn(),
    setActiveProject: vi.fn(),
    addMessage: vi.fn(),
    getMessages: vi.fn(() => [
      { id: 'msg-1', role: 'assistant', content: 'Hello', timestamp: new Date() },
    ]),
    _hasHydrated: true,
    readAloudEnabled: false,
    setReadAloud: vi.fn(),
    voiceSessionState: 'idle',
    editHistory: null,
  })),
}));

vi.mock('@/lib/api', () => ({
  generateResponse: vi.fn(),
}));

vi.mock('@/lib/transcription', () => ({
  transcribeAudio: vi.fn(),
}));

describe('Voice Integration in Page', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('should render ReadAloudToggle in conversation area', async () => {
    const { default: HomePage } = await import('@/app/page');
    render(<HomePage />);

    expect(screen.getByRole('button', { name: /read aloud/i })).toBeInTheDocument();
  });

  it('should render VoiceEditPanel in conversation area', async () => {
    const { default: HomePage } = await import('@/app/page');
    render(<HomePage />);

    expect(screen.getByRole('button', { name: /voice edit/i })).toBeInTheDocument();
  });
});
```

#### 🟢 Green: Minimal Implementation

**Changes to**: `frontend/src/app/page.tsx`
- Import `ReadAloudToggle` and `VoiceEditPanel` components
- Add a voice controls bar between `ConversationView` and the loading indicators
- Wire `useAutoReadAloud` hook into the message add flow
- **Mutual exclusion**: Enforce single voice mode — toggling Read Aloud ON while Voice Edit is active should stop Voice Edit first (and vice versa). Store-level `voiceMode: 'off' | 'read_aloud' | 'voice_edit'` or check in UI before connect.
- **Wire data channel `response.done` events** to `handleResponseDone()` so the TTS queue dequeues properly

#### 🔵 Refactor
- Extract the voice controls bar into a `VoiceControlBar` component if it grows

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/e2e/VoiceIntegration.test.tsx`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/e2e/VoiceIntegration.test.tsx`
- [ ] All existing tests still pass: `cd frontend && npx vitest run`

---

## Behavior 14: Cost Tracking for Realtime API

### Test Specification
**Given**: The existing cost tracking system
**When**: Voice sessions are used
**Then**: Realtime API costs are estimated and tracked using the correct pricing models

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/lib/voice-cost-tracking.test.ts`
```typescript
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
    const estimate = estimateReadAloudCost(60); // 60 minutes
    expect(estimate.estimatedCost).toBeGreaterThan(0);
    expect(estimate.model).toBe('gpt-realtime-mini');
  });

  it('should estimate Voice Edit session cost for given duration', async () => {
    const { estimateVoiceEditCost } = await import('@/lib/voice-cost-tracking');
    const estimate = estimateVoiceEditCost(60);
    expect(estimate.estimatedCost).toBeGreaterThan(0);
    expect(estimate.model).toBe('gpt-realtime');
    // Voice edit is more expensive
    const readAloudEstimate = (await import('@/lib/voice-cost-tracking')).estimateReadAloudCost(60);
    expect(estimate.estimatedCost).toBeGreaterThan(readAloudEstimate.estimatedCost);
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/lib/voice-cost-tracking.ts`
```typescript
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
const TOKENS_PER_MINUTE_AUDIO_INPUT = 600;   // 1 token per 100ms
const TOKENS_PER_MINUTE_AUDIO_OUTPUT = 1200;  // 1 token per 50ms

interface CostEstimate {
  estimatedCost: number;
  model: string;
  breakdown: { label: string; amount: number }[];
}

export function estimateReadAloudCost(durationMinutes: number): CostEstimate {
  const model = 'gpt-realtime-mini';
  const pricing = REALTIME_PRICING[model];
  // Read Aloud: primarily output audio (model speaks)
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
  // Voice Edit: bidirectional audio — use directional rates
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
```

### Success Criteria
**Automated:**
- [ ] Test fails for right reason (Red): `cd frontend && npx vitest run __tests__/lib/voice-cost-tracking.test.ts`
- [ ] Test passes (Green): `cd frontend && npx vitest run __tests__/lib/voice-cost-tracking.test.ts`

---

## Implementation Order

The behaviors should be implemented in this order due to dependencies:

```
Behavior 1: Voice Types & Constants         ← Foundation
    │
    ├── Behavior 2: Ephemeral Token API Route    ← Server infrastructure
    │       │
    │       └── Behavior 3: WebRTC Session       ← Client connection
    │               │
    │               ├── Behavior 5: useRealtimeSession Hook
    │               │       │
    │               │       ├── Behavior 6: ReadAloudToggle Component
    │               │       ├── Behavior 7: TTS Queue
    │               │       │       │
    │               │       │       └── Behavior 8: Auto-Read Hook
    │               │       │
    │               │       └── Behavior 9: VoiceSessionTimer
    │               │
    │               └── Behavior 10: Voice Edit API Route (Main LLM)
    │                       │
    │                       └── Behavior 11: useVoiceEdit Hook
    │                               │
    │                               └── Behavior 12: VoiceEditPanel
    │
    ├── Behavior 4: Voice Store Extensions       ← State (parallel with 2-3)
    │
    ├── Behavior 13: Page Integration            ← Wiring everything together
    │
    └── Behavior 14: Cost Tracking               ← Parallel/last
```

**Parallelizable work:**
- Behaviors 2, 4, 14 can be started in parallel (independent)
- Behaviors 6, 7, 9 can be started in parallel (independent components sharing hook)
- Behaviors 10 can start alongside 5-9 (independent API route)

## New File Summary

| File | Purpose |
|------|---------|
| `frontend/src/lib/voice-types.ts` | Types, constants, factory functions |
| `frontend/src/lib/voice-session.ts` | WebRTC connection logic |
| `frontend/src/lib/tts-queue.ts` | FIFO TTS queue |
| `frontend/src/lib/voice-cost-tracking.ts` | Realtime API pricing |
| `frontend/src/app/api/voice/session/route.ts` | Ephemeral token API |
| `frontend/src/app/api/voice/edit/route.ts` | Main LLM edit API |
| `frontend/src/hooks/useRealtimeSession.ts` | WebRTC session lifecycle hook |
| `frontend/src/hooks/useAutoReadAloud.ts` | Auto-read new messages hook |
| `frontend/src/hooks/useVoiceEdit.ts` | Three-layer edit orchestration hook |
| `frontend/src/components/chat/ReadAloudToggle.tsx` | Read Aloud toggle UI |
| `frontend/src/components/chat/VoiceSessionTimer.tsx` | Session countdown timer |
| `frontend/src/components/chat/VoiceEditPanel.tsx` | Voice editing controls |

## Modified Files

| File | Changes |
|------|---------|
| `frontend/src/lib/store.ts` | Add `readAloudEnabled`, `voiceSessionState`, `editHistory` state + actions |
| `frontend/src/app/page.tsx` | Integrate ReadAloudToggle, VoiceEditPanel, useAutoReadAloud |

## References

- Research: `thoughts/searchable/shared/research/2026-02-05-openai-realtime-voice-chat-integration.md`
- Prior voice research: `thoughts/searchable/shared/research/2026-01-16-openai-tools-voice-integration.md`
- Store patterns: `frontend/src/lib/store.ts:111-127` (replaceMessage)
- Message types: `frontend/src/lib/types.ts:49-56`
- API route patterns: `frontend/src/app/api/generate/route.ts`
- Test patterns: `frontend/__tests__/components/AudioRecorder.test.tsx` (browser API mocking)
- Cost tracking: `frontend/src/lib/cost-tracking.ts`
