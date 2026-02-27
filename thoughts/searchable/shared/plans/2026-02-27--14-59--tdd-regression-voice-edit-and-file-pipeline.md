# Regression Recovery: Voice Edit Entry + File Attachment Pipeline TDD Plan

## Overview
This plan addresses two P1 regressions:
- `silmari-writer-lxd`: message-level `Edit` no longer routes into voice edit mode.
- `silmari-writer-6ne`: uploaded file content no longer reaches `/api/generate` and attachment metadata no longer renders in conversation UI.

The implementation is organized as small observable behaviors and strict Red-Green-Refactor loops.

## Current State Analysis

### Key Discoveries
- Message-level edit is still wired to legacy text modal only:
  - `frontend/src/components/chat/ButtonRibbon.tsx:123` sets `isEditModalOpen` and starts blocking operation.
  - `frontend/src/components/chat/EditMessageModal.tsx:44` is text-only; no voice path.
- Voice edit infrastructure is present but disconnected from message-level entry:
  - `frontend/src/hooks/useVoiceEdit.ts:42` exposes `startEditing`.
  - `frontend/src/hooks/useVoiceEdit.ts:55` calls realtime `connect(VOICE_MODES.VOICE_EDIT, ...)`.
  - `frontend/src/hooks/useRealtimeSession.ts:45` maps `VOICE_EDIT` to mic-required realtime session.
- File send pipeline is broken at submit path:
  - `frontend/src/app/page.tsx:30` stores only setter (`[, setFiles]`), so current files are unavailable at send time.
  - `frontend/src/app/page.tsx:64` sends message without any attachment preparation.
  - `frontend/src/lib/api.ts:3` `generateResponse` accepts only `(message, history)`.
  - `frontend/src/app/api/generate/route.ts:39` reads only `{ message, history }` and builds text-only Responses API input.
- Attachment UI plumbing is partially present:
  - `frontend/src/lib/types.ts:54` already has `attachments?: Attachment[]` on `Message`.
  - `frontend/src/components/chat/FileAttachment.tsx` still collects files and calls `onFilesChange`.
  - `frontend/src/components/chat/MessageBubble.tsx` currently does not render attachments.
- Missing artifact confirmed:
  - `frontend/src/lib/file-content.ts` is absent.

### Prior Working References
- Voice-edit baseline: `7df1b55`, `28c58b7`, `1800214`.
- File pipeline baseline: `3675209` (client prep + API payload + route ingestion + tests).

## Desired End State
- Assistant message `Edit` provides a working path into voice edit mode via `useVoiceEdit.startEditing()` and realtime `VOICE_MODES.VOICE_EDIT`.
- Legacy text edit remains reachable as fallback when voice session cannot be started.
- Uploading supported files includes processed attachment payload in `/api/generate` request.
- User message stores attachment metadata and conversation UI displays attachments.
- `/api/generate` validates attachment limits and safely incorporates supported text/image attachments into model input.
- Unsupported file types fail with a user-visible error and do not crash send flow.

### Observable Behaviors
- Behavior LXD-1: Given an assistant message, when user clicks `Edit`, then message-level flow invokes voice edit start path.
- Behavior LXD-2: Given voice edit start path, when it executes, then realtime connects in `voice_edit` mode and seeds targeted message context.
- Behavior LXD-3: Given voice start failure, when user clicks `Edit`, then text modal fallback opens and remains functional.
- Behavior 6NE-1: Given selected supported files, when user sends, then `prepareFilesContent` output is passed to `generateResponse`.
- Behavior 6NE-2: Given user sends with files, when message is added, then attachment metadata is persisted and rendered in message bubble.
- Behavior 6NE-3: Given `/api/generate` receives attachments, when request is processed, then route validates limits and builds attachment-aware user content.
- Behavior 6NE-4: Given unsupported files, when send is attempted, then user sees a clear error and generation call is skipped.

## What We’re NOT Doing
- Rewriting the existing voice session architecture (`useRealtimeSession`, `/api/voice/session`).
- Changing the `/api/upload` + `/api/transcribe` audio transcription pipeline.
- Migrating `/api/generate` away from current Responses API prompt/tooling.
- Broad UI redesign for attachment display beyond restoring concise metadata list.

## Testing Strategy
- **Framework**: Vitest + Testing Library (`frontend`).
- **Test Types**:
  - Unit/component: `ButtonRibbon`, `MessageBubble`, `file-content` helper.
  - API route: `/api/generate` attachment ingestion and validation.
  - Integration: end-to-end message send flow with file attachment handoff.
- **Mocking/Setup**:
  - Mock `useVoiceEdit` in `ButtonRibbon` tests for click-path verification.
  - Mock `generateResponse` and `prepareFilesContent` for integration send-flow tests.
  - Mock route-level `fetch` (Responses API call) to assert constructed `input` payloads.

## Behavior LXD-1: Message Edit Button Starts Voice Edit

### Test Specification
**Given**: Assistant message with visible `Edit` button.
**When**: User clicks `Edit`.
**Then**: `useVoiceEdit.startEditing()` is called from message-level flow and blocking state transitions are consistent.

**Edge Cases**:
- Message is blocked (`isMessageBlocked=true`) -> button stays disabled.
- Repeated clicks while already blocked do not trigger duplicate starts.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/components/ButtonRibbon.test.tsx`
```ts
it('routes Edit click to voice edit start path', async () => {
  // arrange: mock useVoiceEdit.startEditing
  // act: click Edit
  // assert: startEditing called, startBlockingOperation called with ('edit')
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/components/chat/ButtonRibbon.tsx`
- Import `useVoiceEdit`.
- Update `handleEditClick` to call `startEditing()`.
- Keep existing blocking-operation semantics.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/components/chat/ButtonRibbon.tsx`
- Extract edit-entry action into small function (`startVoiceEditOrFallback`) for readability and testability.
- Keep analytics and state transitions explicit.

### Success Criteria
**Automated:**
- [x] New `ButtonRibbon` edit-path test fails before wiring.
- [x] New test passes after wiring.
- [x] Existing `ButtonRibbon` tests remain green.

**Manual:**
- [ ] Clicking `Edit` on assistant message visibly enters voice-edit control state (panel/session start cues).

---

## Behavior LXD-2: Voice Edit Starts in `VOICE_MODES.VOICE_EDIT` with Message Context

### Test Specification
**Given**: Message-level edit action provides target message id/content.
**When**: `startEditing` runs.
**Then**: `connect` is called with `VOICE_MODES.VOICE_EDIT` and instructions include target context.

**Edge Cases**:
- Target message no longer exists.
- No active project id.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/hooks/useVoiceEdit.test.ts`
```ts
it('passes voice_edit mode and target message context to realtime connect', async () => {
  // call startEditing({ targetMessageId: 'msg-1' })
  // expect connect('voice_edit', { instructions: ...msg-1... })
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/hooks/useVoiceEdit.ts`
- Extend `startEditing` signature to optionally accept target message metadata.
- Include selected target context in instructions while preserving document overview.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/hooks/useVoiceEdit.ts`
- Move prompt assembly into a pure helper for direct unit testing and easier maintenance.

### Success Criteria
**Automated:**
- [x] New hook test fails first for missing targeted context.
- [x] `useVoiceEdit` tests pass with `connect('voice_edit', ...)` assertions.

**Manual:**
- [ ] Starting edit from a specific assistant message produces contextually correct edit behavior.

---

## Behavior LXD-3: Text Edit Fallback Remains Functional

### Test Specification
**Given**: Voice edit start throws/rejects.
**When**: User clicks message-level `Edit`.
**Then**: Legacy text modal opens and `Save/Cancel` path still works.

**Edge Cases**:
- Voice permissions blocked.
- Realtime endpoint transient failure.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/components/ButtonRibbon.test.tsx`
```ts
it('falls back to EditMessageModal when startEditing fails', async () => {
  // mock startEditing rejection
  // click Edit
  // assert modal opens + no crash
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/components/chat/ButtonRibbon.tsx`
- Wrap `startEditing` in `try/catch`.
- On failure, open `EditMessageModal` and complete/fail operation state cleanly.

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/components/chat/ButtonRibbon.tsx`
- `frontend/src/components/chat/EditMessageModal.tsx` (only if needed)
- Normalize fallback error copy and avoid duplicated completion branches.

### Success Criteria
**Automated:**
- [x] Fallback test fails before try/catch fallback exists.
- [x] Fallback + existing modal tests pass together.

**Manual:**
- [ ] With microphone denied, `Edit` still provides usable text editing path.

---

## Behavior 6NE-1: Send Flow Includes Prepared File Payloads

### Test Specification
**Given**: User has attached supported files.
**When**: User sends a message.
**Then**: `prepareFilesContent(files)` is called and resulting payload is passed as 3rd arg to `generateResponse`.

**Edge Cases**:
- No files selected -> `attachments` omitted.
- Multiple files preserve deterministic order.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/integration/file-send-flow.test.tsx` (reintroduce)
```tsx
it('passes prepared file payloads to generateResponse', async () => {
  // upload file, send message
  // expect prepareFilesContent called with selected files
  // expect generateResponse(message, history, attachments)
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/lib/file-content.ts` (restore helper + validation primitives)
- `frontend/src/app/page.tsx`
- `frontend/src/lib/api.ts`

Implementation slice:
- Track real `files` state (not setter-only tuple).
- Snapshot files in `handleSendMessage`.
- Prepare payloads and pass to `generateResponse`.
- Extend `generateResponse` signature/body with optional `attachments`.

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/app/page.tsx`
- `frontend/src/lib/file-content.ts`
- Extract payload prep/error conversion into helper to keep `handleSendMessage` focused.

### Success Criteria
**Automated:**
- [x] Integration test fails before pipeline restoration.
- [x] Integration test passes with new third-arg payload assertions.

**Manual:**
- [ ] Attach `txt` or `json` file, send message, and verify no client-side crash.

---

## Behavior 6NE-2: Attachment Metadata Persists and Renders

### Test Specification
**Given**: Message sent with selected files.
**When**: User message is added and rendered.
**Then**: `message.attachments` metadata is stored and `MessageBubble` shows attachment list.

**Edge Cases**:
- Metadata absent -> no attachment list rendered.
- Multiple attachments render predictable order.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/__tests__/integration/file-send-flow.test.tsx`
- `frontend/__tests__/components/MessageBubble.test.tsx`
```ts
it('stores user message with attachments metadata', ...)
it('renders attachment list for message with attachments', ...)
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/app/page.tsx` (add attachment metadata to `addMessage` user payload)
- `frontend/src/components/chat/MessageBubble.tsx` (render attachment chips/list)

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/components/chat/MessageBubble.tsx`
- Keep markdown/timestamp rendering unchanged.
- Isolate attachment rendering into small block/component if JSX gets noisy.

### Success Criteria
**Automated:**
- [x] Metadata + render tests fail before UI restoration.
- [x] Both tests pass after restoration.

**Manual:**
- [ ] Sent message visually displays attached filename(s) and size.

---

## Behavior 6NE-3: `/api/generate` Ingests and Validates Attachments

### Test Specification
**Given**: Request includes `attachments` with text and/or image payloads.
**When**: Route builds model input.
**Then**: Supported attachments are folded into user content, limits enforced, and text-only behavior remains backward compatible.

**Edge Cases**:
- Attachment count > limit -> 400.
- Total payload > limit -> 400.
- Unsupported MIME included with supported files -> unsupported skipped safely.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/__tests__/api/generate.test.ts` (or split into `generate-route.test.ts`)
```ts
it('accepts attachments and builds attachment-aware user content', ...)
it('returns ATTACHMENT_LIMIT when count exceeded', ...)
it('returns PAYLOAD_TOO_LARGE when payload exceeded', ...)
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/app/api/generate/route.ts`
- Parse `{ message, history, attachments }`.
- Add route-level limits and payload-size checks.
- Build attachment-aware user content for Responses API format:
  - Text attachments prepended into user text context.
  - Image attachments emitted as image content parts.
- Preserve current system prompt/retry/error contract.

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/app/api/generate/route.ts`
- Extract pure helpers (`isSupportedAttachment`, `buildUserContent`, `calculatePayloadSize`) for direct testing and lower route complexity.

### Success Criteria
**Automated:**
- [x] Route tests fail before attachment ingestion exists.
- [x] Existing route tests still pass for text-only requests.
- [x] New attachment tests pass (mixed, limit, oversized cases).

**Manual:**
- [ ] Prompt output quality remains normal for text-only messages.

---

## Behavior 6NE-4: Unsupported Files Fail Gracefully with User Feedback

### Test Specification
**Given**: User attempts to send unsupported file type (e.g., PDF).
**When**: Send flow validates and prepares file payload.
**Then**: UI shows clear error; generation request is not sent; app remains interactive.

**Edge Cases**:
- Mixed supported + unsupported files.
- File-read failure while converting content.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/__tests__/integration/file-send-flow.test.tsx`
- `frontend/__tests__/lib/file-content.test.ts` (new)
```ts
it('returns unsupported-file error details', ...)
it('surfaces unsupported-file error in UI and skips generateResponse', ...)
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/lib/file-content.ts`
- `frontend/src/app/page.tsx`

Implementation slice:
- Throw structured `UnsupportedFileError` from `prepareFileContent`.
- Convert to user-facing error in page send handler.
- Ensure error path does not crash and always resets loading state.

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/lib/file-content.ts`
- `frontend/src/app/page.tsx`
- Consolidate error mapping (`technical -> user-visible`) in one helper.

### Success Criteria
**Automated:**
- [x] Unsupported-file unit + integration tests fail first.
- [x] Tests pass with clear user-visible error assertions.

**Manual:**
- [ ] Attaching unsupported file shows immediate readable error and allows retry.

---

## Integration and Regression Suite
Run these after each behavior block and at the end:

```bash
cd frontend
npm run test -- __tests__/components/ButtonRibbon.test.tsx
npm run test -- __tests__/hooks/useVoiceEdit.test.ts
npm run test -- __tests__/components/EditMessageModal.test.tsx
npm run test -- __tests__/components/MessageBubble.test.tsx
npm run test -- __tests__/api/generate.test.ts
npm run test -- __tests__/integration/file-send-flow.test.tsx
npm run test -- __tests__/components/FileAttachment.test.tsx
npm run test -- __tests__/lib/transcription.test.ts
npm run test -- __tests__/api/upload.test.ts
npm run lint
npm run type-check
```

## Manual Verification Checklist
- [ ] Assistant message `Edit` enters voice edit mode from message-level action.
- [ ] If voice session init fails/permissions denied, text modal fallback is available and functional.
- [ ] Send with text file includes file context in generated response quality checks.
- [ ] Send with image file includes image payload path without route crash.
- [ ] Unsupported file type shows user-visible error and does not block subsequent sends.
- [ ] Voice transcription file flow (`/api/upload` + `/api/transcribe`) still works.

## Implementation Order
1. LXD-1 (wire button to voice start)
2. LXD-3 (fallback safety)
3. LXD-2 (targeted context refinement)
4. 6NE-1 (client pipeline restoration)
5. 6NE-2 (metadata + UI rendering)
6. 6NE-3 (route ingestion + limits)
7. 6NE-4 (unsupported-file UX hardening)
8. Full regression run + lint/typecheck

## References
- Beads:
  - `silmari-writer-lxd`
  - `silmari-writer-6ne`
- Current divergence:
  - `frontend/src/components/chat/ButtonRibbon.tsx:123`
  - `frontend/src/components/chat/EditMessageModal.tsx:44`
  - `frontend/src/hooks/useVoiceEdit.ts:42`
  - `frontend/src/app/page.tsx:64`
  - `frontend/src/lib/api.ts:3`
  - `frontend/src/app/api/generate/route.ts:39`
- Prior working commits:
  - Voice path: `7df1b55`, `28c58b7`, `1800214`
  - File pipeline: `3675209`
