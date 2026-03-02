# voice-edit-no-input-error-on-review-screen TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/332-voice-edit-no-input-error-on-review-screen.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed:
- **Reachability**
- **TypeInvariant**
- **ErrorConsistency**

Command:
```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/332-voice-edit-no-input-error-on-review-screen.md
```

Verifier output (excerpt):
```
Result: ALL PROPERTIES PASSED
States: 18 found, 9 distinct, depth 0
Properties: Reachability, TypeInvariant, ErrorConsistency
```

This TDD plan mirrors those properties at code level using Vitest + React Testing Library (Next.js + TypeScript, Option 1).

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|---------------|------------------------|
| ui-v3n6 | module | `frontend/modules/review/ReviewModule.ts` |
| ui-w8p2 | component | `frontend/components/review/ReviewScreen.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/VoiceInputVerifier.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/VoiceErrors.ts` |

Testing stack:
- `vitest`
- `@testing-library/react`
- `@testing-library/user-event`

---

# Step 1: Capture edit-by-voice action [x]

**From path spec:**
- [x] Input: User interaction event from review screen component (ui-w8p2, ui-v3n6).
- [x] Process: Detect 'Edit by Voice' and transition UI into voice capture mode.
- [x] Output: Voice capture session initialized within review screen context.
- [x] Error: If initialization fails, display shared error (cfg-j9w2) and remain on review screen.

---

## Test (`frontend/components/review/__tests__/ReviewScreen.step1.test.tsx`) [x]

### Reachability
- [x] Render `ReviewScreen` with mock `ReviewModule` state.
- [x] Click "Edit by Voice" button.
- [x] Assert `voiceMode === 'capturing'`.

### TypeInvariant
- [x] Assert voice session object matches type:
  ```ts
  type VoiceSession = {
    status: 'capturing' | 'idle' | 'error';
    attempts: number;
  }
  ```
- [x] Assert returned session object conforms.

### ErrorConsistency
- [x] Mock `initializeVoiceSession()` to throw.
- [x] Click button.
- [x] Assert error banner rendered with `VoiceErrors.VOICE_INIT_FAILED.code`.
- [x] Assert still on review screen (no navigation).

---

## Implementation [x]

### `shared/error_definitions/VoiceErrors.ts`
```ts
export const VoiceErrors = {
  VOICE_INIT_FAILED: {
    code: 'VOICE_INIT_FAILED',
    message: 'Unable to start voice capture. Please try again.'
  },
  VOICE_INPUT_INVALID: {
    code: 'VOICE_INPUT_INVALID',
    message: 'Voice input could not be processed.'
  },
  GENERIC_VOICE_ERROR: {
    code: 'GENERIC_VOICE_ERROR',
    message: 'Something went wrong with voice input.'
  }
} as const;
```

### `frontend/modules/review/ReviewModule.ts`
- State: `{ voiceSession: VoiceSession | null, content: string }`
- Method: `initializeVoiceSession(): VoiceSession`
  - Returns `{ status: 'capturing', attempts: 0 }`

### `ReviewScreen.tsx`
- Button triggers `initializeVoiceSession()`.
- Catches error → sets error state from `VoiceErrors`.

---

# Step 2: Collect and preliminarily validate voice input [x]

**From path spec:**
- [x] Input: Audio stream or empty/unintelligible audio.
- [x] Process: Validate existence + intelligibility using ui-a4y1.
- [x] Output: Valid voice input payload OR validation failure state.
- [x] Error: Empty/unintelligible → mapped shared error, prevent backend call.

---

## Test (`frontend/verifiers/__tests__/VoiceInputVerifier.test.ts`) [x]

### Reachability
- [x] Call `validateVoiceInput(validAudioBlob)`.
- [x] Assert returns `{ valid: true, payload }`.

### TypeInvariant
- [x] Assert payload type:
  ```ts
  type VoicePayload = { transcript: string; durationMs: number };
  ```

### ErrorConsistency
- [x] Call with:
  - empty transcript
  - transcript below intelligibility threshold
- [x] Assert returns:
  ```ts
  { valid: false, error: VoiceErrors.VOICE_INPUT_INVALID }
  ```
- [x] Assert no backend API contract invoked (mock `fetch`).

---

## Implementation [x]

### `frontend/verifiers/VoiceInputVerifier.ts`
```ts
import { VoiceErrors } from '@/shared/error_definitions/VoiceErrors';

export function validateVoiceInput(transcript: string, durationMs: number) {
  if (!transcript || transcript.trim().length < 3) {
    return { valid: false, error: VoiceErrors.VOICE_INPUT_INVALID };
  }

  return {
    valid: true,
    payload: { transcript, durationMs }
  };
}
```

In `ReviewScreen.tsx`:
- [x] On capture complete → call verifier.
- [x] If invalid → set validation failure state.
- [x] Do NOT call backend endpoint.

---

# Step 3: Display voice input processing error [x]

**From path spec:**
- [x] Input: Validation failure state + shared error.
- [x] Process: Render error message; reset voice capture mode.
- [x] Output: Error visible; original content unchanged.
- [x] Error: If render fails → fallback generic error; no navigation.

---

## Test (`frontend/components/review/__tests__/ReviewScreen.step3.test.tsx`) [x]

### Reachability
- [x] Simulate invalid voice input.
- [x] Assert error banner shows `VoiceErrors.VOICE_INPUT_INVALID.message`.
- [x] Assert `voiceMode === 'idle'`.

### TypeInvariant
- [x] Assert error object conforms to:
  ```ts
  type VoiceError = { code: string; message: string };
  ```

### ErrorConsistency
- [x] Mock error renderer to throw.
- [x] Assert fallback message equals `VoiceErrors.GENERIC_VOICE_ERROR.message`.
- [x] Assert still on review screen.

---

## Implementation [x]

In `ReviewScreen.tsx`:
- [x] Local state: `error: VoiceError | null`
- [x] On validation failure:
  - `setError(errorFromVerifier)`
  - `setVoiceSession({ ...session, status: 'idle' })`
- [x] Wrap error render in try/catch → fallback to `GENERIC_VOICE_ERROR`.

---

# Step 4: Maintain review screen state [x]

**From path spec:**
- [x] Input: Current review screen state with displayed error.
- [x] Process: Preserve generated content and review context.
- [x] Output: User remains on review screen with content intact.
- [x] Error: If unintended navigation/state mutation → restore snapshot.

---

## Test (`frontend/modules/review/__tests__/ReviewModule.step4.test.ts`) [x]

### Reachability
- [x] Initialize module with content "Draft v1".
- [x] Trigger voice error flow.
- [x] Assert content still "Draft v1".

### TypeInvariant
- [x] Assert state type:
  ```ts
  type ReviewState = {
    content: string;
    voiceSession: VoiceSession | null;
    error: VoiceError | null;
  };
  ```

### ErrorConsistency
- [x] Simulate unintended mutation.
- [x] Assert module restores previous snapshot.

---

## Implementation

In `ReviewModule.ts`:

- Add snapshot mechanism:
```ts
private lastStableState: ReviewState;

snapshot() {
  this.lastStableState = structuredClone(this.state);
}

restore() {
  this.state = structuredClone(this.lastStableState);
}
```

- On entering voice mode → snapshot.
- On mutation detection → restore.

---

# Terminal Condition [x]

## Integration Test [x]

**File:** `frontend/components/review/__tests__/voice-edit-no-input.integration.test.tsx`

### Scenario
- [x] Render review screen with generated draft.
- [x] Click "Edit by Voice".
- [x] Provide empty transcript.

### Assertions
- [x] Error message displayed: "Voice input could not be processed."
- [x] Review screen remains visible.
- [x] Original draft content unchanged.
- [x] Attempt counter increments.

---

# Feedback Loop Tests [x]

## Test: 3 consecutive failures [x]

- [x] Simulate 3 invalid attempts.
- [x] Assert attempts === 3.
- [x] Assert no automatic retry.
- [x] Assert same error message shown.

---

# References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/332-voice-edit-no-input-error-on-review-screen.md`
- Gate 2: Option 1 – Next.js + TypeScript + Vitest
- Resource registry entries: ui-v3n6, ui-w8p2, ui-a4y1, cfg-j9w2

---

## Validation Report

**Validated at**: 2026-03-01T19:05:00-05:00

### Implementation Status
✓ Phase 0: Verification (TLA+ model) — Passed (Reachability, TypeInvariant, ErrorConsistency)
✓ Step 1: Capture edit-by-voice action — Fully implemented
✓ Step 2: Collect and validate voice input — Fully implemented
✓ Step 3: Display voice input processing error — Fully implemented
✓ Step 4: Maintain review screen state — Fully implemented
✓ Terminal Condition: Integration test — Fully implemented
✓ Feedback Loop Tests: 3 consecutive failures — Fully implemented

Plan completion: **61/61 items checked (100%)**

### Automated Verification Results
✓ All path-332 tests pass: `npx vitest run` — **5 test files, 34 tests, 0 failures**
✓ TypeScript type check: `npx tsc --noEmit` — **No errors in path-332 files**
⚠ Lint (`npx eslint`): 4 warnings in ReviewScreen.tsx (unused destructured vars from other paths' props — `response`, `error`, `intent`, `session` at lines 49-53). These are non-blocking and relate to path 329/331 props, not path 332.
✓ No unrelated test file regression introduced by path-332 implementation

### Code Review Findings

#### Matches Plan:

- **VoiceErrors.ts** (`cfg-j9w2`): All three error codes (`VOICE_INIT_FAILED`, `VOICE_INPUT_INVALID`, `GENERIC_VOICE_ERROR`) present with exact messages matching plan specification. Dual export pattern: factory functions for backend + `VoiceInputErrors` lightweight constants for frontend.
- **VoiceInputVerifier.ts** (`ui-a4y1`): `validateVoiceInput(transcript, durationMs)` validates ≥3 chars after trim. Returns `{ valid: false, error: VoiceInputErrors.VOICE_INPUT_INVALID }` on failure, `{ valid: true, payload }` on success. No backend API invoked on invalid input.
- **ReviewModule.ts** (`ui-v3n6`): State shape `{ content, voiceSession, error }` with `VoiceSession { status, attempts }`. Snapshot/restore mechanism via `structuredClone` implemented: `snapshot()`, `restore()`, `guardState()`. Snapshot taken on entering voice mode. Content preserved through voice error flows.
- **ReviewScreen.tsx** (`ui-w8p2`): "Edit by Voice" button triggers `handleEditByVoice()` → `initializeVoiceSession()`. Try/catch on init → `VOICE_INIT_FAILED`. On validation failure → `setVoiceError(result.error)`, session reset to `{ status: 'idle', attempts: N+1 }`. `renderVoiceError()` wrapped in try/catch with `GENERIC_VOICE_ERROR` fallback.
- **Test coverage**: All TLA+ properties (Reachability, TypeInvariant, ErrorConsistency) verified across all 4 steps plus integration and feedback loop tests. Tests explicitly reference "Path 332" in their describe blocks.

#### Deviations from Plan:

1. **File path prefix**: Plan uses `shared/error_definitions/VoiceErrors.ts` and `frontend/modules/...` but actual files are under `frontend/src/server/error_definitions/` and `frontend/src/modules/`. This is a documentation-level discrepancy; the `@/` TypeScript path alias resolves correctly to `frontend/src/`.

2. **Method naming**: Plan specifies `ReviewModule.initializeVoiceSession(): VoiceSession`. Actual implementation splits this into `ReviewModule.startVoiceSession(): void` (state management + snapshot) and `ReviewScreen.initializeVoiceSession()` (private component helper that constructs the session and can throw for `VOICE_INIT_FAILED`). This is a deliberate architectural improvement — component owns the throw/catch path, module owns the state.

3. **Error state separation**: Plan describes a single `error: VoiceError | null`. Implementation uses `error: string | null` (for approval errors) + `voiceError: VoiceErrorDef | null` (for voice errors). Cleaner separation of concerns; both are properly typed.

4. **Transcript trimming**: Plan's pseudocode returns raw `transcript` in payload; implementation returns `transcript.trim()`. Tests explicitly assert this behavior, so it's intentional.

5. **`guardState()` method**: Not in plan. Added as an enhancement to `ReviewModule` for proactive mutation detection. Covered by tests.

All deviations are improvements or refinements — none compromise the plan's intent or the TLA+ property guarantees.

#### Issues Found:

- **No critical issues.** All core functionality works as specified.
- **Minor**: 4 ESLint warnings for unused destructured variables in ReviewScreen.tsx (lines 49-53). These belong to other paths' prop interfaces and are non-blocking.
- **Pre-existing**: TypeScript errors exist in `behavioralQuestionVerifier.test.ts` (unrelated to path 332 — missing vitest type declarations). Not introduced by this implementation.

### Manual Testing Required:
- [ ] Render ReviewScreen in the full app context (not just test environment)
- [ ] Click "Edit by Voice" and submit an empty input — verify error "Voice input could not be processed." appears
- [ ] Submit 3 consecutive empty inputs — verify error persists, no automatic retries, content unchanged
- [ ] Verify no network requests fire on invalid voice input (check browser DevTools Network tab)
- [ ] Test with voice initialization failure (if applicable to real audio API) — verify "Unable to start voice capture" error

### Recommendations:
- Consider adding vitest type declarations to `tsconfig.json` to resolve the pre-existing `behavioralQuestionVerifier.test.ts` TS errors (unrelated to path 332)
- The 4 ESLint unused-var warnings in ReviewScreen.tsx could be addressed with `_` prefixes for unused destructured props
- The `showVoiceCapture` prop default (`true`) is good for standalone use; verify that `ReviewWorkflowModule` passes `false` when rendering its own voice UI separately

VALIDATION_RESULT: PASS
