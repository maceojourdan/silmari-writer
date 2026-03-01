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

# Step 1: Capture edit-by-voice action

**From path spec:**
- Input: User interaction event from review screen component (ui-w8p2, ui-v3n6).
- Process: Detect 'Edit by Voice' and transition UI into voice capture mode.
- Output: Voice capture session initialized within review screen context.
- Error: If initialization fails, display shared error (cfg-j9w2) and remain on review screen.

---

## Test (`frontend/components/review/__tests__/ReviewScreen.step1.test.tsx`)

### Reachability
- Render `ReviewScreen` with mock `ReviewModule` state.
- Click "Edit by Voice" button.
- Assert `voiceMode === 'capturing'`.

### TypeInvariant
- Assert voice session object matches type:
  ```ts
  type VoiceSession = {
    status: 'capturing' | 'idle' | 'error';
    attempts: number;
  }
  ```
- Assert returned session object conforms.

### ErrorConsistency
- Mock `initializeVoiceSession()` to throw.
- Click button.
- Assert error banner rendered with `VoiceErrors.VOICE_INIT_FAILED.code`.
- Assert still on review screen (no navigation).

---

## Implementation

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

# Step 2: Collect and preliminarily validate voice input

**From path spec:**
- Input: Audio stream or empty/unintelligible audio.
- Process: Validate existence + intelligibility using ui-a4y1.
- Output: Valid voice input payload OR validation failure state.
- Error: Empty/unintelligible → mapped shared error, prevent backend call.

---

## Test (`frontend/verifiers/__tests__/VoiceInputVerifier.test.ts`)

### Reachability
- Call `validateVoiceInput(validAudioBlob)`.
- Assert returns `{ valid: true, payload }`.

### TypeInvariant
- Assert payload type:
  ```ts
  type VoicePayload = { transcript: string; durationMs: number };
  ```

### ErrorConsistency
- Call with:
  - empty transcript
  - transcript below intelligibility threshold
- Assert returns:
  ```ts
  { valid: false, error: VoiceErrors.VOICE_INPUT_INVALID }
  ```
- Assert no backend API contract invoked (mock `fetch`).

---

## Implementation

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
- On capture complete → call verifier.
- If invalid → set validation failure state.
- Do NOT call backend endpoint.

---

# Step 3: Display voice input processing error

**From path spec:**
- Input: Validation failure state + shared error.
- Process: Render error message; reset voice capture mode.
- Output: Error visible; original content unchanged.
- Error: If render fails → fallback generic error; no navigation.

---

## Test (`frontend/components/review/__tests__/ReviewScreen.step3.test.tsx`)

### Reachability
- Simulate invalid voice input.
- Assert error banner shows `VoiceErrors.VOICE_INPUT_INVALID.message`.
- Assert `voiceMode === 'idle'`.

### TypeInvariant
- Assert error object conforms to:
  ```ts
  type VoiceError = { code: string; message: string };
  ```

### ErrorConsistency
- Mock error renderer to throw.
- Assert fallback message equals `VoiceErrors.GENERIC_VOICE_ERROR.message`.
- Assert still on review screen.

---

## Implementation

In `ReviewScreen.tsx`:
- Local state: `error: VoiceError | null`
- On validation failure:
  - `setError(errorFromVerifier)`
  - `setVoiceSession({ ...session, status: 'idle' })`
- Wrap error render in try/catch → fallback to `GENERIC_VOICE_ERROR`.

---

# Step 4: Maintain review screen state

**From path spec:**
- Input: Current review screen state with displayed error.
- Process: Preserve generated content and review context.
- Output: User remains on review screen with content intact.
- Error: If unintended navigation/state mutation → restore snapshot.

---

## Test (`frontend/modules/review/__tests__/ReviewModule.step4.test.ts`)

### Reachability
- Initialize module with content "Draft v1".
- Trigger voice error flow.
- Assert content still "Draft v1".

### TypeInvariant
- Assert state type:
  ```ts
  type ReviewState = {
    content: string;
    voiceSession: VoiceSession | null;
    error: VoiceError | null;
  };
  ```

### ErrorConsistency
- Simulate unintended mutation.
- Assert module restores previous snapshot.

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

# Terminal Condition

## Integration Test

**File:** `frontend/components/review/__tests__/voice-edit-no-input.integration.test.tsx`

### Scenario
- Render review screen with generated draft.
- Click "Edit by Voice".
- Provide empty transcript.

### Assertions
- Error message displayed: "Voice input could not be processed."
- Review screen remains visible.
- Original draft content unchanged.
- Attempt counter increments.

---

# Feedback Loop Tests

## Test: 3 consecutive failures

- Simulate 3 invalid attempts.
- Assert attempts === 3.
- Assert no automatic retry.
- Assert same error message shown.

---

# References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/332-voice-edit-no-input-error-on-review-screen.md`
- Gate 2: Option 1 – Next.js + TypeScript + Vitest
- Resource registry entries: ui-v3n6, ui-w8p2, ui-a4y1, cfg-j9w2
