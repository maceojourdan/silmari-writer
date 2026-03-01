# enforce-affirmative-consent-before-voice-session TDD Plan

Path spec: `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/302-enforce-affirmative-consent-before-voice-session.md`

---

## Verification (Phase 0)

The TLA+ model for this path passed the following properties:

- Reachability
- TypeInvariant
- ErrorConsistency

Command:

```bash
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/302-enforce-affirmative-consent-before-voice-session.md
```

Verification output:

- Result: **ALL PROPERTIES PASSED**
- States: 26 found, 13 distinct
- Exit code: 0

This guarantees at the model level:
- Every step from trigger → terminal is reachable.
- Input/output types are consistent at each boundary.
- All defined error branches lead to valid error states.

The following TDD plan mirrors those guarantees at the code level.

---

## Tech Stack (Gate 2 – Option 1)

- Frontend: Next.js (App Router), React, TypeScript, Vitest + React Testing Library
- Backend: Next.js API Routes (Node.js, TypeScript, Zod)
- Database: Supabase (Postgres)

---

## Resource Mapping

| UUID | Registry Name | Concrete Implementation |
|------|--------------|------------------------|
| ui-w8p2 | component | `frontend/components/VoiceSessionStart.tsx` |
| ui-a4y1 | frontend_verifier | `frontend/verifiers/consentVerifier.ts` |
| api-q7v1 | frontend_api_contract | `frontend/api_contracts/startVoiceSession.ts` |
| api-m5g7 | endpoint | `frontend/app/api/voice-session/start/route.ts` |
| api-n8k2 | request_handler | `backend/request_handlers/StartVoiceSessionHandler.ts` |
| db-h2s4 | service | `backend/services/VoiceSessionService.ts` |
| cfg-j9w2 | shared_error_definitions | `shared/error_definitions/ConsentErrors.ts` |
| cfg-q9c5 | backend_logging | `backend/logging/index.ts` |
| cfg-r3d7 | frontend_logging | `frontend/logging/index.ts` |

---

## Step 1: Initiate Voice Session Request ✅

**From path spec:**
- Input: User interaction event from frontend component (ui-w8p2)
- Process: Transition UI state to display consent prompt instead of starting session
- Output: Consent prompt rendered with affirmative/negative options
- Error: If component fails to render → log via cfg-r3d7 and show generic UI error

### Test
`frontend/src/components/__tests__/VoiceSessionStart.step1.test.tsx` ✅ (6 tests)

- [x] Reachability: simulate click on "Start Voice Session" → assert consent prompt appears
- [x] TypeInvariant: assert prompt state is `{ consentRequired: boolean }`
- [x] ErrorConsistency: mock render failure → assert `frontend_logging.error` called and generic error displayed

### Implementation
`frontend/src/components/VoiceSessionStart.tsx` ✅

- [x] Local state: `uiState = 'idle' | 'consent_prompt' | 'blocked' | 'loading' | 'active' | 'error'`
- [x] On click → set state to `consent_prompt`
- [x] Error handling with frontend logging

---

## Step 2: Capture Consent Response ✅

**From path spec:**
- Input: User response (affirmative or non-affirmative)
- Process: Evaluate explicitly affirmative; block otherwise
- Output: Affirmative consent flag OR blocked state with message
- Error: Undefined/malformed response → apply ui-a4y1 verifier and redisplay with validation feedback

### Test
`frontend/src/components/__tests__/VoiceSessionStart.step2.test.tsx` ✅ (4 tests)
`frontend/src/verifiers/__tests__/consentVerifier.test.ts` ✅ (12 tests)

- [x] Reachability: select "I agree" → expect `consentFlag === true`
- [x] TypeInvariant: consentFlag is boolean
- [x] ErrorConsistency:
  - [x] Select "Decline" → assert blocked state message shown
  - [x] Pass undefined → verifier rejects, returns false

### Implementation
- [x] `frontend/src/verifiers/consentVerifier.ts` — `isExplicitlyAffirmative(input: string): boolean`
- [x] Component uses verifier before setting `consentFlag`
- [x] Track failed attempts (max 3) in local state

---

## Step 3: Submit Session Start with Consent Flag ✅

**From path spec:**
- Input: Affirmative consent flag via api-q7v1
- Process: Package and send HTTP request
- Output: HTTP POST to api-m5g7 with consent indicator
- Error: Network failure → retry (max 2), log via cfg-r3d7

### Test
`frontend/src/api_contracts/__tests__/startVoiceSession.test.ts` ✅ (14 tests)

- [x] Reachability: call contract with `{ consent: true }` → assert fetch called with correct payload
- [x] TypeInvariant: payload validated via Zod schema (`z.literal(true)`)
- [x] ErrorConsistency:
  - [x] Mock network failure once → retry succeeds on second attempt
  - [x] Mock network failure 3× → throw after max retries, log via frontendLogger

### Implementation
- [x] `frontend/src/api_contracts/startVoiceSession.ts`
  - [x] Zod schema: `{ consent: z.literal(true) }`
- [x] Exponential retry (max 2 retries) on TypeError
- [x] Logging via `frontend/logging`

---

## Step 4: Validate Consent on Backend ✅

**From path spec:**
- Input: Request received by api-n8k2
- Process: Backend verifies affirmative consent flag
- Output: Authorization to proceed OR consent-required error
- Error: Missing/false → return shared error (cfg-j9w2)

### Test
`frontend/src/server/services/__tests__/VoiceSessionService.test.ts` ✅ (6 tests)

- [x] Reachability: pass `{ consent: true }` → expect `authorized: true`
- [x] TypeInvariant: response matches `ConsentValidationResult`
- [x] ErrorConsistency:
  - [x] `{ consent: false }` → expect `CONSENT_REQUIRED` error code
  - [x] Missing consent → same error
  - [x] String "true" → same error (strict boolean check)

### Implementation
- [x] `frontend/src/server/error_definitions/ConsentErrors.ts` — `CONSENT_REQUIRED` error definition
- [x] `frontend/src/server/services/VoiceSessionService.ts` — `validateConsent(payload)`
- [x] Handler bridges endpoint → service

---

## Step 5: Enforce Block and Return Response ✅

**From path spec:**
- Input: Backend validation result
- Process: Halt session creation if invalid; proceed if valid
- Output: Success OR structured consent-required error
- Error: Unexpected failure → log via cfg-q9c5 and return generic failure

### Test
`frontend/src/server/request_handlers/__tests__/StartVoiceSessionHandler.test.ts` ✅ (4 tests)
`frontend/src/app/api/voice-session/start/__tests__/route.test.ts` ✅ (6 tests)

- [x] Reachability: valid consent → 200 response `{ sessionStatus: 'INIT' }`
- [x] TypeInvariant: response conforms to API contract
- [x] ErrorConsistency:
  - [x] Consent invalid → 400 with CONSENT_REQUIRED
  - [x] Simulated service exception → 500 + backend log called

### Implementation
- [x] `frontend/src/server/request_handlers/StartVoiceSessionHandler.ts` — handler with error wrapping
- [x] `frontend/src/app/api/voice-session/start/route.ts` — POST handler
- [x] Try/catch → log unexpected errors via `backend/logging`

---

## Step 6: Render Final User State ✅

**From path spec:**
- Input: Backend response
- Process: Activate session only if approved
- Output: UI shows inactive session with consent-required message if blocked
- Error: Response parsing fails → log via cfg-r3d7

### Test
`frontend/src/components/__tests__/VoiceSessionStart.step6.test.tsx` ✅ (5 tests)

- [x] Reachability: mock success → voice session active UI rendered
- [x] TypeInvariant: response parsed via typed contract
- [x] ErrorConsistency:
  - [x] Mock CONSENT_REQUIRED → session inactive + visible message
  - [x] Mock malformed response → log + fallback error notification
  - [x] Mock network failure → error displayed + frontendLogger called

### Implementation
- [x] Component handles API response state: `uiState = 'idle' | 'consent_prompt' | 'blocked' | 'loading' | 'active' | 'error'`
- [x] Error boundary for parse failures via try/catch + frontendLogger

---

## Feedback Loop (Max 3 Attempts) ✅

### Test
`frontend/src/components/__tests__/VoiceSessionStart.feedback.test.tsx` ✅ (5 tests)

- [x] Provide 3 non-affirmative responses → session reset to initial state
- [x] Allow retry after 1st and 2nd decline
- [x] No API calls during decline flow
- [x] Succeed if user agrees on 2nd attempt

### Implementation
- [x] Maintain `attemptCount` in component state
- [x] After 3 → reset to `idle`

---

## Terminal Condition ✅

### Integration Test
`frontend/src/server/__tests__/enforceConsent.integration.test.ts` ✅ (14 tests)

Exercise full flow:

1. [x] Click Start Voice Session
2. [x] Decline consent
3. [x] Assert:
   - [x] No API request made
   - [x] Session inactive
   - [x] Visible message: "Affirmative consent is required before starting voice session"

Also tested:
- [x] Accept consent → 200 response → session transitions to INIT
- [x] Unexpected errors wrapped in GenericError + logged

This proves:
- [x] Reachability (trigger → terminal exercised)
- [x] TypeInvariant (typed contract + Zod schemas)
- [x] ErrorConsistency (all defined errors return correct states)

---

## References

- `/home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/302-enforce-affirmative-consent-before-voice-session.md`
- `SEC-CONSENT` requirement
- Gate 2 Option 1 tech stack
