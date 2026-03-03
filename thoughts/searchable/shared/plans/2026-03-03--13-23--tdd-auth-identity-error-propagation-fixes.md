# Auth Identity and Error Propagation TDD Implementation Plan

## Overview
This plan implements the modeled fixes from:
- `specs/orchestration/auth-identity-error-propagation-model.md`
- `artifacts/tlaplus/auth-identity-error-propagation-model/AuthIdentityErrorPropagation.tla`
- `artifacts/tlaplus/auth-identity-error-propagation-model/AuthIdentityErrorPropagationModel.tla`

Goal: eliminate cross-user auth identity collisions and preserve `SESSION_ALREADY_ACTIVE` conflict semantics from service to client so URL/session initialization failures are actionable instead of generic 500s.

TDD rule for each behavior:
1. Write a failing test for one observable behavior.
2. Add the minimal implementation to make it pass.
3. Refactor while keeping tests green.

## Current State Analysis

### Key Discoveries
- Auth identity is currently derived from token prefix (`token.substring(0, 8)`), which collapses standard JWTs to the same value (`eyJhbGci`) at `frontend/src/server/filters/AuthAndValidationFilter.ts:36`.
- Pipeline adapter catches all errors and rewrites them to `PIPELINE_INIT_FAILED` 500 at `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts:52-55`.
- `PIPELINE_INIT_FAILED` is explicitly defined as HTTP 500 at `frontend/src/server/error_definitions/ChannelIngestionErrors.ts:53-54`.
- URL ingestion route handles `StoryError`, `VoiceUxError`, and `ChannelIngestionError`, but not `SessionError`, at `frontend/src/app/api/ingestion/url/route.ts:60-89`.
- Frontend URL contract currently throws generic `Error` for non-OK responses and does not emit typed conflict errors (`frontend/src/api_contracts/startSessionFromUrl.ts:40-47`).
- Existing URL route tests hardcode old identity behavior (`user-valid-to`) at `frontend/src/app/api/ingestion/url/__tests__/route.test.ts:60`.
- Multiple route tests seed state with the same substring-derived userId pattern, e.g.:
  - `frontend/src/app/api/acceleration/outreach/__tests__/route.test.ts:15,43`
  - `frontend/src/app/api/acceleration/contacts/__tests__/route.test.ts:14`
  - `frontend/src/app/api/acceleration/shortlist/__tests__/route.test.ts:14`
  - `frontend/src/app/api/acceleration/contribution/__tests__/route.test.ts:15,39`
  - `frontend/src/app/api/linkedin/drafts/__tests__/route.test.ts:14,39`
  - `frontend/src/app/api/onboarding/linkedin/connect/callback/__tests__/route.test.ts:16`

## Desired End State
- Distinct JWT users produce distinct backend `userId` values (INV-1).
- `SESSION_ALREADY_ACTIVE` conflicts are preserved through adapter and response layer as HTTP 409 (INV-2, INV-3).
- Client contract exposes typed conflict semantics so UI can render actionable guidance (INV-5).
- Existing auth-dependent route tests remain stable after identity derivation change.

### Observable Behaviors
1. Given two bearer tokens with distinct JWT `sub` values, when authenticated, then derived user IDs are distinct.
2. Given a `SessionError(SessionAlreadyActive)` from session initialization, when adapter handles it, then conflict metadata is preserved (`code: SESSION_ALREADY_ACTIVE`, `status: 409`).
3. Given adapter returns an active-session conflict, when `/api/ingestion/url` responds, then response is HTTP 409 with `SESSION_ALREADY_ACTIVE`.
4. Given `/api/ingestion/url` returns 409 + `SESSION_ALREADY_ACTIVE`, when `startSessionFromUrl()` handles it, then a typed conflict error is thrown (not generic error).
5. Given a typed conflict error in `StartVoiceSessionModule`, when rendered, then UI message is specific and actionable.
6. Given route tests seed per-user data, when identity derivation is updated, then tests derive user IDs through shared auth behavior instead of duplicate substring logic.

## What We're NOT Doing
- Full JWT signature verification or Supabase Auth integration (this remains a stub path).
- Redesigning session finalization UX flows beyond actionable conflict messaging.
- Changing unrelated ingestion dedupe logic for provider/canonical URL.

## Testing Strategy
- **Framework**: Vitest (`frontend/package.json`).
- **Test Types**:
  - Unit: auth derivation, adapter error mapping, API contract error typing.
  - Route integration: URL ingestion and channel ingestion status/code behavior.
  - UI module: session start error presentation.
  - Regression: auth-dependent route tests that currently depend on old substring identity convention.
- **Commands**:
  - `npm --prefix frontend run test -- src/server/filters/__tests__/AuthAndValidationFilter.authenticate.test.ts`
  - `npm --prefix frontend run test -- src/server/services/__tests__/ChannelIngestionPipelineAdapter.test.ts`
  - `npm --prefix frontend run test -- src/app/api/ingestion/url/__tests__/route.test.ts`
  - `npm --prefix frontend run test -- src/app/api/ingestion/channel/__tests__/route.test.ts`
  - `npm --prefix frontend run test -- src/api_contracts/__tests__/startSessionFromUrl.test.ts`
  - `npm --prefix frontend run test -- src/modules/session/__tests__/StartVoiceSessionModule.test.tsx`
  - `npm --prefix frontend run test`
  - `npm --prefix frontend run type-check`
  - `npm --prefix frontend run lint`

## Behavior 1: Derive Unique Auth Identity from Bearer Token

### Test Specification
**Given**: JWT bearer tokens with different `sub` claims.
**When**: `AuthAndValidationFilter.authenticate()` is called.
**Then**: returned `userId` values are distinct and deterministic.

**Edge Cases**:
- Missing/empty auth header still returns `UNAUTHORIZED` 401.
- Malformed/non-JWT token falls back to deterministic full-token hash, not prefix substring.
- Same token always maps to same `userId`.

### TDD Cycle

#### Red: Write Failing Test
**Files**:
- `frontend/src/server/filters/__tests__/AuthAndValidationFilter.authenticate.test.ts` (new)

```ts
it('derives userId from JWT sub claim when present', () => {
  // tokenA.sub !== tokenB.sub -> userIdA !== userIdB
});

it('falls back to deterministic hash for non-JWT token', () => {
  // same token -> same userId
  // different token -> different userId
});
```

#### Green: Minimal Implementation
**File**:
- `frontend/src/server/filters/AuthAndValidationFilter.ts`

```ts
// 1) Parse token payload if JWT-like and use `sub`.
// 2) Else derive hash from full token.
// 3) Return `user-${derived}`.
```

#### Refactor: Improve Code
**Files**:
- `frontend/src/server/filters/AuthAndValidationFilter.ts`

```ts
// Extract small helpers:
// - tryDecodeJwtSub(token)
// - deriveDeterministicUserId(token)
```

### Success Criteria
**Automated:**
- [x] New auth filter tests fail first on current substring behavior.
- [x] All auth filter tests pass with new derivation.
- [x] Existing unauthorized tests remain green.

**Manual:**
- [ ] Distinct production JWT users no longer collapse to one derived user identity.

---

## Behavior 2: Preserve Session Conflict Metadata in Pipeline Adapter

### Test Specification
**Given**: `InitializeSessionService.createSession()` throws `SessionErrors.SessionAlreadyActive()`.
**When**: `ChannelIngestionPipelineAdapter.initializeFromUrl()` catches it.
**Then**: adapter emits conflict semantics (`SESSION_ALREADY_ACTIVE`, 409) instead of `PIPELINE_INIT_FAILED` 500.

**Edge Cases**:
- Unknown errors are still wrapped as `PIPELINE_INIT_FAILED` 500.
- Success path payload remains unchanged.

### TDD Cycle

#### Red: Write Failing Test
**File**:
- `frontend/src/server/services/__tests__/ChannelIngestionPipelineAdapter.test.ts`

```ts
it('preserves SESSION_ALREADY_ACTIVE as 409 conflict', async () => {
  // mock createSession reject SessionErrors.SessionAlreadyActive()
  // expect ChannelIngestionError with code SESSION_ALREADY_ACTIVE statusCode 409
});

it('keeps unknown errors mapped to PIPELINE_INIT_FAILED 500', async () => {
  // mock createSession reject new Error(...)
});
```

#### Green: Minimal Implementation
**Files**:
- `frontend/src/server/error_definitions/ChannelIngestionErrors.ts`
- `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts`

```ts
// Add ChannelIngestion error variant for SESSION_ALREADY_ACTIVE (409).
// In adapter catch:
// if SessionError.code === 'SESSION_ALREADY_ACTIVE' -> throw conflict ChannelIngestionError
// else keep existing PipelineInitFailed mapping.
```

#### Refactor: Improve Code
**File**:
- `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts`

```ts
// Extract mapInitializationError(error) helper for deterministic mapping.
```

### Success Criteria
**Automated:**
- [x] Adapter conflict-preservation test fails first then passes.
- [x] Adapter unknown-error mapping test remains green.

**Manual:**
- [ ] Live adapter no longer rewrites active-session conflicts to generic 500.

---

## Behavior 3: Route Returns 409 Conflict for Active Session (URL + Channel)

### Test Specification
**Given**: adapter emits `SESSION_ALREADY_ACTIVE` conflict.
**When**: `/api/ingestion/url` or `/api/ingestion/channel` handles the error.
**Then**: response is HTTP 409 with code `SESSION_ALREADY_ACTIVE`.

**Edge Cases**:
- Existing 401/400/404 handling remains unchanged.
- Unknown exceptions still return internal error.

### TDD Cycle

#### Red: Write Failing Test
**Files**:
- `frontend/src/app/api/ingestion/url/__tests__/route.test.ts`
- `frontend/src/app/api/ingestion/channel/__tests__/route.test.ts`

```ts
it('returns 409 SESSION_ALREADY_ACTIVE when adapter reports active conflict', async () => {
  // mock adapter initializeFromUrl reject conflict ChannelIngestionError
});
```

#### Green: Minimal Implementation
**Files**:
- `frontend/src/app/api/ingestion/url/route.ts`
- `frontend/src/app/api/ingestion/channel/route.ts` (likely no code change if adapter emits ChannelIngestionError)

```ts
// Keep route catch blocks authoritative for ChannelIngestionError status/code.
// Only add handling if needed by final adapter mapping approach.
```

#### Refactor: Improve Code
**Files**:
- `frontend/src/app/api/ingestion/url/route.ts`
- `frontend/src/app/api/ingestion/channel/route.ts`

```ts
// Consolidate repeated error response mapping shape if duplication grows.
```

### Success Criteria
**Automated:**
- [x] URL route test for 409 conflict fails first then passes.
- [x] Channel route regression test confirms no fallback 500 regression.

**Manual:**
- [ ] Browser network response for URL ingestion conflict is 409 with structured code.

---

## Behavior 4: Typed Conflict Error in URL API Contract

### Test Specification
**Given**: `startSessionFromUrl()` receives HTTP 409 with `{ code: 'SESSION_ALREADY_ACTIVE', message }`.
**When**: client contract handles response.
**Then**: it throws a typed conflict error (not generic `Error`).

**Edge Cases**:
- Non-409 errors remain generic.
- Invalid error payload still falls back to status-based generic error.

### TDD Cycle

#### Red: Write Failing Test
**File**:
- `frontend/src/api_contracts/__tests__/startSessionFromUrl.test.ts`

```ts
it('throws SessionAlreadyActiveError for 409 SESSION_ALREADY_ACTIVE', async () => {
  // mock fetch 409 + code
  // expect typed error class with statusCode 409
});
```

#### Green: Minimal Implementation
**File**:
- `frontend/src/api_contracts/startSessionFromUrl.ts`

```ts
export class StartSessionAlreadyActiveError extends Error { ... }

if (response.status === 409 && errorBody.code === 'SESSION_ALREADY_ACTIVE') {
  throw new StartSessionAlreadyActiveError(errorBody.message)
}
```

#### Refactor: Improve Code
**File**:
- `frontend/src/api_contracts/startSessionFromUrl.ts`

```ts
// Align error-contract pattern with initializeSession.ts to keep consistency.
```

### Success Criteria
**Automated:**
- [x] Typed-conflict contract test fails first then passes.
- [x] Existing contract tests remain green.

**Manual:**
- [ ] Error telemetry still logs correct context while preserving typed client behavior.

---

## Behavior 5: UI Shows Actionable Conflict Message

### Test Specification
**Given**: `StartVoiceSessionModule` receives typed conflict error from `startSessionFromUrl()`.
**When**: user starts session and conflict occurs.
**Then**: module displays explicit guidance about finalizing/ending active session.

**Edge Cases**:
- Generic errors still display fallback message.
- Unauthenticated flow remains unchanged.

### TDD Cycle

#### Red: Write Failing Test
**File**:
- `frontend/src/modules/session/__tests__/StartVoiceSessionModule.test.tsx`

```tsx
it('shows actionable message on active session conflict', async () => {
  // mock startSessionFromUrl reject StartSessionAlreadyActiveError
  // expect alert message includes finalize/end current session guidance
});
```

#### Green: Minimal Implementation
**File**:
- `frontend/src/modules/session/StartVoiceSessionModule.tsx`

```ts
// In catch block, branch on StartSessionAlreadyActiveError and set specific message.
```

#### Refactor: Improve Code
**File**:
- `frontend/src/modules/session/StartVoiceSessionModule.tsx`

```ts
// Extract mapStartSessionErrorToUiMessage(err) for deterministic testing.
```

### Success Criteria
**Automated:**
- [x] UI conflict-message test fails first then passes.
- [x] Existing module tests remain green.

**Manual:**
- [ ] User sees actionable resolution guidance instead of generic failure text.

---

## Behavior 6: Stabilize Auth-Dependent Test Fixtures

### Test Specification
**Given**: tests that pre-seed data by derived `userId`.
**When**: auth derivation changes.
**Then**: tests still pass by deriving IDs through shared auth behavior rather than duplicated substring logic.

**Edge Cases**:
- Cross-user forbiddance tests still use distinct tokens and still fail correctly for access violations.

### TDD Cycle

#### Red: Write Failing Test
**Files (expected to fail once Behavior 1 lands):**
- `frontend/src/app/api/acceleration/outreach/__tests__/route.test.ts`
- `frontend/src/app/api/acceleration/contacts/__tests__/route.test.ts`
- `frontend/src/app/api/acceleration/shortlist/__tests__/route.test.ts`
- `frontend/src/app/api/acceleration/contribution/__tests__/route.test.ts`
- `frontend/src/app/api/linkedin/drafts/__tests__/route.test.ts`
- `frontend/src/app/api/onboarding/linkedin/connect/callback/__tests__/route.test.ts`
- `frontend/src/app/api/ingestion/url/__tests__/route.test.ts`

#### Green: Minimal Implementation
**Files**:
- Same test files above.

```ts
// Replace manual `user-${token.substring(0, 8)}` with shared derivation via
// AuthAndValidationFilter.authenticate(`Bearer ${token}`).userId
// (or exported helper if introduced in Behavior 1 refactor).
```

#### Refactor: Improve Code
**Files**:
- Potential new test helper, e.g. `frontend/src/test_helpers/authTestUtils.ts`

```ts
// createDerivedUserIdForToken(token) to remove repeated setup logic.
```

### Success Criteria
**Automated:**
- [x] Previously brittle route tests fail under new derivation then pass after fixture updates.
- [x] Cross-user authorization regression checks remain valid.

**Manual:**
- [x] No hidden dependence remains on token-prefix identity convention.

## Integration and Regression Suite
- Run behaviors in strict order: 1 → 2 → 3 → 4 → 5 → 6.
- After each behavior: run only touched tests.
- Final gate:
  - `npm --prefix frontend run test`
  - `npm --prefix frontend run type-check`
  - `npm --prefix frontend run lint`

## References
- `specs/orchestration/auth-identity-error-propagation-model.md`
- `artifacts/tlaplus/auth-identity-error-propagation-model/AuthIdentityErrorPropagation.tla`
- `artifacts/tlaplus/auth-identity-error-propagation-model/AuthIdentityErrorPropagationModel.tla`
- `frontend/src/server/filters/AuthAndValidationFilter.ts`
- `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts`
- `frontend/src/server/error_definitions/ChannelIngestionErrors.ts`
- `frontend/src/app/api/ingestion/url/route.ts`
- `frontend/src/app/api/ingestion/channel/route.ts`
- `frontend/src/api_contracts/startSessionFromUrl.ts`
- `frontend/src/modules/session/StartVoiceSessionModule.tsx`
