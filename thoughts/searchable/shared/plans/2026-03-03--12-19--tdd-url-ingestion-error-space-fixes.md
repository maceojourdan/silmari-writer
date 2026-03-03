# URL Ingestion Error Space (INV-1 to INV-5) TDD Implementation Plan

## Overview
This plan implements the modeled fixes from:
- `specs/orchestration/url-ingestion-error-space-model.md`
- `artifacts/tlaplus/url-ingestion-error-space-model/UrlIngestionErrorSpaceModel.tla`

Goal: make URL ingestion resilient by removing the persist/read mismatch (`updated_at` null), scoping active-session uniqueness by user, and superseding stale initialized sessions so retries converge.

TDD rule for every slice:
1. Write a failing test for one observable behavior.
2. Add minimal implementation to make it pass.
3. Refactor without changing behavior.

## Current State Analysis

### Key Discoveries
- URL ingestion uses authenticated user context and calls the channel adapter from [`frontend/src/app/api/ingestion/url/route.ts:41`](/home/maceo/Dev/silmari-writer/frontend/src/app/api/ingestion/url/route.ts:41).
- Adapter currently does not pass `userId` into `InitializeSessionService.createSession` input object, so session creation has no user identity for uniqueness scoping in [`frontend/src/server/services/ChannelIngestionPipelineAdapter.ts:26`](/home/maceo/Dev/silmari-writer/frontend/src/server/services/ChannelIngestionPipelineAdapter.ts:26).
- Service uniqueness check is global because DAO call has no user parameter in [`frontend/src/server/services/InitializeSessionService.ts:109`](/home/maceo/Dev/silmari-writer/frontend/src/server/services/InitializeSessionService.ts:109).
- DAO active-session query is global (`state = initialized` only) in [`frontend/src/server/data_access_objects/InitializeSessionDAO.ts:42`](/home/maceo/Dev/silmari-writer/frontend/src/server/data_access_objects/InitializeSessionDAO.ts:42).
- DAO insert omits both `updated_at` and `user_id` in [`frontend/src/server/data_access_objects/InitializeSessionDAO.ts:86`](/home/maceo/Dev/silmari-writer/frontend/src/server/data_access_objects/InitializeSessionDAO.ts:86).
- Base `sessions` schema allows `updated_at` null and has no `user_id` column in [`supabase/migrations/20260302000000_initial_schema.sql:45`](/home/maceo/Dev/silmari-writer/supabase/migrations/20260302000000_initial_schema.sql:45).
- Session read mapping assumes non-null timestamp (`data.updated_at as string`) in [`frontend/src/server/data_access_objects/SessionDAO.ts:67`](/home/maceo/Dev/silmari-writer/frontend/src/server/data_access_objects/SessionDAO.ts:67).
- API response contract currently requires non-null `updatedAt` in [`frontend/src/server/data_structures/SessionView.ts:13`](/home/maceo/Dev/silmari-writer/frontend/src/server/data_structures/SessionView.ts:13).
- Existing tests encode global duplicate rejection behavior (not user-scoped) in [`frontend/src/server/services/__tests__/InitializeSessionService.checkActive.test.ts:119`](/home/maceo/Dev/silmari-writer/frontend/src/server/services/__tests__/InitializeSessionService.checkActive.test.ts:119) and [`frontend/src/server/__tests__/rejectDuplicateSession.integration.test.ts:106`](/home/maceo/Dev/silmari-writer/frontend/src/server/__tests__/rejectDuplicateSession.integration.test.ts:106).

## Desired End State
- Every newly persisted `sessions` row has non-null `updated_at` at insert time.
- GET `/api/sessions/[id]` cannot fail solely due to legacy null `updated_at` rows.
- Active initialized-session uniqueness is enforced per user, not globally.
- Retry after stale initialized session converges by superseding stale row and creating a fresh one.

### Observable Behaviors
1. Given URL ingestion persists a new session, when insert completes, then `updated_at` is populated and readable.
2. Given a legacy session row with `updated_at = null`, when `/api/sessions/[id]` responds, then response schema accepts and returns a valid payload.
3. Given user A has an initialized session, when user B ingests a URL, then user B is not blocked by user A.
4. Given a same-user initialized session newer than threshold, when ingesting another URL, then request is rejected with `SESSION_ALREADY_ACTIVE`.
5. Given a same-user initialized session older than threshold, when ingesting another URL, then stale session is superseded and new session is created.

## What We're NOT Doing
- Reworking the channel ingestion dedupe/reply flow already implemented in [`frontend/src/app/api/ingestion/channel/route.ts:33`](/home/maceo/Dev/silmari-writer/frontend/src/app/api/ingestion/channel/route.ts:33).
- Altering answer-session (`answer_sessions`) lifecycle paths.
- Implementing new analytics/event contracts (INV-6 remains separate follow-up).

## Testing Strategy
- Framework: Vitest.
- Test types:
  - Unit: DAO payload/query behavior, schema guards, stale-age logic.
  - Integration: service + route behavior through existing URL ingestion entrypoint.
  - Migration validation: SQL presence checks for `sessions.user_id` and supporting index/constraints.
- Commands:
  - `npm --prefix frontend run test -- src/server/data_access_objects/__tests__/InitializeSessionDAO.test.ts`
  - `npm --prefix frontend run test -- src/server/services/__tests__/InitializeSessionService.checkActive.test.ts`
  - `npm --prefix frontend run test -- src/app/api/ingestion/url/__tests__/route.test.ts`
  - `npm --prefix frontend run test -- src/app/api/sessions/[id]/__tests__/route.get.test.ts`
  - `npm --prefix frontend run test -- src/server/data_access_objects/__tests__/migration.validation.test.ts`
  - `npm --prefix frontend run test`
  - `npm --prefix frontend run type-check`
  - `npm --prefix frontend run lint`

## Behavior 1: Persist `updated_at` at Session Creation (Fix 1)

### Test Specification
Given a valid initialized session payload, when `InitializeSessionDAO.persist` inserts the row, then the insert payload includes `updated_at` and persisted data maps cleanly.

Edge cases: Supabase insert failure still maps to `PERSISTENCE_FAILURE`.

### TDD Cycle

#### Red: Write Failing Test
File: `frontend/src/server/data_access_objects/__tests__/InitializeSessionDAO.test.ts`
```ts
it('includes updated_at in insert payload for new initialized session', async () => {
  // Arrange supabase insert chain
  // Act InitializeSessionDAO.persist(...)
  // Assert insert called with created_at and updated_at
});
```

#### Green: Minimal Implementation
File: `frontend/src/server/data_access_objects/InitializeSessionDAO.ts`
```ts
.insert({
  resume: session.resume,
  job: session.job,
  question: session.question,
  state: session.state,
  created_at: session.createdAt,
  updated_at: session.createdAt,
})
```

#### Refactor: Improve Code
File: `frontend/src/server/data_access_objects/InitializeSessionDAO.ts`
```ts
// Extract a private helper for insert payload construction to avoid field drift.
```

### Success Criteria
Automated:
- [x] New test fails before implementation for missing `updated_at`.
- [x] DAO tests pass after implementation.
- [x] No regressions in existing DAO error tests.

Manual:
- [ ] Verified DB row shows non-null `updated_at` immediately after URL ingestion.

---

## Behavior 2: Defensive Session Read for Legacy Null `updated_at` (Fix 2 + fallback)

### Test Specification
Given a session row with `updated_at = null`, when session is mapped and returned through GET `/api/sessions/[id]`, then payload remains schema-valid and endpoint returns 200.

Edge cases: preserve behavior for rows that already have non-null `updated_at`.

### TDD Cycle

#### Red: Write Failing Test
Files:
- `frontend/src/server/data_access_objects/__tests__/SessionDAO.wiring.test.ts`
- `frontend/src/app/api/sessions/[id]/__tests__/route.get.test.ts`
- `frontend/src/server/data_structures/__tests__/SessionView.test.ts` (new)

```ts
it('falls back to created_at when sessions.updated_at is null', async () => {
  // mock row updated_at: null
  // expect mapped.updatedAt === created_at
});

it('SessionView schema accepts null updatedAt for defense in depth', () => {
  // safeParse({ updatedAt: null, ... }) === true
});
```

#### Green: Minimal Implementation
Files:
- `frontend/src/server/data_access_objects/SessionDAO.ts`
- `frontend/src/server/data_structures/SessionView.ts`

```ts
updatedAt: (data.updated_at ?? data.created_at) as string,
```

```ts
updatedAt: z.string().nullable(),
```

#### Refactor: Improve Code
File: `frontend/src/server/data_access_objects/SessionDAO.ts`
```ts
// Reuse a tiny normalizeTimestamp helper across mapping paths where legacy nulls can appear.
```

### Success Criteria
Automated:
- [x] New legacy-null tests fail first, then pass.
- [x] Route test verifies 200 response path for nullable `updatedAt` payload.

Manual:
- [ ] Existing session IDs created before fix load without 500.

---

## Behavior 3: User-Scoped Active Session Uniqueness (Fix 3)

### Test Specification
Given active initialized session for user A, when user B initializes via URL ingestion, then user B succeeds. Given same user has fresh initialized session, second attempt is rejected with `SESSION_ALREADY_ACTIVE`.

Edge cases: keep existing error mapping (409 for same-user fresh conflict).

### TDD Cycle

#### Red: Write Failing Test
Files:
- `frontend/src/server/services/__tests__/InitializeSessionService.checkActive.test.ts`
- `frontend/src/server/services/__tests__/ChannelIngestionPipelineAdapter.test.ts`
- `frontend/src/server/data_access_objects/__tests__/InitializeSessionDAO.test.ts`
- `frontend/src/server/data_access_objects/__tests__/migration.validation.test.ts`

```ts
it('queries active initialized session by user_id', async () => {
  // expect getActiveSession called with userId
  // expect DAO query includes .eq('user_id', userId)
});

it('passes userId from ingestion adapter into createSession input', async () => {
  // expect createSession called with { ..., userId }
});
```

#### Green: Minimal Implementation
Files:
- `supabase/migrations/<new>_sessions_user_scope.sql`
- `frontend/src/server/services/InitializeSessionService.ts`
- `frontend/src/server/data_access_objects/InitializeSessionDAO.ts`
- `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts`

```sql
ALTER TABLE sessions ADD COLUMN IF NOT EXISTS user_id text;
CREATE INDEX IF NOT EXISTS idx_sessions_user_state ON sessions(user_id, state);
```

```ts
// service input adds userId
const activeSession = await InitializeSessionDAO.getActiveSession(input.userId);
```

```ts
// DAO query scopes by state + user_id and insert stores user_id
.eq('state', 'initialized').eq('user_id', userId)
```

#### Refactor: Improve Code
Files:
- `frontend/src/server/services/InitializeSessionService.ts`
- `frontend/src/server/data_access_objects/InitializeSessionDAO.ts`

```ts
// Introduce a typed CreateSessionContext object to avoid threading drift for userId/state checks.
```

### Success Criteria
Automated:
- [x] Cross-user non-blocking test fails first then passes.
- [x] Same-user fresh conflict test remains 409.
- [x] Migration validation test verifies new column/index are present.

Manual:
- [ ] Two different users can initialize sessions concurrently.

---

## Behavior 4: Supersede Stale Initialized Sessions (Fix 4)

### Test Specification
Given same-user initialized session older than threshold, when creating a new session, then stale session is transitioned out of `initialized` and new session is persisted.

Edge cases:
- Fresh session (below threshold) still blocks.
- Supersede update failure returns persistence error and does not persist new session.

### TDD Cycle

#### Red: Write Failing Test
Files:
- `frontend/src/server/services/__tests__/InitializeSessionService.checkActive.test.ts`
- `frontend/src/server/services/__tests__/InitializeSessionService.stale.test.ts` (new)

```ts
it('supersedes stale initialized session and proceeds to persist', async () => {
  // mock active session createdAt older than threshold
  // expect DAO.supersedeInitializedSession called before persist
});

it('keeps fresh initialized session blocking', async () => {
  // expect SESSION_ALREADY_ACTIVE and no persist
});
```

#### Green: Minimal Implementation
Files:
- `frontend/src/server/services/InitializeSessionService.ts`
- `frontend/src/server/data_access_objects/InitializeSessionDAO.ts`

```ts
const STALE_INITIALIZED_MS = 30 * 60 * 1000;
if (activeSession && isStale(activeSession.createdAt)) {
  await InitializeSessionDAO.supersedeInitializedSession(activeSession.id);
} else {
  SessionUniquenessVerifier.verify(activeSession !== null);
}
```

```ts
async supersedeInitializedSession(id: string): Promise<void> {
  await supabase.from('sessions').update({ state: 'FINALIZE', updated_at: new Date().toISOString() }).eq('id', id);
}
```

#### Refactor: Improve Code
File: `frontend/src/server/services/InitializeSessionService.ts`
```ts
// Extract stale-age policy into pure function for deterministic unit testing.
```

### Success Criteria
Automated:
- [x] Stale-branch test fails before logic exists.
- [x] Fresh-session blocking test still passes.
- [x] DAO failure path test confirms no second persist attempt.

Manual:
- [ ] Reproduced flow: stale zombie no longer permanently blocks URL retry.

---

## Behavior 5: End-to-End URL Ingestion Recovery Path

### Test Specification
Given initial URL submission creates session row, when subsequent load/retry occurs under legacy or stale conditions, then API behavior converges to either successful session load or one-retry recovery.

Edge cases: preserve auth, feature flag, and invalid-domain behavior in existing route tests.

### TDD Cycle

#### Red: Write Failing Test
Files:
- `frontend/src/app/api/ingestion/url/__tests__/route.test.ts`
- `frontend/src/app/api/sessions/[id]/__tests__/route.get.test.ts`

```ts
it('does not fail session fetch due to null updatedAt legacy record', async () => {
  // mock handler output w/ null updatedAt and expect 200
});

it('ingestion adapter receives userId-scoped creation context', async () => {
  // assert adapter call includes userId and canonicalUrl
});
```

#### Green: Minimal Implementation
Files:
- `frontend/src/app/api/ingestion/url/route.ts`
- `frontend/src/app/api/sessions/[id]/route.ts`
- `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts`

```ts
// Preserve existing entrypoints, but flow now rides user-scoped + stale-aware service semantics.
```

#### Refactor: Improve Code
File: `frontend/src/server/services/ChannelIngestionPipelineAdapter.ts`
```ts
// Keep host/contextSummary derivation isolated from session-creation policy concerns.
```

### Success Criteria
Automated:
- [x] URL route test suite remains green with new expectations.
- [x] Session GET route rejects only true malformed payloads, not legacy null timestamps.
- [x] Full frontend test suite green.

Manual:
- [ ] Direct paste URL path creates session, loads `/session/[id]`, and retries recover after stale conflict.

## Integration and Regression Suite
- Run targeted suites first (fast feedback), then full `frontend` tests.
- Add one integration test for cross-user isolation in URL ingestion path.
- Add one integration test for stale-session supersede and retry convergence.
- Re-run existing duplicate-session integration tests and update assertions from global uniqueness to same-user uniqueness where applicable.

## References
- `specs/orchestration/url-ingestion-error-space-model.md`
- `artifacts/tlaplus/url-ingestion-error-space-model/UrlIngestionErrorSpaceModel.tla`
- [`frontend/src/server/services/InitializeSessionService.ts`](/home/maceo/Dev/silmari-writer/frontend/src/server/services/InitializeSessionService.ts)
- [`frontend/src/server/data_access_objects/InitializeSessionDAO.ts`](/home/maceo/Dev/silmari-writer/frontend/src/server/data_access_objects/InitializeSessionDAO.ts)
- [`frontend/src/server/data_access_objects/SessionDAO.ts`](/home/maceo/Dev/silmari-writer/frontend/src/server/data_access_objects/SessionDAO.ts)
- [`frontend/src/server/data_structures/SessionView.ts`](/home/maceo/Dev/silmari-writer/frontend/src/server/data_structures/SessionView.ts)
- [`frontend/src/app/api/ingestion/url/route.ts`](/home/maceo/Dev/silmari-writer/frontend/src/app/api/ingestion/url/route.ts)
- [`frontend/src/app/api/sessions/[id]/route.ts`](/home/maceo/Dev/silmari-writer/frontend/src/app/api/sessions/[id]/route.ts)
- [`supabase/migrations/20260302000000_initial_schema.sql`](/home/maceo/Dev/silmari-writer/supabase/migrations/20260302000000_initial_schema.sql)
