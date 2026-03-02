# Session Workflow UI Integration TDD Implementation Plan

## Overview
Implement the session workflow UI end-to-end in production routes so paths 293–339 are reachable in the actual app, not only in isolated modules/tests. The plan keeps existing chat behavior stable while introducing a production workflow surface and route-driven orchestration.

## Current State Analysis
The codebase has substantial workflow implementation, but route-level integration is missing.

### Key Discoveries
- Live `/` page is chat-centric and does not mount workflow modules (`WritingFlowModule`, `StartVoiceSessionModule`, `OrientStoryModule`, `AnswerModule`, `FinalizedAnswerModule`): `frontend/src/app/page.tsx:5-23`, `frontend/src/app/page.tsx:203-287`.
- Production `app` routes currently include only `/` plus test pages; there is no `session/[id]` page.
- Session-start module already expects route navigation to `/session/[id]`: `frontend/src/modules/session/StartVoiceSessionModule.tsx:92`.
- Writing flow module and review/recall transitions are already implemented and tested in isolation: `frontend/src/modules/WritingFlowModule.tsx:116-158`, `frontend/src/modules/__tests__/WritingFlowModule.rendering.test.tsx:56-201`.
- Existing integration tests directly import `HomePage` and assert current chat/file behavior, so replacing `/` outright will regress coverage: `frontend/__tests__/integration/file-send-flow.test.tsx:4-152`, `frontend/__tests__/e2e/VoiceIntegration.test.tsx:90-102`.
- Backend DAO already supports session lookup for read endpoints (`findById`, `findAnswerSessionById`) but no UI-facing read route is exposed for page hydration: `frontend/src/server/data_access_objects/SessionDAO.ts:57-75`, `frontend/src/server/data_access_objects/SessionDAO.ts:184-202`.
- State vocabularies differ across domains (`INIT/ORIENT/RECALL/VERIFY/...` vs `DRAFT/FINALIZE`), requiring an explicit UI stage mapper: `frontend/src/server/data_structures/AnswerSession.ts:21-41`, `frontend/src/server/data_structures/Session.ts:17-22`.

## Desired End State
A user can start from a production workflow entrypoint, create/open a session, and progress through the UI flow that surfaces existing components/modules for orient, recall/review, finalize/export, and KPI tracking.

### Observable Behaviors
- Given a user opens workflow entry, when route loads, then they see workflow start UI (not test-only pages).
- Given a valid start action, when session is created, then app navigates to `/session/[sessionId]` and hydrates server session state.
- Given hydrated session state, when page renders, then the correct workflow module is mounted for that stage.
- Given actions succeed (confirm/approve/finalize/export), when callbacks fire, then stage and visible UI advance consistently.
- Given API failures or invalid stage values, when rendering/transition occurs, then user sees stable error UI and no illegal transition.
- Given existing chat flows, when `/` is used, then current chat/file/voice tests still pass.

## What We're NOT Doing
- Rewriting backend business logic already implemented for paths 293–339.
- Replacing or redesigning the existing chat UX on `/` in this pass.
- Implementing new analytics providers or changing KPI semantics.
- Solving non-UI technical debt already identified in specs (for example, TOCTOU and non-fatal analytics deviations).

## Testing Strategy
- **Framework**: Vitest + React Testing Library (`frontend/vitest.config.ts:5-21`).
- **Test Types**:
  - Unit: stage mapping, route param parsing, callback/state reducers.
  - Integration: production pages mounting modules + API contract interaction.
  - API integration: new `GET /api/sessions/[id]` endpoint contract.
  - Optional E2E extension: playwright smoke route for `/writer` → `/session/[id]` navigation.
- **Mocking/Setup**:
  - Continue existing pattern of `fetch` stubbing and `next/navigation` router mocks.
  - Mock auth context/token provider in route/page tests.
  - Keep legacy `HomePage` tests intact; add new tests rather than replacing old assertions first.

## Behavior 1: Expose Workflow Entry in Production Routes

### Test Specification
**Given**: App route tree in production.
**When**: User visits `/writer` (or clicks an explicit entry action from `/`).
**Then**: Workflow entry UI renders and is not dependent on `test-*` pages.

**Edge Cases**:
- Unknown entry params render safe fallback.
- Entry route SSR/client hydration mismatch does not crash.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/src/app/writer/__tests__/page.test.tsx`
```tsx
describe('Writer entry route', () => {
  it('renders workflow entry UI in production route', () => {
    render(<WriterPage />);
    expect(screen.getByTestId('workflow-entry')).toBeInTheDocument();
  });
});
```

#### 🟢 Green: Minimal Implementation
**File**: `frontend/src/app/writer/page.tsx`
```tsx
export default function WriterPage() {
  return <div data-testid="workflow-entry"><StartVoiceSessionModule ... /></div>;
}
```

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/app/writer/page.tsx`
```tsx
// Extract route-level auth/token adapter and error boundary
<WorkflowEntryPageShell />
```

### Success Criteria
**Automated:**
- [ ] Red test fails for missing route: `npm run test -- src/app/writer/__tests__/page.test.tsx`
- [x] Green test passes after route creation.
- [x] Typecheck passes for new route: `npm run type-check`

**Manual:**
- [ ] `/writer` loads from browser without using `/test*` routes.
- [ ] Entry UI is visually accessible and interactive.

---

## Behavior 2: Mount Start Session Flow with Real Navigation

### Test Specification
**Given**: Authenticated user + token at workflow entry.
**When**: User clicks `Start Voice-Assisted Session`.
**Then**: `createSession` executes, and router navigates to `/session/[id]`.

**Edge Cases**:
- Missing token redirects to `/login` (or configured auth route).
- API failure surfaces error state without navigation.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/src/app/writer/__tests__/page.start-session.test.tsx`
```tsx
it('navigates to /session/[id] after successful session creation', async () => {
  mockCreateSession.mockResolvedValue({ sessionId: 'uuid', state: 'INIT' });
  render(<WriterPage />);
  await user.click(screen.getByRole('button', { name: /start voice-assisted session/i }));
  expect(mockPush).toHaveBeenCalledWith('/session/uuid');
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/app/writer/page.tsx`
- `frontend/src/modules/session/StartVoiceSessionModule.tsx` (adapter-only changes)
```tsx
<StartVoiceSessionModule user={user} authToken={token} onNavigate={router.push} />
```

#### 🔵 Refactor: Improve Code
**File**: `frontend/src/modules/session/StartSessionRouteAdapter.tsx` (new)
```tsx
// Isolate auth/token retrieval + navigation wiring from UI module
```

### Success Criteria
**Automated:**
- [x] Route-level navigation test passes.
- [x] Existing module tests remain green: `npm run test -- src/modules/session/__tests__/StartVoiceSessionModule.test.tsx`

**Manual:**
- [ ] Start action moves user to `/session/{id}` in browser.
- [ ] Error scenario shows message and keeps user on entry route.

---

## Behavior 3: Add Session Read Contract for Route Hydration

### Test Specification
**Given**: A session ID in URL.
**When**: `/session/[sessionId]` loads.
**Then**: UI fetches normalized session data from API contract and hydrates stage state.

**Edge Cases**:
- 404 session shows not-found UI.
- Non-UUID ID returns 400 contract error.
- Malformed server payload fails schema validation and shows recoverable error UI.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/api_contracts/__tests__/getSession.test.ts`
- `frontend/src/app/api/sessions/[id]/__tests__/route.get.test.ts`
```ts
it('returns normalized session payload for valid id', async () => {
  const result = await getSession('uuid');
  expect(result.id).toBe('uuid');
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/api_contracts/getSession.ts` (new)
- `frontend/src/app/api/sessions/[id]/route.ts` (new `GET`)
- `frontend/src/server/request_handlers/GetSessionHandler.ts` (new)
```ts
// GET /api/sessions/[id] -> SessionDAO.findAnswerSessionById / findById -> normalized DTO
```

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/server/data_structures/SessionView.ts` (new shared schema)
- `frontend/src/app/api/sessions/[id]/route.ts`
```ts
// Centralize response schema + error mapping for all session read callers
```

### Success Criteria
**Automated:**
- [x] Contract tests pass for success + error variants.
- [x] API route tests pass with status-code assertions.
- [x] Lint/typecheck pass for new contracts and schemas.

**Manual:**
- [ ] `/session/{id}` shows hydrated state-driven UI for valid session.
- [ ] Invalid IDs show error state instead of blank page/crash.

---

## Behavior 4: Orchestrate Session Stage → Module Rendering

### Test Specification
**Given**: Hydrated session data and workflow context.
**When**: Stage changes or page reloads.
**Then**: Correct module is rendered for each stage (ORIENT, RECALL/REVIEW, DRAFT, FINALIZE).

**Edge Cases**:
- Unknown stage renders safe fallback + logs.
- Stage transition callbacks cannot jump to illegal target.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**Files**:
- `frontend/src/modules/session/__tests__/SessionWorkflowShell.test.tsx` (new)
- `frontend/src/modules/session/__tests__/stageMapper.test.ts` (new)
```tsx
it('renders WritingFlowModule when stage is REVIEW', () => {
  render(<SessionWorkflowShell initialStage="REVIEW" ... />);
  expect(screen.getByTestId('writing-flow-module')).toBeInTheDocument();
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/modules/session/SessionWorkflowShell.tsx` (new)
- `frontend/src/modules/session/stageMapper.ts` (new)
```ts
// map backend session states -> UI stage enum -> module component switch
```

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/modules/session/stageMapper.ts`
- `frontend/src/modules/session/SessionWorkflowShell.tsx`
```ts
// Pure transition + rendering map table; remove branching duplication
```

### Success Criteria
**Automated:**
- [x] Stage mapper unit tests cover all known states + unknown fallback.
- [x] Shell integration tests verify module mounts by stage.
- [x] Existing module tests still pass unchanged.

**Manual:**
- [ ] Refreshing `/session/{id}` preserves correct visible stage.
- [ ] Invalid stage yields visible fallback with actionable message.

---

## Behavior 5: Wire Cross-Step Actions for End-to-End Reachability

### Test Specification
**Given**: User proceeds through session workflow.
**When**: Confirm, approve, finalize, export/copy, and KPI actions are performed.
**Then**: UI advances, backend contracts are called, and post-action module visibility updates.

**Edge Cases**:
- Action failure keeps user on current stage.
- Partial success (for example analytics non-fatal) still shows deterministic UI outcome.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**File**: `frontend/src/app/session/[sessionId]/__tests__/page.flow.integration.test.tsx` (new)
```tsx
it('advances review -> finalize -> finalized module controls', async () => {
  render(<SessionPage params={{ sessionId: 'uuid' }} />);
  await user.click(screen.getByRole('button', { name: /approve/i }));
  expect(screen.getByTestId('answer-status')).toBeInTheDocument();
});
```

#### 🟢 Green: Minimal Implementation
**Files**:
- `frontend/src/app/session/[sessionId]/page.tsx` (new)
- `frontend/src/modules/session/SessionWorkflowShell.tsx`
```tsx
// Pass callbacks from module to shell reducer; update local stage state on success
```

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/modules/session/useWorkflowReducer.ts` (new)
- `frontend/src/app/session/[sessionId]/page.tsx`
```ts
// Consolidate stage transitions and error handling in reducer + action creators
```

### Success Criteria
**Automated:**
- [x] Page-level integration tests pass for happy path + error path.
- [x] Related module integration tests remain green:
  - `src/modules/review/__tests__/ReviewWorkflowModule.test.tsx`
  - `src/modules/answer/__tests__/finalizeAnswer.integration.test.tsx`
  - `src/modules/finalizedAnswer/__tests__/exportOrCopyFinalizedAnswer.integration.test.tsx`

**Manual:**
- [ ] User can complete at least one full visible flow from start to finalized controls.
- [ ] Error states keep user in-context without blank screens.

---

## Behavior 6: Preserve Existing Chat Route and Regression Coverage

### Test Specification
**Given**: Existing `/` chat behavior and tests.
**When**: Workflow routes are added.
**Then**: existing tests that rely on `HomePage` still pass, and no accidental behavior regressions occur.

**Edge Cases**:
- New global layout/nav does not break `HomePage` selectors.
- Workflow imports do not pull incompatible browser APIs into chat tests.

### TDD Cycle

#### 🔴 Red: Write Failing Test
**Files**:
- Existing tests as regression baseline:
  - `frontend/__tests__/integration/file-send-flow.test.tsx`
  - `frontend/__tests__/e2e/VoiceIntegration.test.tsx`

#### 🟢 Green: Minimal Implementation
**Files**:
- Keep `frontend/src/app/page.tsx` behavior intact.
- Add link/button to `/writer` only if it does not break existing assertions.

#### 🔵 Refactor: Improve Code
**Files**:
- `frontend/src/app/page.tsx`
- `frontend/src/components/layout/AppLayout.tsx` (if needed)
```tsx
// Introduce optional, test-safe workflow entry CTA with stable labels/testids
```

### Success Criteria
**Automated:**
- [x] Existing `HomePage` integration tests remain green.
- [x] Full test subset for touched paths passes before merge.

**Manual:**
- [ ] `/` remains functional chat surface.
- [ ] Workflow entry discoverable from production UI.

---

## Integration & E2E Testing
- Integration scenarios:
  - `/writer` entry rendering + start-session navigation.
  - `/session/[id]` hydration and stage-driven module rendering.
  - Callback-driven stage advancement and fallback behavior.
- API integration scenarios:
  - `GET /api/sessions/[id]` success, 400, 404, 500.
- E2E smoke (optional but recommended):
  - Start at `/writer` → create session (mocked backend) → land on `/session/[id]` → see stage module.

## Execution Order (Smallest First)
1. Add route + shell tests (`/writer`) without changing `/`.
2. Add session read contract + `GET /api/sessions/[id]`.
3. Add `/session/[sessionId]` page with stage mapper.
4. Wire callback-driven transitions across modules.
5. Run regression suite for existing chat page.
6. Refactor shared stage/reducer utilities.

## Verification Commands
- Targeted tests:
  - `npm run test -- src/app/writer/__tests__/page.test.tsx`
  - `npm run test -- src/app/session/[sessionId]/__tests__/page.flow.integration.test.tsx`
  - `npm run test -- src/api_contracts/__tests__/getSession.test.ts`
  - `npm run test -- src/app/api/sessions/[id]/__tests__/route.get.test.ts`
- Existing regressions:
  - `npm run test -- __tests__/integration/file-send-flow.test.tsx`
  - `npm run test -- __tests__/e2e/VoiceIntegration.test.tsx`
- Quality gates:
  - `npm run type-check`
  - `npm run lint`
  - `npm run test`

## References
- Session plans state: `thoughts/searchable/shared/plans/session-1772314225364/.tdd_state.json`
- Core app route: `frontend/src/app/page.tsx:5-23`, `frontend/src/app/page.tsx:203-287`
- Session start navigation: `frontend/src/modules/session/StartVoiceSessionModule.tsx:73-103`
- Writing flow module: `frontend/src/modules/WritingFlowModule.tsx:116-158`
- Review workflow module: `frontend/src/modules/review/ReviewWorkflowModule.tsx:37-179`
- Answer + finalized modules:
  - `frontend/src/modules/answer/AnswerModule.tsx:33-92`
  - `frontend/src/modules/finalizedAnswer/FinalizedAnswerModule.tsx:38-155`
- Session data structures:
  - `frontend/src/server/data_structures/AnswerSession.ts:21-41`
  - `frontend/src/server/data_structures/Session.ts:17-22`
- DAO capability for session reads:
  - `frontend/src/server/data_access_objects/SessionDAO.ts:57-75`
  - `frontend/src/server/data_access_objects/SessionDAO.ts:184-202`
- Existing `/` regressions:
  - `frontend/__tests__/integration/file-send-flow.test.tsx:4-152`
  - `frontend/__tests__/e2e/VoiceIntegration.test.tsx:90-102`
- Domain specs:
  - `specs/session-initialization.md`
  - `specs/voice-recall-story-selection.md`
  - `specs/draft-generation-review.md`
  - `specs/finalize-export-sms.md`
  - `specs/metrics-analytics.md`
