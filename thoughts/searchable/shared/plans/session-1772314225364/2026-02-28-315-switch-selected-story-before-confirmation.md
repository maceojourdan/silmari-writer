# switch-selected-story-before-confirmation TDD Plan

Path spec: /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/315-switch-selected-story-before-confirmation.md

---

## Verification (Phase 0)

The TLA+ model for this path passed: **Reachability**, **TypeInvariant**, **ErrorConsistency**.

Command:
```
silmari verify-path /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/315-switch-selected-story-before-confirmation.md
```

Verification output (excerpt):
```
Result: ALL PROPERTIES PASSED
States: 18 found, 9 distinct, depth 0
Properties: Reachability, TypeInvariant, ErrorConsistency
```

This guarantees at the model level:
- Every step is reachable from the trigger.
- Input/output types are consistent at each boundary.
- All error branches lead to valid error states.

The following TDD plan recreates those guarantees at the code level.

---

## Tech Stack (Gate 2 – Option 1)
- Frontend: Next.js (App Router) + React + TypeScript
- Test runner: Vitest + React Testing Library
- Logging: frontend_logging (`cfg-r3d7`)

---

## Resource Mapping

| UUID     | Registry Name      | Concrete Implementation |
|----------|-------------------|--------------------------|
| ui-w8p2  | component          | `frontend/components/StorySelectionList.tsx` |
| cfg-r3d7 | frontend_logging   | `frontend/logging/index.ts` |

---

## Step 1: Capture story selection event ✅

**From path spec:**
- Input: User click event on a story item handled by frontend component (ui-w8p2).
- Process: Detect click and identify newly selected story and currently selected story from state.
- Output: Newly selected story identifier and current selected story identifier available in component state context.
- Error: If clicked story identifier is missing or invalid, ignore event and log via frontend_logging (cfg-r3d7).

### Test (`frontend/components/__tests__/StorySelectionList.step1.test.tsx`)

**Reachability**
- Render component with two stories (`id: 'a'`, `id: 'b'`) and initial selected `'a'`.
- Simulate click on `'b'`.
- Assert internal handler receives `{ newId: 'b', currentId: 'a' }`.

**TypeInvariant**
- Assert both identifiers are `string`.
- Assert they match the `StoryId = string` TypeScript type.

**ErrorConsistency**
- Simulate click with invalid id (`undefined` via malformed event).
- Assert:
  - No state update function invoked.
  - `frontend_logging.error` called with `INVALID_STORY_ID`.

### Implementation (`frontend/components/StorySelectionList.tsx`)

- Props:
  ```ts
  type Story = { id: string; title: string; selected: boolean };
  ```
- Maintain local state: `stories: Story[]`.
- Implement `handleStoryClick(id?: string)`:
  - If `!id || !stories.find(s => s.id === id)` → log error via `frontend_logging.error(...)` and return.
  - Derive `currentSelected = stories.find(s => s.selected)?.id ?? null`.
  - Forward `{ newId: id, currentId }` to evaluation step.

Minimal logic only to satisfy tests.

---

## Step 2: Evaluate selection change ✅

**From path spec:**
- Input: Newly selected story identifier and current selected story identifier.
- Process: Compare identifiers.
- Output: Decision to update selection state to newly selected story.
- Error: If identifiers match, no state change and exit.

### Test (`frontend/components/__tests__/StorySelectionList.step2.test.tsx`)

**Reachability**
- Given `newId='b'`, `currentId='a'`.
- Call evaluation function.
- Assert result is `{ shouldUpdate: true }`.

**TypeInvariant**
- Assert return type is `{ shouldUpdate: boolean }`.

**ErrorConsistency**
- Given `newId='a'`, `currentId='a'`.
- Assert result is `{ shouldUpdate: false }`.
- Assert no state mutation occurs.

### Implementation

Extract pure function in same file:
```ts
export function evaluateSelectionChange(newId: string, currentId: string | null) {
  return { shouldUpdate: newId !== currentId };
}
```

Component calls this before updating state.

---

## Step 3: Update selected story state ✅

**From path spec:**
- Input: Decision to update selection and story list state.
- Process: Set previous `selected=false`, new `selected=true`, ensure exactly one selected.
- Output: Updated component state with exactly one selected story.
- Error: If inconsistent data (story not found), log error and retain previous state.

### Test (`frontend/components/__tests__/StorySelectionList.step3.test.tsx`)

**Reachability**
- Initial: `'a'` selected.
- Trigger update to `'b'`.
- Assert:
  - `'a'.selected === false`
  - `'b'.selected === true`
  - Exactly one story has `selected === true`.

**TypeInvariant**
- Assert resulting state is `Story[]`.
- Assert exactly one `selected: true`.

**ErrorConsistency**
- Attempt update with `newId='missing'`.
- Assert:
  - `frontend_logging.error` called with `STORY_NOT_FOUND`.
  - State remains unchanged.

### Implementation

Add function:
```ts
function updateSelectedStory(stories: Story[], newId: string): Story[] | null
```

- If story not found → log + return `null`.
- Otherwise map:
  ```ts
  stories.map(s => ({ ...s, selected: s.id === newId }))
  ```
- Component only sets state if result not null.

---

## Step 4: Render updated selection in UI ✅

**From path spec:**
- Input: Updated component state.
- Process: Re-render story list UI.
- Output: Only newly selected story visually marked selected.
- Error: If rendering fails, log error and keep last successful render.

### Test (`frontend/components/__tests__/StorySelectionList.step4.test.tsx`)

**Reachability**
- Render with `'a'` selected.
- Click `'b'`.
- Assert DOM:
  - `'a'` does NOT have `data-selected="true"`.
  - `'b'` HAS `data-selected="true"`.

**TypeInvariant**
- Assert rendered attributes reflect boolean `selected` state.

**ErrorConsistency**
- Mock rendering error (wrap item render in try/catch and simulate throw).
- Assert:
  - `frontend_logging.error` called with `RENDER_FAILURE`.
  - Previously rendered DOM remains unchanged.

### Implementation

- Render:
  ```tsx
  <li
    key={story.id}
    data-selected={story.selected}
    onClick={() => handleStoryClick(story.id)}
  >
  ```
- Wrap render mapping in try/catch:
  - On catch → log error, render last stable snapshot (store in ref).

Minimal error boundary logic sufficient to satisfy tests.

---

## Terminal Condition ✅

### Integration Test (`frontend/components/__tests__/StorySelectionList.integration.test.tsx`)

- Given two stories, `'a'` initially selected.
- User clicks `'b'` before confirmation.
- Assert:
  - `'a'` visually deselected.
  - `'b'` visually selected.
  - Exactly one story selected in state.

This proves end-to-end reachability from trigger → terminal UI state.

---

## References
- /home/maceo/Dev/silmari-writer/specs/orchestration/session-1772314225364/315-switch-selected-story-before-confirmation.md
- Gate 2 Tech Stack (Option 1 – Next.js + TypeScript)
- Resource Registry entries: ui-w8p2, cfg-r3d7

---

## Validation Report: 315-switch-selected-story-before-confirmation

### Implementation Status

| Phase | Status | Notes |
|-------|--------|-------|
| Step 1: Capture story selection event | ✅ Fully implemented | 3/3 tests passing |
| Step 2: Evaluate selection change | ✅ Fully implemented | 4/4 tests passing (1 bonus) |
| Step 3: Update selected story state | ✅ Fully implemented | 5/5 tests passing |
| Step 4: Render updated selection in UI | ✅ Fully implemented | 3/3 tests passing |
| Terminal Condition: Integration test | ✅ Fully implemented | 2/2 tests passing (1 bonus) |

### Automated Verification Results

| Check | Result |
|-------|--------|
| Vitest tests | ✅ **17/17 passing** across 5 test files (759ms) |
| TypeScript (StorySelectionList) | ✅ **0 errors** (no TS errors in implementation or test files) |
| Logging dependency (`@/logging/index`) | ✅ **Exists** with correct `frontendLogger.error(message, error?, context?)` signature |
| Path spec reference | ✅ **Exists** at `specs/orchestration/session-1772314225364/315-switch-selected-story-before-confirmation.md` |

### Code Review Findings

#### ✅ Matches Plan
- **Types**: `Story = { id: string; title: string; selected: boolean }` and `StoryId = string` match spec exactly
- **Step 1**: `handleStoryClick(id?)` validates ID, derives `currentSelected`, forwards `{ newId, currentId }` — exact plan match
- **Step 2**: `evaluateSelectionChange()` exported as pure function returning `{ shouldUpdate: boolean }` — exact plan match
- **Step 3**: `updateSelectedStory()` returns `Story[] | null`, logs `STORY_NOT_FOUND` on missing ID, uses `.map()` — exact plan match
- **Step 4**: Renders `<li data-selected={story.selected}>`, try/catch with `RENDER_FAILURE` logging, fallback to `lastStableRender` ref — exact plan match
- **Integration**: End-to-end click flow with "exactly one selected" invariant — exact plan match
- **Error codes**: `INVALID_STORY_ID`, `STORY_NOT_FOUND`, `RENDER_FAILURE` all correctly used per spec

#### 🟢 Improvements Over Plan
- **Bonus integration test**: `should handle rapid successive clicks correctly` — validates a real-world edge case not in the plan
- **Accessibility attributes**: Added `role="option"`, `aria-selected`, `role="listbox"`, `aria-label` — improves a11y beyond what was specified
- **`data-testid` attributes**: e.g. `story-item-a` — makes tests more robust than text-based queries alone
- **`SelectionChangePayload` interface**: Clean typed callback interface for parent integration

#### ⚠️ Deviations from Plan

1. **File path**: Plan specifies `frontend/components/` but files live at `frontend/src/components/`
   - **Severity**: Low — `frontend/src/` is the project convention; plan used a shorthand
   
2. **Dead code — `StoryItemErrorBoundary`** (lines 83–106): Class component error boundary is defined but **never used** in JSX. The render error handling uses try/catch instead.
   - **Severity**: Low — functionally correct, but unused code should be removed

3. **Test-only props** (`_testInvalidClickId`, `_testForceRenderError`): These exist in production code to enable error path testing.
   - **Severity**: Low — underscored and optional, but a `NODE_ENV` guard or separate test wrapper would be cleaner

4. **`@ts-nocheck`** in all test files: TypeScript checking is bypassed in tests.
   - **Severity**: Low — pragmatic for heavy mocking, but weakens type safety guarantees in test assertions

### 🔴 Critical Issue: Files Not Committed

All 6 implementation files are **untracked** (`??` status):
```
?? frontend/src/components/StorySelectionList.tsx
?? frontend/src/components/__tests__/StorySelectionList.integration.test.tsx
?? frontend/src/components/__tests__/StorySelectionList.step1.test.tsx
?? frontend/src/components/__tests__/StorySelectionList.step2.test.tsx
?? frontend/src/components/__tests__/StorySelectionList.step3.test.tsx
?? frontend/src/components/__tests__/StorySelectionList.step4.test.tsx
```
**Action needed**: These must be committed before they can be merged or reviewed.

### TLA+ Property Coverage

| Property | Step 1 | Step 2 | Step 3 | Step 4 | Integration |
|----------|--------|--------|--------|--------|-------------|
| Reachability | ✅ | ✅ | ✅ | ✅ | ✅ |
| TypeInvariant | ✅ | ✅ | ✅ | ✅ | — |
| ErrorConsistency | ✅ | ✅ | ✅ | ✅ | — |

All three TLA+-modeled properties are covered at every step — the code-level tests faithfully replicate the model guarantees.

### Recommendations

1. **Commit the files** — this is the only blocking issue
2. **Remove `StoryItemErrorBoundary`** dead code (lines 83–106)
3. **Consider removing `@ts-nocheck`** from test files and adding proper Vitest type references instead
4. **Consider extracting test-only props** into a test wrapper component rather than embedding them in production code
5. **Update the plan file paths** from `frontend/components/` to `frontend/src/components/` for accuracy

### Verdict: ✅ PASS (with caveats)

The implementation is **functionally complete and correct**. All 4 steps + terminal condition are implemented with full TLA+ property coverage. All 17 tests pass. The only blocking issue is that **files need to be committed**. The dead code and `@ts-nocheck` are minor cleanup items.
Done: success