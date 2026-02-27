# Extract TLA+ Model from Existing Code

You are tasked with analyzing existing code in a brownfield codebase, extracting a formal behavioral model of the affected functions, and producing a TLA+ path spec that captures the current behavior. This model then constrains subsequent implementation work — ensuring new changes don't violate existing invariants.

This command bridges `/research_codebase` and `/create_tdd_plan` by formalizing the research output into a checkable artifact instead of prose.

Use Haiku subagents for file searches, grep, and file discovery tasks.
Use up to 10 Sonnet subagents for analyzing code behavior, tracing state transitions, and identifying invariants.
Keep the main context window for synthesis and model writing — delegate all deep reading to subagents.

## Initial Response

**If parameters provided** (file paths, function names, or a change description):
- Read all mentioned files FULLY (no partial reads)
- Begin analysis immediately

**If no parameters:**
```
I'll help you extract a TLA+ behavioral model from existing code. This model captures what the code does today so we can verify that proposed changes don't break existing invariants.

Please provide:
1. **What you want to change** — a brief description of the new functionality or modification
2. **Entry points** — file paths, function names, or module names that are affected
3. **Scope boundary** (optional) — how deep to trace (e.g., "just this module" or "follow calls into the database layer")

Example: `/extract_tlaplus_model "Add retry logic to http_post" src/api/client.rs`
Example: `/extract_tlaplus_model src/pipeline.rs "I want to add a caching step between verify and refine"`
```

Then wait for the user's input.

## Process

### Step 1: Scope the Extraction

1. **Read all mentioned files FULLY** using the Read tool (no limit/offset)
   - DO NOT spawn sub-tasks before reading these files yourself
   - This gives you the primary context before decomposing

2. **Identify the change boundary:**
   - What functions will be modified or extended?
   - What functions call those functions (callers)?
   - What functions do those functions call (callees)?
   - Where is the boundary — what do we model vs. treat as opaque?

3. **Present the scope for confirmation:**
```
**Extraction Scope:**

Change: [what the user wants to do]

Functions to model (will be TLA+ states):
- `function_a()` in file.rs:45 — [brief role]
- `function_b()` in file.rs:112 — [brief role]

Callers (modeled as triggers/observers):
- `caller_x()` in other.rs:30 — expects [contract]

Callees (modeled as opaque steps):
- `db.query()` — returns [type], can fail with [errors]

Boundary: [what's inside vs outside the model]

Does this scope capture the right slice? Too broad? Too narrow?
```

### Step 2: Extract State Machine

Spawn parallel subagents to analyze each function in the scope:

**For each function, extract:**

1. **States** — What distinct phases does this function pass through?
   - Entry state (what must be true when called)
   - Processing states (intermediate conditions)
   - Terminal states (success, error variants)
   - Example: `idle → validating → processing → {success, validation_error, timeout}`

2. **Transitions** — What causes state changes?
   - What input/condition moves from state A to state B?
   - Are transitions deterministic or conditional?
   - What data flows between states?

3. **Invariants** — What must ALWAYS be true?
   - Type contracts (what goes in, what comes out)
   - Ordering constraints (A must happen before B)
   - Resource contracts (if acquired, must be released)
   - Error propagation rules (errors propagate vs. are swallowed)
   - Idempotency properties (safe to retry?)

4. **Caller expectations** — What do callers depend on?
   - Return type contract
   - Error types they handle
   - Side effects they expect (or expect NOT to happen)
   - Ordering assumptions (call A before B)

**Subagent prompts should be specific:**
- "Read `src/api/client.rs` lines 45-120. Identify all states that `http_post` can be in (from entry to return). List each conditional branch, each error return, and each successful return. Format as: state_name → condition → next_state."
- "Read `src/api/client.rs` and all files that call `http_post`. For each caller, document: what return values they handle, what errors they catch, and what assumptions they make about http_post's behavior."

### Step 3: Synthesize the Behavioral Model

Combine subagent findings into a unified state machine:

1. **Merge overlapping states** — if two subagents describe the same function differently, reconcile
2. **Resolve conflicts** — if caller A expects error propagation but caller B expects silent retry, flag this as a model conflict (this IS the kind of bug TLA+ helps find)
3. **Identify implicit invariants** — patterns that aren't explicitly documented but are relied upon

Present the behavioral model in plain language first:

```
**Behavioral Model: [scope name]**

States:
1. idle — function not yet called
2. validating_input — checking arguments against [contract]
3. executing — main operation in progress
4. [etc.]

Transitions:
- idle → validating_input: function called with (arg1, arg2)
- validating_input → executing: all validation passes
- validating_input → error: validation fails → returns ValidationError
- executing → success: operation completes → returns Result<T>
- executing → error: operation fails → returns OperationError
- [etc.]

Invariants:
1. [INV-1] Every call terminates (no infinite loops or hangs)
2. [INV-2] Errors are always propagated to caller (never swallowed)
3. [INV-3] If resource X is acquired, it is released on all paths
4. [etc.]

Caller contracts:
- caller_x expects: [what it relies on]
- caller_y expects: [what it relies on]

**Proposed change impact:**
The change "[description]" would affect transitions [X → Y] and may interact with invariant [INV-N].

Does this model accurately capture the current behavior?
```

### Step 4: Generate the TLA+ Path Spec

Convert the behavioral model into a path spec that `silmari verify-path` can consume. Use the standard path format from `specs/orchestration/`.

**Mapping rules:**
- Each **state** becomes a step in the path
- Each **transition** becomes the Input/Process/Output of a step
- Each **invariant** maps to a TLA+ property:
  - Ordering invariants → Reachability properties
  - Type contracts → TypeInvariant
  - Error propagation → ErrorConsistency
  - Termination → Liveness (with weak fairness)
- **Caller contracts** become terminal condition constraints
- **Error paths** become the Error field of each step

**Write the path spec** to `specs/orchestration/<scope-name>-model.md`:

```markdown
# PATH: <scope-name>-model

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from existing code — [files analyzed]

## Purpose

Behavioral model of [functions] extracted from the existing codebase.
This model captures current behavior as a verifiable baseline. Proposed
changes must preserve the invariants documented here unless explicitly
relaxing them.

## Trigger

[What activates this code path — the caller's action or system event]

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `cfg-a1b2` | config_store | Example: stores configuration state |
| `api-x3y4` | endpoint | Example: HTTP endpoint being modeled |

**UUID format (REQUIRED — parser rejects anything else):**
- Backtick-wrapped: `` `xx-xxxx` `` or `` `xxx-xxxx` ``
- Prefix: 2-3 lowercase letters (category: `cfg`, `api`, `db`, `fn`, `ui`, `fs`, `mq`)
- Hyphen separator
- Suffix: exactly 4 alphanumeric characters (e.g. `a1b2`, `x3Y4`)
- Examples: `cfg-a1b2`, `api-q7v1`, `db-a3f7`, `ui-w8p2`

Invent UUIDs for each component in scope. Each function, data type, config,
or external service gets one entry. The Name column is a single word (no spaces).

## Steps

1. **[State name from behavioral model]**
   - Input: [what enters this state]
   - Process: [transformation — WHAT not HOW]
   - Output: [what this state produces]
   - Error: [failure modes] -> [error handling behavior]

[Continue for all states...]

## Terminal Condition

[What callers observe on success. Derived from caller contract analysis.]

## Feedback Loops

[Any existing retry/loop behavior in the code, or "None — strictly linear."]

## Extracted Invariants

[This section is unique to extracted models — not present in greenfield paths.]

| ID | Invariant | Source | TLA+ Property |
|----|-----------|--------|---------------|
| INV-1 | [description] | [file:line] | Reachability / TypeInvariant / ErrorConsistency |
| INV-2 | [description] | [file:line] | [property type] |

## Change Impact Analysis

**Proposed change:** [user's description]

**Affected states:** [which steps change]
**Affected invariants:** [which INV-* might be impacted]
**Risk:** [what could break if the change is naive]
**Recommendation:** [how to extend the model to accommodate the change]
```

### Step 5: Verify the Extracted Model

Run the extracted model through TLA+ verification:

```bash
silmari verify-path specs/orchestration/<scope-name>-model.md
```

**Interpret results:**
- **All properties pass** → The model is internally consistent. Proceed to planning.
- **Reachability fails** → A state in the model is unreachable. This might mean dead code in the existing codebase, or a modeling error. Investigate before proceeding.
- **TypeInvariant fails** → The model has an inconsistency in data flow. Flag to user.
- **ErrorConsistency fails** → Error paths don't terminate properly. This might be a real bug in the existing code.

Present verification results:
```
**TLA+ Verification Results:**

States explored: [N]
Distinct states: [N]

Properties:
- Reachability: [PASS/FAIL] [details if fail]
- TypeInvariant: [PASS/FAIL]
- ErrorConsistency: [PASS/FAIL]

[If any FAIL: explanation and whether it's a modeling error or a real code issue]

The model is [verified / needs revision]. Ready to proceed to planning?
```

### Step 6: Handoff to Planning

Once the model is verified, present the user's options:

```
**Verified behavioral model ready.** The TLA+ model at:
  specs/orchestration/<scope-name>-model.md

captures the current behavior of [functions] with [N] invariants verified.

Next steps — choose one:
1. `/create_tdd_plan` with this model as input — tests will verify invariants are preserved
2. `/create_plan` to create a full implementation plan constrained by this model
3. Extend the model first — add the proposed change as new states, re-verify, then plan
4. Manual review — study the model and invariants before deciding

Recommended: Option 3 (extend model, verify, then plan) — this catches invariant violations
before you write any code.
```

### Step 7: Beads Integration

1. **Check for existing beads issues**: `bd list --status=open`
2. **Create a tracking issue**:
   ```bash
   bd create --title="TLA+ model: <scope-name>" --description="Extracted behavioral model from [files]. Invariants: [count]. Proposed change: [description]" --type=task --priority=2
   ```
3. **Link dependencies** if the model relates to other tracked work

## Guidelines

### What Makes a Good Extraction

- **Right granularity** — Model the functions being changed and one level of callers/callees. Going deeper adds noise without insight.
- **Explicit invariants** — Every invariant should cite the source file:line where the behavior is relied upon. "The code does X" is weaker than "caller at file.rs:45 depends on X."
- **Honest uncertainty** — If a behavior is ambiguous (e.g., is this error swallowed intentionally or accidentally?), flag it as `[AMBIGUOUS]` rather than guessing.
- **Minimal states** — Prefer fewer states with clear transitions over many fine-grained states. The model should be readable by a human in under 2 minutes.

### Common Patterns

| Code Pattern | TLA+ Model |
|---|---|
| Sequential function calls | Linear step chain: A → B → C |
| If/else branch | Single step with two output paths (success/error) |
| Try/catch with retry | Feedback loop (bounded, shrinking subset) |
| Resource acquire/release | Two states with invariant: acquired → must release on all paths |
| Callback/event handler | Trigger step with async terminal condition |
| State machine (explicit) | Direct mapping — each state becomes a step |

### When NOT to Extract

- **Pure functions with no side effects** — Just test them directly, no model needed
- **Trivial CRUD** — The model adds no insight over the code itself
- **Code you're replacing entirely** — Model the interface contract, not the internals
- **Third-party library internals** — Treat as opaque; model only what you call and what it returns

### Relationship to Other Commands

| Command | When to Use |
|---|---|
| `/research_codebase` | When you need to understand code but don't plan to change it |
| `/extract_tlaplus_model` | When you plan to change code and want to verify you don't break it |
| `/plan_path` | When building something new (greenfield) from a user story |
| `/create_tdd_plan` | After extraction — use the model as the behavioral spec for TDD |
| `/create_plan` | After extraction — use the model as constraint for implementation |

### Important Rules

- Read all files COMPLETELY before spawning sub-tasks (step 1)
- Wait for ALL sub-agents to complete before synthesizing (step 3)
- The model is a contract, not documentation — imprecision here becomes bugs later
- Always verify with `silmari verify-path` before handing off to planning
- Flag ambiguities explicitly — a wrong invariant is worse than a missing one
- The user confirms scope (step 1), model (step 3), and verification (step 5) before proceeding
