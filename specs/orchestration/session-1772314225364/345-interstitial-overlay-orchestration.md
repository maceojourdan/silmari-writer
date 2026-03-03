# PATH: interstitial-overlay-orchestration

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from voice-assisted-session-ui-ux.md — "Interstitial steps to reduce blocked feeling" (lines 90-110) and "Interstitial observability requirements" (lines 224-236)

## Purpose

Models interstitial overlays as a first-class orchestration flow rather than ad-hoc UI decoration. The UX spec defines interstitials at key transition points between stages. This path specifies when they appear, what they contain, how they behave, and how they are instrumented. The existing orchestration set has no interstitial modeling.

## Trigger

The session state machine transitions between major stages: ingestion → entry, entry → recall, recall → verification, verification → draft.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-h1i2` | interstitial_controller | Manages interstitial display lifecycle: show, dwell, dismiss, continue |
| `ui-j3k4` | interstitial_content | Contains copy/content for each interstitial type |
| `ui-l5m6` | progress_indicator | Renders step name and progress within the interstitial overlay |
| `cfg-r3d7` | frontend_logging | Logs interstitial observability events |
| `cfg-j9w2` | shared_error_definitions | Provides error definitions for edge cases |

## Steps

1. **Detect stage transition**
   - Input: Session state change event (e.g., INGESTED → SESSION_STARTED, ORIENT_CONFIRMED → RECALL, RECALL_COMPLETED → VERIFICATION_PASSED).
   - Process: Map the state transition to an interstitial type: `after_ingestion`, `before_voice_recall`, `before_verification_draft`. Not all transitions require an interstitial — only the transitions defined in the spec.
   - Output: Interstitial type and associated content, or no-op if the transition does not require one.
   - Error: If the transition is unrecognized, skip interstitial and proceed directly to the next stage.

2. **Show interstitial overlay**
   - Input: Interstitial type and content from ui-j3k4 (interstitial_content), rendered by ui-h1i2 (interstitial_controller).
   - Process: Display a static overlay with: (a) explanation of what is happening now, (b) explanation of why this step improves outcomes, (c) reinforcement that the process builds truthful answers, (d) step name and progress indicator via ui-l5m6 (progress_indicator), (e) a clear continue/wait affordance. Emit `interstitial_shown` event with `interstitial_type`, `step_before`, `step_after`.
   - Output: Overlay visible to the user with forward-motion progress indicator.
   - Error: If content is missing for this interstitial type, show a minimal progress-only overlay and log via cfg-r3d7.

3. **Track dwell and dismissal**
   - Input: User interaction with the interstitial (wait for background processing to complete, or explicit continue action).
   - Process: Track dwell time from show to dismissal. Determine whether dismissal was automatic (processing completed) or manual (user tapped continue). Record `cta_action` (continue, wait, or auto-advance).
   - Output: Emit `interstitial_dismissed_or_continued` event with `dwell_ms`, `cta_action`, `interstitial_type`.
   - Error: None — dismissal always succeeds.

4. **Handle abandonment**
   - Input: User navigates away or closes the app during an active interstitial.
   - Process: Detect abandonment (page unload, back navigation, app backgrounding). Emit `interstitial_abandonment` event with `interstitial_type`, `step_before`, `dwell_ms`.
   - Output: Session state is preserved — user can return to the same point.
   - Error: If abandonment detection fails (e.g., abrupt process kill), the event is lost but session state is still preserved.

5. **Advance to next stage**
   - Input: Interstitial dismissed (step 3) or background processing completed.
   - Process: Remove the overlay and transition the UI to the next stage. The interstitial must never block forward progress indefinitely — if background processing completes during the overlay, auto-advance after a brief minimum display time (e.g., 1.5 seconds) to ensure the user sees the message.
   - Output: UI displays the next stage. The interstitial is no longer visible.
   - Error: If the next stage fails to load, display an error using cfg-j9w2 (shared_error_definitions), not the interstitial.

## Terminal Condition

The interstitial overlay has been shown, the user has either waited or continued, and the UI has advanced to the next stage. Observability events for the interstitial lifecycle have been emitted.

## Feedback Loops

None — strictly linear per interstitial. Multiple interstitials occur at different stage transitions but each is independent.

## Interstitial Content Definitions

| Type | When | Message | Why-statement |
|------|------|---------|---------------|
| `after_ingestion` | Ingestion starts | "We are reading the application context so you do not need to rewrite your story from scratch." | Reduces rewrite anxiety |
| `before_voice_recall` | Before voice recall begins | "Strong interview answers combine clear actions, measurable impact, and context. We will guide you to all three." | Sets expectations for the interrogation |
| `before_verification_draft` | Before verification/draft | "We only draft from confirmed details to avoid generic AI language and protect credibility." | Reinforces trust and anti-slop commitment |

## UX Rules (from spec)

1. Keep overlays short, calm, and confidence-building.
2. Never present them as error states.
3. Always show visible forward motion (step name + progress indicator).
4. Provide a clear continue/wait affordance.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | Interstitials are never presented as error states | spec:108 | TypeInvariant | Overlay styling uses informational/progress treatment, never error colors or icons |
| INV-2 | Every interstitial shows a progress indicator | spec:109 | Reachability | Progress indicator element is rendered in every interstitial overlay |
| INV-3 | Interstitials never block forward progress indefinitely | spec:110 | Reachability | Auto-advance fires after background processing + minimum display time |
| INV-4 | Abandonment preserves session state | spec:90-96 | TypeInvariant | Session state is unchanged after abandonment — user can resume |
| INV-5 | Every interstitial lifecycle emits at least one observability event | spec:224-236 | Reachability | `interstitial_shown` event exists for every displayed overlay |
| INV-6 | Minimum display time prevents flash of content | step 5 | TypeInvariant | Overlay is displayed for at least 1.5 seconds even if processing completes instantly |
