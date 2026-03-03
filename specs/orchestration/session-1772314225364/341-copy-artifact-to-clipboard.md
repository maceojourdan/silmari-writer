# PATH: copy-artifact-to-clipboard

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from voice-assisted-session-ui-ux.md — "Copy-first UX rule" (lines 85-88) and "Short-list and network observability requirements" (lines 206-222)

## Purpose

Extends copy-to-clipboard coverage beyond finalized answers (covered by path 334) to all completed text artifacts: outreach drafts, LinkedIn post drafts, application answers, and summary notes. The existing path 334 only covers finalized answer export/copy. This path models the universal copy action available on any completed artifact.

## Trigger

User taps the Copy button on any completed text artifact displayed in the UI.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-a2b3` | artifact_display | Renders any completed text artifact with a conspicuous Copy button |
| `ui-c4d5` | clipboard_handler | Executes clipboard write and provides immediate visual confirmation |
| `cfg-j9w2` | shared_error_definitions | Provides cross-layer error definitions for clipboard failures |
| `cfg-r3d7` | frontend_logging | Logs copy success/failure events for observability |

## Steps

1. **Render artifact with Copy button**
   - Input: Completed text artifact loaded in ui-a2b3 (artifact_display). Artifact types: `answer`, `outreach`, `linkedin_post`, `summary`.
   - Process: Validate that the artifact is in a completed state (not draft-in-progress). Render the artifact text with a conspicuous Copy button adjacent to the content.
   - Output: Artifact displayed with visible, accessible Copy button.
   - Error: If the artifact is not in completed state, the Copy button is hidden or disabled — no error displayed.

2. **Execute clipboard write**
   - Input: User tap on Copy button, artifact content, and artifact metadata (type, id) from ui-a2b3 (artifact_display) forwarded to ui-c4d5 (clipboard_handler).
   - Process: Write the full artifact text content to the system clipboard. Apply no transformations — the clipboard receives exactly the rendered text.
   - Output: Artifact text written to system clipboard. Emit `artifact_copied_to_clipboard` event with fields: `artifact_type`, `copy_success=true`, `session_id`, `user_id`.
   - Error: If clipboard write fails (browser permissions, secure context), display a user-facing error via cfg-j9w2 (shared_error_definitions), log via cfg-r3d7 (frontend_logging), and emit `artifact_copied_to_clipboard` with `copy_success=false`.

3. **Provide immediate visual confirmation**
   - Input: Clipboard write result from ui-c4d5 (clipboard_handler).
   - Process: On success, display a brief visual confirmation (e.g., button text changes to "Copied!" with a checkmark, returns to "Copy" after 2 seconds). On failure, display an error toast.
   - Output: User sees immediate visual feedback confirming the copy action succeeded or failed.
   - Error: None — this step always completes.

## Terminal Condition

User sees a visual confirmation that the artifact text has been copied to the clipboard. The `artifact_copied_to_clipboard` observability event has been emitted.

## Feedback Loops

None — strictly linear.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | Every completed text artifact exposes a conspicuous Copy button | spec:86-87 | Reachability | Copy button is rendered for all artifact types: answer, outreach, linkedin_post, summary |
| INV-2 | Copy action always provides immediate visual confirmation | spec:88 | Reachability | Visual feedback is displayed within 500ms of tap, for both success and failure |
| INV-3 | Clipboard receives the exact rendered text with no transformations | spec:85-88 | TypeInvariant | Clipboard content equals artifact text content verbatim |
| INV-4 | Every copy action emits an observability event | spec:214 | Reachability | `artifact_copied_to_clipboard` event exists for every copy button tap |
| INV-5 | Copy button is never shown on draft-in-progress artifacts | spec:85 | ErrorConsistency | Incomplete artifacts have no Copy button rendered |
