# PATH: linkedin-content-planning-workflow

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from voice-assisted-session-ui-ux.md — section 7 items 5-6 (lines 79-84) and "Short-list and network observability requirements" (lines 206-222)

## Purpose

Models the LinkedIn content planning workflow tied to short-list companies. The system generates LinkedIn post drafts mapped to contribution areas and company themes but never posts on the user's behalf. This path covers the content generation, manual-post-only safeguards, and the copy-to-clipboard UX for LinkedIn drafts.

## Trigger

User navigates to LinkedIn content planning for a short-list company that has contribution areas already generated (path 343 step 3 completed).

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-a1b1` | linkedin_planning_module | Contains the LinkedIn content planning view |
| `ui-c2d2` | post_draft_component | Displays generated LinkedIn post drafts with Copy button and manual-post reminder |
| `api-e3f3` | linkedin_draft_handler | Generates LinkedIn post drafts from contribution areas and candidate profile |
| `db-h2s4` | service | Orchestrates draft generation and persistence |
| `db-d3w8` | data_access_object | Persists generated drafts |
| `db-l1c3` | backend_error_definitions | Defines error types for generation failures |
| `cfg-r3d7` | frontend_logging | Logs LinkedIn planning events |

## Steps

1. **Select company and contribution areas for LinkedIn content**
   - Input: User selects a short-list company in ui-a1b1 (linkedin_planning_module). The company has contribution areas available from path 343.
   - Process: Load the company's contribution areas and the candidate's profile baseline. Present the areas as content themes the user can select for LinkedIn post generation.
   - Output: Selected contribution areas as content themes for draft generation.
   - Error: If no contribution areas exist for the company, prompt user to generate them first (redirect to path 343 step 3).

2. **Generate LinkedIn post drafts**
   - Input: Selected contribution areas, candidate profile baseline, and company context forwarded to api-e3f3 (linkedin_draft_handler).
   - Process: Generate one or more LinkedIn post drafts per selected contribution area. Each draft is grounded in the candidate's real experience and framed around the company's theme. Drafts are written in the candidate's natural voice (informed by onboarding data). Emit `linkedin_post_draft_generated` event with `artifact_type=linkedin_post`, `company_id_or_name`, `time_to_artifact_ms`.
   - Output: LinkedIn post draft texts, each tagged with the contribution area and company.
   - Error: If generation fails, display error and allow retry.

3. **Display drafts with manual-post-only safeguard**
   - Input: Generated drafts rendered in ui-c2d2 (post_draft_component).
   - Process: Display each draft with: (a) the full post text, (b) a conspicuous Copy button (per path 341), (c) a clear reminder that "This is a draft for you to post manually — we will never post on your behalf." The UI must not include any "Post" or "Publish" button. No API integration to LinkedIn's posting endpoints exists.
   - Output: User sees drafts with Copy buttons and manual-post reminder.
   - Error: None — display step always completes.

4. **User copies draft to clipboard**
   - Input: User taps Copy on a draft. Delegated to path 341 (copy-artifact-to-clipboard) with `artifact_type=linkedin_post`.
   - Process: Path 341 handles clipboard write and visual confirmation.
   - Output: Draft text in clipboard, ready for manual paste into LinkedIn.
   - Error: Handled by path 341.

## Terminal Condition

User has one or more LinkedIn post drafts copied to clipboard, ready to manually post on LinkedIn. The system has never automated any posting action. Manual-post-only reminder was displayed.

## Feedback Loops

User may generate drafts for multiple contribution areas or companies in sequence. This is free-form navigation, not a bounded loop.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | The system never posts to LinkedIn on the user's behalf | spec:81-83 | TypeInvariant | No LinkedIn posting API call exists in any code path; no "Post" or "Publish" button is rendered |
| INV-2 | Every draft display includes a manual-post-only reminder | spec:81-83 | Reachability | Reminder text is present in every post_draft_component render |
| INV-3 | Drafts are grounded in candidate experience, not generic | spec:79 | TypeInvariant | Draft text references at least one specific candidate experience or contribution area |
| INV-4 | Drafts are tied to specific company themes | spec:79 | TypeInvariant | Each draft references a company_id and contribution_area_id |
| INV-5 | Every draft exposes a Copy button | spec:85-88 | Reachability | Copy button rendered for every generated draft |
| INV-6 | Every draft generation emits an observability event | spec:213 | Reachability | `linkedin_post_draft_generated` event emitted per draft |
