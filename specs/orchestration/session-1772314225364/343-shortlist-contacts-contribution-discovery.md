# PATH: shortlist-contacts-contribution-discovery

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from voice-assisted-session-ui-ux.md — section 7 "Job-search acceleration layer" (lines 72-88) and "Short-list and network observability requirements" (lines 206-222)

## Purpose

Models the company short-list generation, contact discovery, and contribution-area discovery flows described in the UX spec section 7. These are outside the per-question voice session and support the broader job-search strategy. None of these flows exist in the current orchestration set.

## Trigger

User navigates to the job-search acceleration view after completing onboarding (candidate profile baseline exists).

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-m1n2` | acceleration_module | Contains the job-search acceleration UI with short-list, contacts, and contribution views |
| `ui-o3p4` | shortlist_component | Displays the company short-list and allows add/remove/reorder |
| `ui-q5r6` | contacts_component | Displays discovered contacts for a selected company |
| `ui-s7t8` | contribution_component | Displays contribution areas for a selected company |
| `api-u9v1` | shortlist_handler | Manages short-list generation and CRUD operations |
| `api-w2x3` | contacts_handler | Generates contact suggestions for a short-list company |
| `api-y4z5` | contribution_handler | Generates contribution-area suggestions based on candidate background and company context |
| `db-h2s4` | service | Orchestrates research generation and persistence |
| `db-d3w8` | data_access_object | Persists short-list, contacts, and contribution data |
| `db-l1c3` | backend_error_definitions | Defines error types for generation and persistence failures |
| `cfg-r3d7` | frontend_logging | Logs acceleration events for observability |

## Steps

1. **Generate company short-list**
   - Input: Candidate profile baseline (experience themes, domain areas, strengths) and optional user-provided company preferences.
   - Process: Analyze candidate background against market signals to suggest companies likely to be good fits. User can also manually add companies. Generate initial list via api-u9v1 (shortlist_handler). Emit `shortlist_generated` event.
   - Output: Ordered list of companies with brief rationale for each suggestion.
   - Error: If generation fails, display error and allow manual-only list building.

2. **Save and manage short-list**
   - Input: Generated or manually curated company list in ui-o3p4 (shortlist_component).
   - Process: User reviews suggestions, adds/removes companies, reorders by priority. Each save action persists via db-d3w8 (data_access_object). Emit `shortlist_company_saved` event per company with `company_id_or_name`.
   - Output: Persisted short-list of target companies.
   - Error: If persistence fails, display retry option. No data loss — changes remain in UI state until saved.

3. **Discover contribution areas for selected company**
   - Input: User selects a company from the short-list. Candidate profile baseline and company context forwarded to api-y4z5 (contribution_handler).
   - Process: Analyze intersection of candidate strengths and company needs (product areas, technology stack, team structure, recent initiatives). Generate contribution areas the candidate could credibly speak to. Emit `company_contribution_area_generated` event with `company_id_or_name`.
   - Output: List of contribution areas with brief descriptions, mapped to specific candidate experiences.
   - Error: If insufficient company context is available, return partial results with a note indicating what context is missing.

4. **Discover relevant contacts at selected company**
   - Input: User selects a company from the short-list. Company context and contribution areas forwarded to api-w2x3 (contacts_handler).
   - Process: Identify likely relevant people at the company: hiring managers, peers in target teams, recruiters, and adjacent team leads. Categorize contacts by role type and relevance to the candidate's contribution areas. Emit `company_contacts_suggested` event with `company_id_or_name`.
   - Output: Categorized list of contact suggestions with role, team, and relevance to the candidate's profile.
   - Error: If contact discovery yields no results, display a message suggesting alternative approaches (e.g., broader search, different team focus).

5. **Generate outreach drafts for contacts**
   - Input: Selected contact and associated contribution areas. Candidate profile baseline.
   - Process: Generate tailored outreach drafts (email or LinkedIn message) for each selected contact, grounding the message in the candidate's real experience and the contact's role/team. Each draft includes a talking points summary. Emit `outreach_draft_generated` event with `artifact_type=outreach`, `company_id_or_name`, `time_to_artifact_ms`.
   - Output: Outreach draft text with talking points, displayed with a conspicuous Copy button (per path 341).
   - Error: If generation fails, display error and allow manual drafting.

## Terminal Condition

User has a persisted short-list of target companies, with contribution areas and contact suggestions for reviewed companies, and outreach drafts available for selected contacts. All completed artifacts expose Copy buttons.

## Feedback Loops

User may iterate between steps 2-5: adjusting the short-list, exploring different companies, and generating outreach for different contacts. This is free-form navigation, not a bounded loop.

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | Short-list requires a candidate profile baseline to exist | spec:19-31 | TypeInvariant | Short-list generation fails with clear error if no profile baseline |
| INV-2 | Contact discovery is scoped to a single short-list company | spec:77 | TypeInvariant | Contacts always reference exactly one company_id |
| INV-3 | Contribution areas are grounded in candidate background, not generic | spec:76 | TypeInvariant | Every contribution area references at least one candidate experience theme |
| INV-4 | Outreach drafts reference real candidate experience, not generic templates | spec:78 | TypeInvariant | Draft text contains at least one specific detail from candidate profile |
| INV-5 | All completed text artifacts expose a Copy button | spec:85-88 | Reachability | Every outreach draft and contribution summary has a rendered Copy button |
| INV-6 | Every generation action emits an observability event | spec:206-222 | Reachability | At least one of: shortlist_generated, company_contacts_suggested, outreach_draft_generated is emitted per action |
