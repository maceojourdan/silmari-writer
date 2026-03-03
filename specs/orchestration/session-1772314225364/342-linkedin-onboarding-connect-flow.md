# PATH: linkedin-onboarding-connect-flow

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1
**Source:** Extracted from voice-assisted-session-ui-ux.md — section 1 "Onboarding first" (lines 19-32) and "Onboarding observability requirements" (lines 188-204)

## Purpose

Models the optional LinkedIn account connect flow during onboarding. The existing onboarding paths cover resume upload and basic session initialization. This path covers the OAuth-style LinkedIn connect flow and the fallback to manual entry when URL parsing fails, which are specified in the UX spec but not modeled.

## Trigger

User selects the "Connect LinkedIn" option during onboarding, or LinkedIn URL parsing fails and the user is prompted for manual entry.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-e6f7` | onboarding_module | Contains the onboarding UI flow with LinkedIn input options |
| `ui-g8h9` | linkedin_input_component | Presents URL paste, manual entry, and OAuth connect options |
| `api-i1j2` | linkedin_oauth_handler | Manages the OAuth redirect, authorization code exchange, and token storage |
| `api-k3l4` | linkedin_profile_parser | Extracts profile data from LinkedIn API using access token or from URL scrape |
| `db-h2s4` | service | Stores the parsed profile data as part of the candidate baseline |
| `db-d3w8` | data_access_object | Persists candidate profile to storage |
| `db-l1c3` | backend_error_definitions | Defines error types for OAuth, parsing, and storage failures |
| `cfg-r3d7` | frontend_logging | Logs onboarding events for observability |

## Steps

1. **Present LinkedIn input options**
   - Input: User reaches the LinkedIn step in onboarding at ui-e6f7 (onboarding_module).
   - Process: Display three input options: (a) paste LinkedIn profile URL, (b) enter profile details manually, (c) connect LinkedIn account via OAuth. All three are optional — the user may skip this step entirely.
   - Output: User selects one of the three input modes, or skips.
   - Error: None — all options are valid, including skip.

2. **Handle URL paste and parse**
   - Input: User pastes a LinkedIn profile URL into ui-g8h9 (linkedin_input_component).
   - Process: Send the URL to api-k3l4 (linkedin_profile_parser) for extraction. Emit `linkedin_url_submitted` event. Parse public profile data (experience themes, job titles, skills, education).
   - Output: Parsed profile data with `linkedin_input_mode=url`. Emit `linkedin_profile_parsed` event.
   - Error: If URL parsing fails (private profile, anti-scrape block, invalid URL), prompt user to switch to manual entry or OAuth connect. Emit event with `error_code`.

3. **Handle manual profile entry**
   - Input: User enters profile details manually in ui-g8h9 (linkedin_input_component) — job titles, companies, skills, years of experience.
   - Process: Validate that at least one meaningful field is provided. Structure the input as a candidate profile baseline with `linkedin_input_mode=manual`.
   - Output: Manually entered profile data, validated and structured.
   - Error: If no meaningful fields are provided, display a prompt to enter at least one field or skip.

4. **Handle OAuth connect flow**
   - Input: User clicks "Connect LinkedIn" in ui-g8h9 (linkedin_input_component). Emit `linkedin_connect_started` event.
   - Process: Redirect user to LinkedIn OAuth authorization page via api-i1j2 (linkedin_oauth_handler). On return, exchange authorization code for access token. Use token to fetch full profile data via LinkedIn API through api-k3l4 (linkedin_profile_parser).
   - Output: Full profile data from LinkedIn API with `linkedin_input_mode=connected`. Access token stored securely. Emit `linkedin_connect_completed` event.
   - Error: If OAuth fails (user denies, token exchange fails, API rate limit), display error and offer fallback to URL paste or manual entry. Emit event with `error_code`.

5. **Store candidate profile baseline**
   - Input: Parsed profile data (from any input mode) forwarded to db-h2s4 (service).
   - Process: Merge LinkedIn profile data with any existing resume-derived profile data. Generate story seeds and suggested contribution themes from the combined profile. Persist via db-d3w8 (data_access_object).
   - Output: Complete candidate profile baseline with experience themes, strengths, domain areas, story seeds, and contribution themes. Emit `onboarding_completed` event with `onboarding_time_ms`.
   - Error: If persistence fails, return error via db-l1c3 (backend_error_definitions). Profile data is not lost — retry is possible.

## Terminal Condition

Candidate profile baseline is persisted with LinkedIn-derived data (from URL, manual entry, or OAuth connect). Reusable story seeds and suggested contribution themes are generated and available for later voice sessions.

## Feedback Loops

URL parse failure → fallback to manual entry or OAuth connect (single retry path, not a loop).

## Extracted Invariants

| ID | Invariant | Source | TLA+ Property | Test Oracle |
|----|-----------|--------|---------------|-------------|
| INV-1 | LinkedIn input is always optional — user can skip and still complete onboarding | spec:26 | Reachability | Onboarding completes successfully with no LinkedIn data |
| INV-2 | Three input modes are mutually exclusive per attempt: url, manual, connected | spec:24-26 | TypeInvariant | `linkedin_input_mode` is always exactly one of: url, manual, connected, or null (skipped) |
| INV-3 | URL parse failure always offers fallback to manual or OAuth | spec:25 | Reachability | After URL parse failure, manual and OAuth options are presented |
| INV-4 | OAuth access tokens are stored securely and never exposed to the frontend | spec:26 | TypeInvariant | Token is persisted server-side only, never in frontend state or logs |
| INV-5 | Profile merge never overwrites resume-derived data with empty LinkedIn fields | spec:28-31 | TypeInvariant | Merged profile retains all resume fields; LinkedIn fields augment, not replace |
| INV-6 | Every LinkedIn input attempt emits an observability event | spec:188-204 | Reachability | At least one of: linkedin_url_submitted, linkedin_connect_started, or onboarding_completed is emitted |
