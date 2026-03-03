## Plan Review Report: thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md

### Review Summary
| Category | Status | Issues Found |
|----------|--------|--------------|
| Contracts | ❌ | 5 |
| Interfaces | ❌ | 4 |
| Promises | ⚠️ | 3 |
| Data Models | ❌ | 4 |
| APIs | ❌ | 4 |

### Contract Review
#### Well-Defined
- ✅ Behavior slices are explicit and test-first (`Behavior 1..9`) with Red/Green/Refactor structure.
- ✅ Existing path references are grounded to 340-345 specs and existing 293-339 architecture anchors.

#### Missing or Unclear
- ❌ **Path 340 contract mismatch (wrong initialization pipeline)**
  - Plan proposes `SessionInitializationService.initializeSession(userId)` in Behavior 2 ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:147](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:147)).
  - Path 340 requires channel URL to feed the standard initialization path 310 and end in `initialized` state ([340-ingest-url-via-email-or-sms-channel.md:52](specs/orchestration/session-1772314225364/340-ingest-url-via-email-or-sms-channel.md:52), [340-ingest-url-via-email-or-sms-channel.md:64](specs/orchestration/session-1772314225364/340-ingest-url-via-email-or-sms-channel.md:64)).
  - Existing `SessionInitializationService` returns `INIT` answer_session semantics, not `initialized` session semantics ([SessionInitializationService.ts:31](frontend/src/server/services/SessionInitializationService.ts:31), [SessionInitializationService.ts:84](frontend/src/server/services/SessionInitializationService.ts:84)).
- ❌ **Channel ingestion contract is missing outbound reply boundary**
  - Plan mentions deep-link payload only ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:137](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:137), [2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:149](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:149)), but path 340 requires replying on origin channel with summary and non-blocking notification failure handling ([340-ingest-url-via-email-or-sms-channel.md:56](specs/orchestration/session-1772314225364/340-ingest-url-via-email-or-sms-channel.md:56), [340-ingest-url-via-email-or-sms-channel.md:60](specs/orchestration/session-1772314225364/340-ingest-url-via-email-or-sms-channel.md:60)).
- ❌ **Idempotency contract is not explicit**
  - Duplicate URL handling is listed as edge case ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:131](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:131)) and helper is hinted ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:155](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:155)), but no canonical idempotency key/store contract is defined.
- ⚠️ **Universal copy contract lacks completion-state definition per artifact**
  - Behavior 3 assumes a generic `completed` boolean ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:182](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:182)), but no shared artifact status contract exists.
- ⚠️ **Interstitial stage authority is ambiguous vs existing shell state override**
  - Plan wraps shell with interstitial controller ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:413](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:413)), while shell already has stage override logic ([SessionWorkflowShell.tsx:63](frontend/src/modules/session/SessionWorkflowShell.tsx:63)). Source-of-truth precedence is not specified.

#### Recommendations
- Define `ChannelIngestionPipelineAdapter` contract that transforms extracted URL into path 310 objects and invokes initialize-session flow (not answer-session bootstrap flow).
- Define `ChannelReplySender` contract with required payload fields and non-blocking failure behavior.
- Add explicit idempotency contract: `canonical_url + user_id` and provider message id dedupe.
- Add artifact union contract with explicit `status` semantics driving copy visibility.
- Define interstitial transition contract relative to backend-derived stage updates and existing `stageOverride` semantics.

---

### Interface Review
#### Well-Defined
- ✅ Proposed file-level decomposition (handler/service/module split) generally follows current code organization patterns.

#### Missing or Unclear
- ❌ **No API contract layer specified for new endpoints**
  - New routes are listed (e.g., shortlist/contribution/contacts/linkedin drafts) ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:280](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:280), [2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:321](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:321), [2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:367](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:367)), but no corresponding `frontend/src/api_contracts/*` additions are planned.
- ❌ **Auth interface omitted for user-scoped new APIs**
  - Plan does not specify auth header/context handling for new route groups, unlike existing protected endpoints ([frontend/src/app/api/sessions/route.ts:23](frontend/src/app/api/sessions/route.ts:23)).
- ⚠️ **Provider adapters are implied but not defined**
  - Email/SMS ingress, LinkedIn parser/connect, and contact discovery are planned with mocks ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:67](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:67)), but interface boundaries are missing.
- ⚠️ **Event logger interface placement is inconsistent with current path loggers**
  - New central logger is proposed ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:456](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:456)); existing code uses path-scoped loggers (`onboardingLogger`, `kpiLogger`).

#### Recommendations
- Add API contract files and tests for every new route group before route implementation.
- Add an auth strategy section for each new endpoint (required/optional/service-auth).
- Define provider interfaces: `InboundChannelReceiver`, `LinkedInAuthClient`, `CompanyDiscoveryClient`.
- Decide whether new events use path-specific loggers or a shared typed telemetry gateway.

---

### Promise Review
#### Well-Defined
- ✅ Interstitial minimum display behavior is testable with fake timers ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:403](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:403)).
- ✅ Notification failure is called out as non-blocking in channel flow edge cases.

#### Missing or Unclear
- ❌ **OAuth security promises are underspecified**
  - Callback route is planned ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:238](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:238)) but no explicit promises for `state` verification, token encryption-at-rest, token TTL/refresh/revocation, or log redaction.
- ⚠️ **Abandonment telemetry promise lacks reliability semantics**
  - Path 345 includes unload abandonment; plan does not define fallbacks when `unload` events are dropped.
- ⚠️ **No timeout/cancellation policy for discovery/generation fan-out**
  - Behaviors 5-7 introduce multiple remote-like operations but no latency or cancellation guarantees per action.

#### Recommendations
- Add explicit OAuth security contract with required checks and storage guarantees.
- Add telemetry reliability notes (`sendBeacon` fallback, best-effort semantics).
- Add timeout/cancellation contracts for shortlist/contact/draft generation with user-visible degraded modes.

---

### Data Model Review
#### Well-Defined
- ✅ Existing onboarding and KPI models are reusable for some telemetry patterns.

#### Missing or Unclear
- ❌ **No schema/migration plan for new persisted entities**
  - Plan commits to persistence for shortlist, contacts, contribution areas, outreach/linkedin drafts ([2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:264](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:264), [2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:306](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:306), [2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:349](thoughts/searchable/shared/plans/2026-03-03--07-51--tdd-voice-assisted-session-ui-ux-orchestration-340-345.md:349)).
  - Current DB schema has no dedicated tables for these domains ([20260302000000_initial_schema.sql:96](supabase/migrations/20260302000000_initial_schema.sql:96), [20260302000000_initial_schema.sql:110](supabase/migrations/20260302000000_initial_schema.sql:110), [20260302000000_initial_schema.sql:220](supabase/migrations/20260302000000_initial_schema.sql:220)).
- ❌ **No LinkedIn connection/token model**
  - Path 342 requires secure token handling ([342-linkedin-onboarding-connect-flow.md:76](specs/orchestration/session-1772314225364/342-linkedin-onboarding-connect-flow.md:76)); plan has no token schema/table or lifecycle fields.
- ⚠️ **No canonical event schema integration path**
  - New event schemas are proposed but not mapped to existing analytics storage (`analytics_events`/`primary_kpi_events`) or a separate sink.
- ⚠️ **No uniqueness constraints specified**
  - Shortlist dedupe, URL dedupe, and draft uniqueness keys are not defined.

#### Recommendations
- Add a dedicated data-model section listing all new entities, keys, FKs, required fields, and migrations.
- Add DB constraints/indexes for dedupe (`user_id + canonical_url`, `user_id + company_id`, etc.).
- Add token storage model with encryption metadata and expiration fields.

---

### API Review
#### Well-Defined
- ✅ The plan clearly identifies endpoint groups by behavior and includes route-level tests.

#### Missing or Unclear
- ❌ **Path 340 API behavior does not include reply-channel contract**
  - Path requires channel reply and deep link summary; plan only asserts JSON route response in route test.
- ❌ **No per-endpoint request/response/error schemas listed**
  - New routes are proposed without status-code/error matrix and Zod schema references.
- ❌ **No versioning or rollout strategy for new endpoint families**
  - `api/acceleration/*`, `api/linkedin/*`, `api/ingestion/channel` are introduced without compatibility strategy.
- ⚠️ **No explicit authorization policy for shortlist/contact/linkedin draft endpoints**
  - Sensitive profile/company data is user-scoped; access policy should be explicit in the plan.

#### Recommendations
- For each new endpoint, define request schema, response schema, error schema, and auth requirement.
- Add route contract tests mirroring existing `api_contracts` patterns.
- Add rollout/versioning notes (feature flags or prefixed path versioning).

---

### Critical Issues (Must Address Before Implementation)
1. **Contract mismatch for Path 340 pipeline target**
   - Impact: Channel-ingested URLs will create wrong session type/state (`INIT` answer_session) and violate path invariants requiring parity with paste-initialized flow.
   - Recommendation: Route channel ingestion into path-310-compatible initialization adapter producing `initialized` sessions from structured objects.

2. **Missing data model and migration strategy for 342-344 persistence**
   - Impact: Implementation will either stall or create ad-hoc, inconsistent persistence; invariants about persisted shortlist/contribution/drafts cannot be validated.
   - Recommendation: Add explicit schema/migration plan before any route/module work.

3. **OAuth security contract incomplete**
   - Impact: Risk of token exposure, CSRF vulnerabilities, and inability to prove “server-only token” invariant.
   - Recommendation: Add state/nonce, token storage encryption contract, redaction rules, expiry/refresh/revoke behavior, and tests.

4. **AuthN/AuthZ undefined for new user-scoped endpoints**
   - Impact: Potential cross-user data exposure and unauthorized data mutation.
   - Recommendation: Define and test auth requirements per endpoint before implementation.

### Suggested Plan Amendments
```diff
# In "Behavior 2: Channel URL -> Session Init + Notification Contract"

- const session = await SessionInitializationService.initializeSession(result.userId);
+ const initialized = await ChannelIngestionPipelineAdapter.initializeFromUrl({
+   userId: result.userId,
+   sourceUrl: result.url,
+   channel: result.channel,
+ });
+ await ChannelReplySender.sendSuccess({
+   channel: result.channel,
+   recipient: result.sender,
+   deepLink: `/session/${initialized.id}`,
+   contextSummary: initialized.contextSummary,
+ });

# Add new section before Behavior 4
+ ## Data Model & Migration Plan (Required Before Code)
+ - candidate_profile_baselines
+ - linkedin_connections (server-only token envelope)
+ - company_shortlists + shortlist_items
+ - company_contribution_areas
+ - company_contact_suggestions
+ - outreach_drafts
+ - linkedin_post_drafts
+ - ingestion_messages (dedupe + status)
+ - indexes/uniqueness constraints and FK strategy

# In Behavior 4 (LinkedIn OAuth)
+ Add explicit OAuth security sub-contract:
+ - require OAuth state/nonce verification
+ - store access/refresh token server-side encrypted
+ - never return token fields in API responses
+ - redact token values from logs
+ - define token expiry/refresh/revoke semantics

# In Behaviors 5-7 (new endpoints)
+ Add API contract files in frontend/src/api_contracts/* with Zod request/response/error schemas.
+ Add explicit auth requirements and error codes per endpoint.

# In Behavior 9 (Observability)
+ Define event sink contract:
+ - where events are persisted/sent
+ - retry/backpressure behavior
+ - relationship to existing analytics_events and primary_kpi_events
```

### Approval Status
- [ ] **Ready for Implementation** - No critical issues
- [ ] **Needs Minor Revision** - Address warnings before proceeding
- [x] **Needs Major Revision** - Critical issues must be resolved first
