# Agent Instructions

This project uses **bd** (beads) for issue tracking. Run `bd onboard` to get started.

## Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --status in_progress  # Claim work
bd close <id>         # Complete work
bd sync               # Sync with git
```

## Voice & API Architecture

### API Endpoints & Models
| Endpoint | Model | Notes |
|----------|-------|-------|
| `/api/transcribe` | `whisper-1` | Audio → text via OpenAI SDK |
| `/api/generate` | `gpt-4o-mini` | Chat completions, imports BAML client (critical infra) |
| `/api/voice/session` | `gpt-4o-realtime-preview` | WebRTC SDP proxy to `api.openai.com/v1/realtime/calls` |
| `/api/voice/edit` | `gpt-4o-mini` | Processes voice edit instructions |
| `/api/tools/document-generation` | `gpt-4o` (default) | Also supports `gpt-4o-mini`, `gpt-4-turbo` |
| `/api/tools/intent-classification` | `gpt-4o-mini` | Intent classification |
| `/api/tools/deep-research` | OpenAI Responses API | Deep research with web search |

### Voice Flow (Read Aloud / Voice Edit)
- Client creates WebRTC peer connection + SDP offer (`voice-session.ts`)
- SDP is sent to `/api/voice/session` which proxies to OpenAI Realtime API with server-side API key
- OpenAI returns SDP answer; client sets remote description
- Data channel (`oai-events`) used for session config and events
- **No client-side code calls OpenAI directly** — all auth is server-side

### Known Gotchas
- All API routes use `process.env.OPENAI_API_KEY` (single key, must have Realtime API access for voice)
- BAML client is imported in `/api/generate` — do NOT remove, it's critical infrastructure
- `next.config.ts` has `removeConsole` in production — Vercel logs will have empty messages, making debugging harder
- BAML version in `generators.baml` must match installed `@boundaryml/baml` package version

### Git Configuration
- Repo uses `maceojourdan / me@maceojourdan.com` for commits
- Two remotes: `origin` (tha-hammer) and `github-maceo` (maceojourdan) — push to both

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
5. **Clean up** - Clear stashes, prune remote branches
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds

