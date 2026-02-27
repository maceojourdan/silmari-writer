## Summary
- Adds end-to-end voice chat support using OpenAI Realtime over WebRTC with server-side session/token handling.
- Adds voice edit support and related UI/workflow updates for read-aloud and in-place voice-driven edits.
- Expands and hardens generation/tooling paths (deep research + tools orchestration + upload/transcription robustness).
- Includes OpenAI API compatibility fixes (unsupported parameter removal) and BAML version updates.

## What Changed
- Added/updated voice endpoints:
  - `POST /api/voice/session` (Realtime SDP proxy)
  - `POST /api/voice/edit` (voice instruction to edit request)
- Added/updated voice client logic and UI:
  - `useRealtimeSession`, `useVoiceEdit`, `useAutoReadAloud`
  - `AudioRecorder`, `VoiceEditPanel`, `ReadAloudToggle`, `VoiceSessionTimer`
  - store/type updates for voice state and message actions
- Improved generation/tool orchestration:
  - richer `/api/generate` handling
  - deep-research route updates and status handling
  - BAML integration retained in generate path; BAML version bumped
- Reliability and compatibility fixes:
  - fixed `getDownloadUrl` usage
  - fixed private blob upload handling and surfaced upload errors
  - removed unsupported OpenAI request parameters in relevant routes
  - assorted UI overflow/layout stability fixes

## Validation
- Attempted `npm test` in `frontend`: failed in this environment due executable permission issues (`vitest`/`esbuild` EACCES).
- Attempted `node node_modules/typescript/bin/tsc --noEmit`: currently failing with existing test/type mismatches on this branch.
- Attempted `npm run lint`: currently failing with existing lint errors on this branch.
- Added/updated a broad test surface for API routes, hooks, components, and libs aligned to this feature set.

## Notes
- Merged `origin/main` into this branch before PR creation.
- `bd` integration could not be synchronized in this environment (`Dolt backend configured but database not found`).
