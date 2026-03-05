# Site Theme Update (Implementation Status)

- [x] 1. Create and claim a beads task for “Matsu theme integration”.
- [x] 2. Take a baseline screenshot pass of `/`, `/writer`, and `/session/[id]`.
- [x] 3. Update theme tokens in `frontend/src/app/globals.css` to Matsu semantic palette variables.
- [x] 4. Add Matsu base rules in `frontend/src/app/globals.css` (border weights, shadow utilities, texture utility).
- [x] 5. Add `texture.jpg` to `frontend/public` and point `.texture` to local `/texture.jpg`.
- [x] 6. Update `frontend/src/app/layout.tsx` to load Nunito + PT Serif and render `<div className="texture" />`.
- [x] 7. Keep dark mode behavior explicit with a single consistent token approach.
- [x] 8. Port existing UI primitives to Matsu styles without changing their public APIs (`button`, `badge`, `card`, `textarea`, `separator`, `scroll-area`).
- [x] 9. Standardize heading typography with `font-serif` on key shell/card titles.
- [x] 10. Replace hard-coded color utilities in production components with semantic tokens (test/debug pages deferred).
- [x] 11. Refactor modal styling in `EditMessageModal.tsx` to semantic theme classes and primitives.
- [x] 12. Refactor primary session/workflow status styles to semantic theme colors.
- [x] 13. Leave internal test/debug pages (`/test-*`) as follow-up work.
- [x] 14. Run static checks in `frontend`: `npm run lint` and `npm run type-check`.
  - `type-check`: pass
  - `lint`: fails due large pre-existing repo baseline issues (not introduced by this theme pass)
- [x] 15. Run tests in `frontend`: `npm test` plus targeted e2e.
  - `npm test`: pass (`450` files, `4091` tests passed)
  - `npm run test:e2e`: conversation-flow suite fails on pre-existing selector assumption (`My First Project`)
- [x] 16. Perform manual QA on desktop and mobile breakpoints for `/`, `/writer`, `/session/[id]`.
  - After screenshots captured under `artifacts/theme-after/`
- [x] 17. Create follow-up beads issues for deferred items.
  - `silmari-writer-an8`: Theme test/debug pages to Matsu tokens
  - `silmari-writer-bt9`: Fix conversation-flow e2e assumptions for project naming
  - `silmari-writer-3v3`: Expand Matsu styling across remaining shadcn primitives
- [x] 18. Close the beads task, run sync/push workflow, and confirm repo is up to date.
  - Closed `silmari-writer-5wg`
  - Ran: `git pull --rebase`, `bd dolt push`, `bd dolt pull`, `git push`, `git push github-maceo main`

## Definition of Done

- [x] Core routes visually align with the Matsu style direction.
- [ ] No regressions in lint/type/test gates.
  - `type-check` and `npm test` are green.
  - `lint` and conversation-flow e2e currently fail due pre-existing baseline issues.
- [x] Theme is token-driven across production UI paths (no remaining hard-coded palette in non-test routes).
