# R04/R08 successor-pair activation

- Activation time (RFC3339 UTC): `2026-08-17T13:18:09Z`.
- Activation authority: `primary-human`, exercising the authorized branch-registry, new-ref, named-worktree, activation-control, main commit/push, and CI-monitoring controls.
- Planned-control commit: `2d9dbf7bf8b4b51e9cb7817f5c5dc2d5194e8c42`.
- Planned-control Lean CI: run `32030191197`, build job `95388234941`, exact head `2d9dbf7bf8b4b51e9cb7817f5c5dc2d5194e8c42`, conclusion `success`.
- Immutable worker base: checkpoint `C0004`, commit `783ae9a4951407ece046adb8631d5a8ff1795a18`.
- C0004 raw dependency graph SHA-256: `98C9C0CA7266A7CF295A27D5D119903F0EF239349F3FBC6C57F29BE9FBF602AB`.

## Activated branch identities

| Branch ID | Wave | Assignment | Branch | Local tip | Remote ref | Remote tip | Named worktree | Worktree HEAD | Lane | Recorded operators | Implementation operator after activation CI |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `B0008` | `R04` | Codex | `codex/reorg-completion-2026-08-r04-cholesky-higham-ch10` | `783ae9a4951407ece046adb8631d5a8ff1795a18` | `refs/heads/codex/reorg-completion-2026-08-r04-cholesky-higham-ch10` | `783ae9a4951407ece046adb8631d5a8ff1795a18` | `C:\Users\qed_s\higham-worktrees\completion-r04-codex` | `783ae9a4951407ece046adb8631d5a8ff1795a18` | `claude-lane` | `["claude-local", "codex-local"]` | `claude-local` |
| `B0009` | `R08` | Claude exclusively | `codex/reorg-completion-2026-08-r08-matrix-inversion-ch14` | `783ae9a4951407ece046adb8631d5a8ff1795a18` | `refs/heads/codex/reorg-completion-2026-08-r08-matrix-inversion-ch14` | `783ae9a4951407ece046adb8631d5a8ff1795a18` | `C:\Users\qed_s\higham-worktrees\completion-r08-claude` | `783ae9a4951407ece046adb8631d5a8ff1795a18` | `claude-lane` | `["claude-local"]` | `claude-local` |

Both local branches were created explicitly at exact C0004, never at the planned-control commit. Both remote refs were created in one atomic push with these explicit mappings:

- `refs/heads/codex/reorg-completion-2026-08-r04-cholesky-higham-ch10:refs/heads/codex/reorg-completion-2026-08-r04-cholesky-higham-ch10`
- `refs/heads/codex/reorg-completion-2026-08-r08-matrix-inversion-ch14:refs/heads/codex/reorg-completion-2026-08-r08-matrix-inversion-ch14`

The atomic push used explicit nonexistent-tip leases for both new refs:

- `--force-with-lease=refs/heads/codex/reorg-completion-2026-08-r04-cholesky-higham-ch10:`
- `--force-with-lease=refs/heads/codex/reorg-completion-2026-08-r08-matrix-inversion-ch14:`

The remote tips were independently re-read after creation and both equal exact C0004.

## Clean activation boundary

Each named worktree has worktree-scoped `core.autocrlf=false`, `core.eol=lf`, and `core.safecrlf=false`. Each has the exact branch and C0004 HEAD shown above, empty tracked and untracked status, zero tracked `w/crlf` entries, no `.lake` directory, and no `.olean` artifacts. No implementation or build state exists in either worktree.

`P0008` and `P0009` remain active and unchanged. `R0009` and `R0010` remain active and unchanged, with null resolutions. Their reviewed 37-path common-base union remains integrator-only and unapplied; neither individual request nor their union has been applied.

`phase.json` remains byte-identical at SHA-256 `E3B8E30F2435EFCEAC9D4A0302A7FD26EC5AD17A1132FEBA692F4287C7608CA1`. C0004 remains current and immutable, and M04/M08 readiness remains unchanged. No worker commit, production or test edit, request application, Lean build, delivery, integration, or `C0005` checkpoint exists.

All future Lean operations for these workers and the integrator serialize under `Local\lean-reorganization-2026-08`. Both workers remain frozen until the activation-control commit itself passes exact Lean CI, including its exact `build` job. This activation turn stops at that green gate and does not begin R04 or R08 implementation.
