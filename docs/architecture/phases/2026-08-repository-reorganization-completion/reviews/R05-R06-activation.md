# R05/R06 activation review

- Activated at: `2026-08-14T22:02:25Z`
- Authority: `primary-human`, exercising the explicitly granted branch-registry, activation-control, main-push, and worktree-creation authority (recorded by `claude-local` under the reviewed B0006-scoped expansion in `reviews/R05-R06-operator-authorization.md`)
- Branches / waves: `B0006` / `R05` and `B0007` / `R06`
- Lane / operators: `codex-lane` / `claude-local` (B0006 only, temporary) and `codex-local`
- Current checkpoint: `C0003`
- Accepted C0003 checkpoint and immutable worker base: `e20de2f931caa12221e708c341e9cb4f64d29b25`
- Planned-control commit: `b6794f326313f8077c0c3433bb9c76b6e2ed5361`
- Planned-control CI: Lean CI push run `31844203563`, job `94907208819`, completed `success`

The planned-control gate was green for the exact planned-control commit
before any B0006/B0007 ref or worktree was created. Both local branches were
created explicitly from accepted C0003 rather than current `main`; both named
worktrees are checked out with `core.autocrlf=false`, `core.eol=lf`, and
`core.safecrlf=false` (tracked content re-smudged to LF and verified); and
both new remote refs were pushed with explicit nonexistent-tip leases.

| Fact | Exact value |
| --- | --- |
| B0006 local branch | `codex/reorg-completion-2026-08-r05-least-squares-underdetermined-ch20-ch21` |
| B0006 local branch tip | `e20de2f931caa12221e708c341e9cb4f64d29b25` |
| B0006 remote ref | `refs/heads/codex/reorg-completion-2026-08-r05-least-squares-underdetermined-ch20-ch21` |
| B0006 remote ref tip | `e20de2f931caa12221e708c341e9cb4f64d29b25` |
| B0006 named worktree | `C:\Users\qed_s\higham-worktrees\completion-r05-claude` |
| B0006 worktree HEAD | `e20de2f931caa12221e708c341e9cb4f64d29b25` |
| B0007 local branch | `codex/reorg-completion-2026-08-r06-schur-sylvester-pivoting-ch09-ch11-ch16` |
| B0007 local branch tip | `e20de2f931caa12221e708c341e9cb4f64d29b25` |
| B0007 remote ref | `refs/heads/codex/reorg-completion-2026-08-r06-schur-sylvester-pivoting-ch09-ch11-ch16` |
| B0007 remote ref tip | `e20de2f931caa12221e708c341e9cb4f64d29b25` |
| B0007 named worktree | `C:\Users\qed_s\higham-worktrees\completion-r06-codex` |
| B0007 worktree HEAD | `e20de2f931caa12221e708c341e9cb4f64d29b25` |

At activation, both named worktrees had empty tracked and untracked status.
No worker commit, production edit, or R0006/R0007 application exists.
M07/R07 remains unactivated and `planned`.

The B0006 worker (`claude-local` under the reviewed expansion) may edit only
B0006-owned paths, B0006 destination prefixes,
`NumStabilityTest/Reorganization/R05/`, and
`docs/architecture/deliveries/R05/`. The B0007 worker (`codex-local`) may
edit only B0007-owned paths, B0007 destination prefixes,
`NumStabilityTest/Reorganization/R06/`, and
`docs/architecture/deliveries/R06/`. Neither worker may touch the other
wave's paths. All 23 R0006 paths, all 49 R0007 paths, and the five shared
union paths remain integrator-only. Both requests are context-free; any
disposable replay must use `git apply --unidiff-zero`. Builds in either
worktree must serialize under the `Local\lean-reorganization-2026-08` mutex.

No implementation begins before activation-control CI. Both workers remain
frozen until the activation-control commit on `main` has exact green Lean
CI, including the full `NumStability` and `NumStabilityTest` build.
