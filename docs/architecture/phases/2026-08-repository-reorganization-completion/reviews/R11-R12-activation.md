# R11/R12 activation review

- Activated at: `2026-08-11T23:42:51Z`
- Activated by: `primary-human`
- Current checkpoint: `C0001`
- Immutable code base: `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`
- Planned-control commit: `c48d241532ad3dee12f4107a5e8875c7054159be`
- Planned-control CI: Lean CI push run `31546978830`, job `93961477202`, completed `success`
- Planned-control architecture/tooling: `success`
- Planned-control build/smoke: `success`, `8895` jobs

The planned-control gate was green before either ref or worktree was created. Both branches were then created from the same exact C0001 code commit, pushed atomically as new remote refs with nonexistent-tip leases, and verified clean before their synchronized transition to `active`.

| Branch | Wave | Lane | Operator | Remote ref | Worktree | Verified tip |
| --- | --- | --- | --- | --- | --- | --- |
| `B0003` | `R11` | `claude-lane` | `claude-local` | `refs/heads/codex/reorg-completion-2026-08-r11-qr-ch19` | `C:\Users\qed_s\higham-worktrees\completion-r11-claude` | `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` |
| `B0004` | `R12` | `claude-lane` | `codex-local` | `refs/heads/codex/reorg-completion-2026-08-r12-ch13-equations-table` | `C:\Users\qed_s\higham-worktrees\completion-r12-codex` | `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` |

At activation, each local branch, named worktree HEAD, and remote branch tip matched the verified tip above; both worker worktrees had empty `git status --porcelain` output. B0003/R11 and B0004/R12 remain graph-disjoint, their primary-human shared requests remain integrator-owned, and the temporary B0004 operator exception remains bounded by the hash-pinned operator-authorization review.
