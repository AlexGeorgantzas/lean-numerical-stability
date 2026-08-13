# C0002 singleton R03 selection and R07 deferral

Authority: `primary-human`
Control operator: `codex-local`
Exact worker-code base: C0002 `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`
Decision: select M03/R03 alone; explicitly defer M07/R07.

This review advances M03 from `planned` to `ready` while leaving
`accepted_checkpoint_id` null. M07 and every other unaccepted milestone remain
`planned`. It does not authorize an R03/R07 pair.

## Why R03 is first

C0002 contains 277 unclassified modules, 9 mixed modules, 13 modules missing a
module docstring, 241 noncanonical modules, and 16 declaration-bearing
umbrellas. The exact 47-owner R03 selector accounts for:

| Residual class | R03 | C0002 total |
| --- | ---: | ---: |
| unclassified | 23 | 277 |
| mixed | 9 | 9 |
| missing module docstring | 13 | 13 |
| noncanonical | 24 | 241 |
| declaration-bearing umbrella | 2 | 16 |

R03 therefore contains every current mixed module and every current
missing-module-doc row. R07 contains 43 unclassified and four noncanonical
rows, but no mixed or missing-doc row.

The milestone DAG also makes R03 the higher-leverage singleton. M05 and M06
each depend on M03 and already-accepted M11. Acceptance of R03 would therefore
make both M05 and M06 dependency-ready. R07 acceptance would not do so.

## Exact selection evidence

The selector is derived only from exact C0002 inventory rows satisfying
`phase_scope == in_scope && wave_id == R03`. Its sorted two-column LF content,
including header `module<TAB>path`, has 47 rows and SHA-256
`176BC214ABAE4B9CC2E9822E3177033213C4BD730D0057FBE8BAB524412C6B3A`.

The independent overlap and consumer evidence is:

- `branches/B0005-consumers.tsv` / `3AFD072408026219BDB07D1004E3768B27576AEB88AFBC8312FA9D9467155400`;
- `branches/B0005-overlap-review.md` / `EC3ADA8E009CCD9E0C8849F73FB8F248EED9FEB1C31A4B33D2C41A74A047CA67`;
- C0002 inventory / `BB5AE8029CC3DC547BA1E4C8B581BA11948E527810AC29F0EBE8E1CC5D81BF02`;
- raw exact-C0002 format-2 graph / `E03DB7A24886AD0B45C7371FE30ACE3AD135B3C4CC9866D65186753CD14FAD4C`.

The audit reproduces 24 R03 -> R07 and 23 R07 -> R03 transitive owner
reachability pairs, seven common direct project dependencies, and five shared
direct outside consumers. All five are direct-both consumers: each directly
imports at least one owner from each candidate wave. There are no direct owner
imports, declaration signature edges, declaration body/proof edges, or shared
outside dependent declarations between the waves.

Declaration-graph separation is insufficient to authorize a pair when the
module graph has bidirectional owner reachability and shared consumers. A
singleton avoids planning two migrations against mutually dependent historical
surfaces and avoids reconciling two independently changing request postimages.

## Planned control allocation

The next collision-free identifiers are allocated only to R03:

| Control | Value |
| --- | --- |
| branch registry record | `B0005` |
| projection | `P0005` |
| shared-file request | `R0005` |
| wave | `R03` |
| lane | `codex-lane` |
| operator | `codex-local` |
| planned worker ref | `refs/heads/codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12` |
| planned worktree | `C:\Users\qed_s\higham-worktrees\completion-r03-codex` |
| worker code base | `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd` |

The pre-activation lifecycle is intentionally asymmetric:

- B0005 is `planned`;
- P0005 and R0005 are active planning controls rooted at exact C0002;
- activation time, activation tip, base-tip evidence, delivery, merge, and
  integration fields are null;
- retirement is `not_due`;
- neither the remote worker ref nor the planned worktree exists;
- current-main retirement/planning-control HEAD is never substituted for the
  exact C0002 worker-code base.

Workers do not own shared/global controls. An audit-only 13-path lower bound
consists of nine exact direct consumers of the 24 rename owners plus
`NumStabilityTest.lean`, `docs/architecture/COMPATIBILITY.md`,
`docs/architecture/layout-exceptions.json`, and
`docs/architecture/tiers.json`. The 13-path list hashes to
`CE3FEC6A24D94031D9A70F5FE002FE89276612060B17E535541A2FEAF8DAB7E1`.
The overlap review records every C0002 blob OID and preimage SHA-256.

The frozen module routes classify 36 structural owners and select all 117 of
their direct outside consumer paths, containing 152 exact import replacements.
With the four controls, R0005 is therefore the exact 121-path request and hashes to
`22D7FB62215BA50D4C9E5E83254B3196C2920CC7B8BF2A835201D7730694E3FB`.
Transitive consumers and external dependent declarations remain exhaustive
protected-consumer/projection evidence rather than automatic patch paths.

## Explicit R07 deferral

M07 remains `planned` with `accepted_checkpoint_id` null. This epoch allocates
no R07 branch ID, projection ID, request ID, ref, worktree, operator exception,
or activation evidence. The audit-only R07 selector hash is retained solely to
make the rejection reproducible; it is not an active selector.

R07 may be reconsidered only after R03 is accepted into a new green checkpoint
and a fresh review from that checkpoint regenerates its inventory selector,
module/declaration projections, routes, consumer closure, shared request, and
overlap facts. No C0002 R07 result is carried forward as activation authority.

## Replay and lock discipline

Verify the immutable inputs and evidence with:

```powershell
git diff --exit-code 9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd -- NumStability NumStability.lean
Get-FileHash -Algorithm SHA256 docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0002-inventory.tsv
Get-FileHash -Algorithm SHA256 benchmark-results/C0002-combined.tsv
Get-FileHash -Algorithm SHA256 docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0005-consumers.tsv
Get-FileHash -Algorithm SHA256 docs/architecture/phases/2026-08-repository-reorganization-completion/branches/B0005-overlap-review.md
```

The exact C0002 raw graph was generated while holding Windows named mutex
`Local\lean-reorganization-2026-08`. Read-only parsing of that pinned graph and
source import scanning require no Lean operation. Every replay that regenerates
the raw graph, a declaration projection, a baseline, or any other Lean-derived
artifact must acquire that mutex first and retain it through verification.

The terminal decision for this planning epoch is therefore: **R03 only; R07
deferred**.
