# Repository reorganization phase: August 2026

Status: **ACTIVE**. Checkpoint C0004 at
`b56f609f3bf66b5d7d0b677567cce82fee0c275b` is accepted and green. M01, M02,
and M12 are accepted; M03 and M05 are ready; and B0001, B0002, and B0003 are
retired. B0004/W03 and B0005/W05 have delivered from C0004 with active frozen
projections P0005 and P0006. Their recorded worker branches and worktrees were
created cleanly from the exact C0004 code SHA after the planned activation
record passed CI. Both branch records are now delivered and await joint
integration. Their independently C0004-based shared requests R0003 and R0004
are active and hash-pinned; the accepted checkpoint remains C0004.

This is the current repository-wide operating contract. It supersedes the
four-lane packets as an instruction source; those packets remain historical
evidence for the bounded work they completed.

## Control artifacts

- [`phase.json`](phase.json) is the machine-checked authority, milestone,
  completion, and shared-path manifest.
- [`scope.tsv`](scope.tsv) is the immutable full production-module scope;
  [`unclassified-queue.tsv`](unclassified-queue.tsv) is its exact current
  implementation-wave partition, and
  [`semantic-review.tsv`](semantic-review.tsv) records suggestions that are not
  safe to apply mechanically.
- [`C0000.json`](checkpoints/C0000.json) defines the accepted origin;
  [`C0001.json`](checkpoints/C0001.json) is the pre-W01 branch checkpoint;
  [`C0002.json`](checkpoints/C0002.json) records W01 acceptance; and
  [`C0003.json`](checkpoints/C0003.json) records W02 acceptance.
  [`C0004.json`](checkpoints/C0004.json), its
  [`green gates`](checkpoints/C0004-gates.md), and its
  [`fresh combined baseline`](baselines/C0004-combined.json) define the current
  W12-accepted checkpoint.
- The [`branch`](branches/README.md),
  [`projection`](projections/README.md), and
  [`shared-request`](requests/README.md) registries define live transport and
  handoffs. [`B0002`](branches/B0002.json) records retired W02 with retired
  [`P0002`](projections/P0002.json). [`B0003`](branches/B0003.json) records W12
  accepted at C0004 and retired, while
  [`P0004`](projections/P0004.json) is its retired immutable projection
  evidence. [`B0004`](branches/B0004.json) and
  [`B0005`](branches/B0005.json) are the delivered W03 and W05 transports, with
  active C0004 projections [`P0005`](projections/P0005.json) and
  [`P0006`](projections/P0006.json), with active shared requests
  [`R0003`](requests/R0003.json) and [`R0004`](requests/R0004.json).
  No prose packet overrides these records.
- [`check_phase.py`](../../../../tools/architecture/check_phase.py) validates
  the complete phase state;
  [`check_phase_projection.py`](../../../../tools/architecture/check_phase_projection.py)
  validates a worker's frozen declaration graph against its candidate
  extraction.

## Scope and completion language

Checkpoint C0000 is based on `main` commit
`7930cca4f6c45ccbe0dc23e40480fabec4993f5b`. At that revision the repository
has 1,390 production modules, including 415 unclassified modules, 206 missing
module-docstring debts, 276 naming debts, and 12 declaration-bearing umbrella
debts. The immutable `scope.tsv` enumerates all 1,390 modules, their base blob
IDs, tiers, debt flags, disposition, owner lane, implementation wave, and
required actions. No production module is implicit.

There are two independent completion claims:

- **Bounded phase complete** means every in-scope wave in this manifest is
  accepted, all required milestones and gates pass at a current checkpoint,
  and no branch or shared-file request remains open.
- **Repository-wide complete** additionally requires zero unclassified,
  mixed, documentation, naming, umbrella, and aggregate-order debt, plus the
  full build, test, compatibility, provenance, entrypoint, outlier, and
  generated-artifact gates recorded by `phase.json`.

Neither status is currently complete.

## Authority and machines

The phase uses one integration authority and two human-owned work lanes:

| Role | Authority |
|---|---|
| Integration authority, release manager, shared files, branch registry, `main` pushes | `primary-human` |
| Local lane owner | `primary-human` |
| Local operators | `codex-local`, `claude-local` |
| Remote lane owner | `remote-human` |
| Remote operators | `codex-remote`, `claude-remote` |
| CI evidence service | `github-actions` |

The identifiers describe authority, not a permanent model subscription. An
operator may change only by updating the relevant integrator-owned record on
`main`.

The local Codex and Claude must not edit the same checkout. They use separate
Git worktrees based on the current checkpoint. The remote Codex and Claude
communicate through the remote repository. Only one tracked branch per live
wave is allowed; branches are retired after their delivery commit is an
ancestor of a green accepted checkpoint. Nobody except the integration
authority pushes `main`.

A branch may list both lane operators, but only one operator is its active
writer at a time. The companion operator reviews read-only or takes over after
a pushed handoff commit; simultaneous uncoordinated edits to the same branch
are outside the contract.

Large Lean builds, tests, and declaration extraction use the shared lock name
`lean-reorganization-2026-08`. Editing and read-only graph work may proceed in
parallel, but two expensive Lean jobs are not independent evidence.

## Implementation waves

The exact module-to-wave assignment is in `unclassified-queue.tsv`; `scope.tsv`
also assigns debt-only and outlier-review rows. Counts below partition the 415
unclassified modules exactly.

| Wave | Owner lane | Modules | Dependency | Purpose |
|---|---|---:|---|---|
| W01 | local | 4 | — | Split the mixed floating-point analysis boundary. |
| W02 | remote | 73 | W01 | Generic, LU, triangular, and Chapter 7 foundations. |
| W03 | local | 26 | W02 | Cholesky, Chapter 10, and the Chapter 11 tail. |
| W04 | remote | 29 | W03 | Chapter 21 after QR, Cholesky, and Chapter 7 APIs. |
| W05 | local | 10 | W02 | Chapter 16 Lyapunov/Psi core and the Chapter 18 real-Schur bridge. |
| W06 | remote | 67 | W05 | Remaining interdependent Chapter 16/18 owners. |
| W07 | local | 5 | W06 | Stationary iteration and Chapter 17. |
| W08 | remote | 42 | W03 | Matrix inversion, Gauss–Jordan, and Chapter 14. |
| W09 | local | 72 | W02, W06 | Test matrices and Chapter 28. |
| W10 | remote | 27 | W03, W09 | Norm estimation and Chapter 15. |
| W11 | local | 18 | W06, W08 | Randomized numerical linear algebra. |
| W12 | remote | 42 | W01 | Chapters 1, 2, and 5 plus source-review owners. |
| W90 | local | 125 debt-only/outlier rows | W01–W12 | Finish documentation, naming, umbrella, entrypoint, and outlier ratchets. |

The order is a dependency DAG, not a demand to keep one machine idle. For
example, W05 and W08 can proceed after their distinct prerequisites; W12 can
proceed after W01 while foundation work continues. Checkpoint acceptance, not
wall-clock completion, unblocks a dependent wave.

This is a **migration-order DAG**, not a claim that the current unclassified
source-import graph is acyclic. Current source owners cross wave boundaries.
Each activated branch therefore freezes its incident declaration graph and
explicitly permits the current external dependencies; the ordering describes
when an interface is stable enough to migrate, not which imports already
exist.

## Branch lifecycle

1. The integrator accepts a green `main` checkpoint and refreshes the combined
   baseline, inventory, and overlap review.
2. A branch record under `branches/` names one wave, one current checkpoint,
   one baseline projection, exact owned and forbidden paths, owner, operators,
   and retirement rule.
3. The worker creates that exact branch from the recorded SHA. It may not edit
   shared files.
4. If shared changes are needed, a hash-pinned request and patch are recorded
   under `requests/` against the current checkpoint. Requests expire when the
   checkpoint advances.
5. Delivery includes a commit, report, scope evidence, focused builds,
   old-import and canonical-import tests, and the lane projection check.
6. The integrator applies shared changes, merges in dependency order, runs the
   combined architecture/build/test gates, publishes the next checkpoint, and
   only then retires the remote branch.

W01 delivery `d30fecc70a1d2066e2d147b79d9e6b9d743a21e5` is an ancestor of
C0002. Its declaration-preserving integration is recorded by B0001, and its
remote branch is retired under the ancestry rule.

W02 and W12 were both implemented from the exact C0002 commit. W02 delivery
`799d781971eed851cd90152c0d9acb0e828f9341` is an ancestor of accepted C0003;
B0002 records the integration and the remote branch's retirement. W12 delivery
`380d3cba83bb9e3704232720f371f28cbbc673da` is an ancestor of accepted C0004.
The integrator reconciled its recorded 17-import delta against W02 before the
canonical, strict-source, full-build, full-test, and frozen-projection gates.
B0003's remote branch was retired after the C0004 control record passed CI, and
the deletion is recorded in its registry entry. Workers must not copy or edit
registry files on their delivery branches.

## Classification warning

The old 386-row classification packet is a frozen proposal, not an executable
tier patch. Of its rows, 309 were still unclassified at the pre-phase audit.
Applying those labels wholesale creates forbidden dependency paths and also
misclassifies semantically source-shaped owners.

Two confirmed defects are `GaussJordanPivoting` (source-faithful Chapter 14,
not reusable) and `Higham726Rump` (equation 7.26, not a fictitious Chapter 72).
Seventeen more graph-safe `reusable` suggestions own source-numbered or
source-named declarations and require declaration-level review. The tracked
`semantic-review.tsv` is a queue for review, not authorization to edit
`tiers.json`.

## Gates

Every implementation wave must preserve old imports and public declarations,
add or retain canonical-only and old-only smoke tests, and pass:

- exact branch scope and shared-request checks;
- the lane-scoped baseline projection;
- `check_layout.py`, `check_compatibility.py`, and `check_provenance.py`;
- strict source-graph generation with zero cycles and zero forbidden reusable
  reachability;
- focused old-path, canonical-path, and family builds; and
- the full build and tests at each accepted integration checkpoint.

`python tools/architecture/check_phase.py` validates this operating contract in
CI. It rejects stale bases, overlapping live branches, expired requests,
unhashed artifacts, milestone cycles, and premature completion claims.
