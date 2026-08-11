# Repository reorganization phase: August 2026

Status: **ACTIVE**. Checkpoint C0008 accepts green code commit
`b1b18772d80185ec08f49c818919558645c330a1`. M01 through M12 are accepted;
M90 is ready but remains unactivated, and bounded-phase and repository-wide
completion remain incomplete. B0011/W07 delivery
`176c72838828795b89f4aa822479010c7860c8e5` and corrected B0012/W10 delivery
`9e7604cbdbd2314bc4bf38bcd9e342c3accfb1d6` are ancestors of C0008 through
separate true merges `9399c0531c6c6431e3f8def33fae1df3fbb060a6` and
`25ea10390ab118dbfc3ecf2c05ba9e33fbe1e626`. Their frozen C0007 projections
P0012/P0013 are retired immutable evidence, and independently C0007-based
requests R0010/R0011 are applied at C0008. B0011 and B0012 are accepted and
retired. After C0008 acceptance-control commit
`5d047643efbc06e69d380a4266010d9f48d934e1` passed
[Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31469704946),
both exact remote refs were deleted atomically with exact expected-SHA leases
at `2026-08-11T07:47:20Z` by `primary-human`. The ignored W07 artifacts were
archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0008-W07-20260811`;
its named delivery worktree was removed without force, and both local branches
remain preserved at their immutable tips. The clean local post-delivery W10
integrator recovery/correction checkout at `C:\Users\qed_s\w10-worker` is not
a worker-lane checkout or retirement target and remains preserved.

B0006/W06 delivery
`436b38cbda2e06cf5c9ea3343f0bc6fe428f0b97` and B0007/W08 delivery
`664d5d495975a05d74cd4c0c09f9207aff8cdd77` were integrated by separate true
merges and accepted at C0006. Their frozen projections P0007 and P0008 are
retired immutable evidence, and their independently C0005-based shared
requests R0005 and R0006 are applied at C0006. B0006 and B0007 are retired;
their exact remote refs were deleted at `2026-08-04T13:33:21Z` after the C0006
acceptance-control commit passed Lean CI. Local worker branches and worktrees
remain preserved. B0008/W04 delivery
`12bd75d4d25b2d98344d26b0dc0b016f1e2f1814`, B0009/W09 delivery
`69ee6cf790d1f3826075f33ea4907c9a4b5a637a`, and B0010/W11 delivery
`580c0298a47a533725e034c32c7702a7436fa6ed` are ancestors of C0007 through
separate true merges. Their frozen projections P0009, P0010, and P0011 are
retired immutable evidence, and their independently C0006-based requests
R0007, R0008, and R0009 are applied at C0007. B0008, B0009, and B0010 are
accepted and retired. After the C0007 acceptance-control commit passed Lean CI,
their three exact remote refs were deleted atomically with exact expected-SHA
leases at `2026-08-08T22:05:06Z` by `primary-human`. W04 never had a local
worktree. The ignored W09/W11 delivery artifacts were archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0007-W09-W11-20260808`;
their named worktrees were removed, and their local branches remain preserved
at the immutable delivery tips.
Planned-control commit `ac3bc1063c7d9aa1c7a0c12a85337c858b6f9200`
passed [Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31300495624);
only then were both worker refs initialized at the exact C0007 code SHA and the
clean W07 worktree created at
`C:\Users\qed_s\higham-worktrees\reorg-w07-codex`. W10's assigned worker lane
remained remote-only and had no authorized local worker checkout during
implementation. After delivery intake, the clean local integrator
recovery/correction checkout `C:\Users\qed_s\w10-worker` was used to
materialize the corrected immutable W10 tip. It is not a worker-lane checkout
or a retirement target and remains preserved. Active-control commit
`cb5fa161bcf6827c7d15e61df9dd9ded34f39327` passed
[Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31300899785)
before either worker began.
B0004/W03 and B0005/W05 were accepted at C0005 and retired after that
acceptance-control state passed Lean CI. P0005 and P0006 are retired immutable
projection evidence, and their independently C0004-based shared requests R0003
and R0004 are applied at C0005. The W03/W05 remote delivery refs are absent;
their local branches and worktrees remain preserved.

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
  [`C0004.json`](checkpoints/C0004.json) records W12 acceptance, and
  [`C0005.json`](checkpoints/C0005.json) records joint W03/W05 acceptance, and
  [`C0006.json`](checkpoints/C0006.json) records joint W06/W08 acceptance, and
  [`C0007.json`](checkpoints/C0007.json) records joint W04/W09/W11 acceptance.
  The current [`C0008.json`](checkpoints/C0008.json), its
  [`green gates`](checkpoints/C0008-gates.md),
  [`fresh combined baseline`](baselines/C0008-combined.json), and
  [`inventory`](checkpoints/C0008-inventory.tsv) define the joint W07/W10
  checkpoint.
- The [`branch`](branches/README.md),
  [`projection`](projections/README.md), and
  [`shared-request`](requests/README.md) registries define live transport and
  handoffs. [`B0002`](branches/B0002.json) records retired W02 with retired
  [`P0002`](projections/P0002.json). [`B0003`](branches/B0003.json) records W12
  accepted at C0004 and retired, while
  [`P0004`](projections/P0004.json) is its retired immutable projection
  evidence. [`B0004`](branches/B0004.json) and
  [`B0005`](branches/B0005.json) are retired W03 and W05 transports accepted at C0005,
  with retired projections [`P0005`](projections/P0005.json) and
  [`P0006`](projections/P0006.json), and applied shared requests
  [`R0003`](requests/R0003.json) and [`R0004`](requests/R0004.json).
  [`B0006`](branches/B0006.json) and [`B0007`](branches/B0007.json) are the
  accepted and retired, disjoint C0005 transports for W06 and W08. Their retired frozen
  projections are [`P0007`](projections/P0007.json) and
  [`P0008`](projections/P0008.json), selected by
  [`W06.tsv`](selectors/W06.tsv) and [`W08.tsv`](selectors/W08.tsv); their
  applied shared requests are [`R0005`](requests/R0005.json) and
  [`R0006`](requests/R0006.json).
  [`B0008`](branches/B0008.json), [`B0009`](branches/B0009.json), and
  [`B0010`](branches/B0010.json) are the accepted and retired, mutually
  disjoint C0006 transports for W04, W09, and W11. Their retired frozen
  projections are
  [`P0009`](projections/P0009.json), [`P0010`](projections/P0010.json), and
  [`P0011`](projections/P0011.json), selected by
  [`W04.tsv`](selectors/W04.tsv), [`W09.tsv`](selectors/W09.tsv), and
  [`W11.tsv`](selectors/W11.tsv). Applied shared requests
  [`R0007`](requests/R0007.json), [`R0008`](requests/R0008.json), and
  [`R0009`](requests/R0009.json) record the integrator-owned deltas accepted at
  C0007.
  Accepted [`B0011`](branches/B0011.json) and
  [`B0012`](branches/B0012.json) are the disjoint C0007 transports for W07 and
  W10. Their frozen projections are retired immutable evidence:
  [`P0012`](projections/P0012.json) and
  [`P0013`](projections/P0013.json), selected by
  [`W07.tsv`](selectors/W07.tsv) and [`W10.tsv`](selectors/W10.tsv). Applied
  requests [`R0010`](requests/R0010.json) and
  [`R0011`](requests/R0011.json) record the integrator-owned C0008 delta. Both
  branch records identify C0008 integration and retirement `retired`.
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

W03 delivery `a36ea332cb8e19ed4f6985d1a22e8e356c5dc9ce` and W05 delivery
`23883bb9e477a2645ce76213687c73584651c077` are ancestors of accepted C0005
code commit `240c0d041781385a647fbec461d6863537e562cb` through separate true merges.
The integrator applied hash-pinned R0003 and R0004, replayed P0005 and P0006
against one full integrated graph, and passed every combined static, focused,
full-build, full-test, and strict-source gate. After the C0005
acceptance-control commit passed CI, both exact remote refs were deleted at
`2026-08-03T15:23:25Z` by `primary-human`; local worktrees and branches were
preserved.

W06 delivery `436b38cbda2e06cf5c9ea3343f0bc6fe428f0b97` and W08 delivery
`664d5d495975a05d74cd4c0c09f9207aff8cdd77` are ancestors of accepted C0006
code commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5` through separate true merges.
The integrator applied hash-pinned R0005 and R0006, replayed P0007 and P0008
against one full integrated graph, and passed the combined static, focused,
full-build, full-test, and strict-source gates. After the C0006
acceptance-control commit passed Lean CI, both exact remote refs were deleted at
`2026-08-04T13:33:21Z` by `primary-human`; local worktrees and branches remain
preserved and were never retirement targets.

W04 delivery `12bd75d4d25b2d98344d26b0dc0b016f1e2f1814`, W09 delivery
`69ee6cf790d1f3826075f33ea4907c9a4b5a637a`, and W11 delivery
`580c0298a47a533725e034c32c7702a7436fa6ed` are ancestors of accepted C0007
code commit `9eb534a06db267203c2b9b88227edd44fc64f5db` through separate true merges.
The integrator applied hash-pinned R0007, R0008, and R0009, replayed P0009,
P0010, and P0011 against one full integrated graph, and passed the combined
static, focused, full-build, full-test, and strict-source gates. All three
branch records are retired. After the C0007 acceptance-control commit passed
Lean CI, their exact remote refs were deleted atomically with exact expected-SHA
leases at `2026-08-08T22:05:06Z` by `primary-human`. W04 never had a local
worktree. The ignored W09/W11 delivery artifacts were archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0007-W09-W11-20260808`;
their named worktrees were removed, and their local branches remain preserved
at the immutable delivery tips.
Planned-control commit `94da2d1e25247d7e9b6661dc188c932cdc6cc1d5`
passed [Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30920452203).
All three worker refs began at the code SHA, never at a later control commit.
W07 and W10 now have accepted B0011/B0012 control records and retired frozen
P0012/P0013 projections. Their immutable delivery tips are
`176c72838828795b89f4aa822479010c7860c8e5` and
`9e7604cbdbd2314bc4bf38bcd9e342c3accfb1d6`; separate true merges and green
C0008 code commit `b1b18772d80185ec08f49c818919558645c330a1` preserve their
integration. Both records are retired after the acceptance-control CI and
exact-lease remote deletion recorded above. Planned-control commit
`ac3bc1063c7d9aa1c7a0c12a85337c858b6f9200` passed
[Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31300495624)
before either worker ref or the W07 worktree was created. Both worker refs
began at exact C0007 code SHA `9eb534a06db267203c2b9b88227edd44fc64f5db`,
never a later control commit. The sole authorized local W07 worktree at
`C:\Users\qed_s\higham-worktrees\reorg-w07-codex` began clean at that SHA; W10
remained assigned to the remote lane with no authorized local worker checkout.
The later clean integrator recovery/correction checkout at
`C:\Users\qed_s\w10-worker` is preserved outside worker retirement.
Active-control commit
`cb5fa161bcf6827c7d15e61df9dd9ded34f39327` passed Lean CI before work began.

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
