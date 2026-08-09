# Branch registry

One JSON record is tracked per phase branch. A planned branch must start from
the current accepted checkpoint and use an active lane baseline projection.
Delivery, integration, ancestry, and retirement fields are updated rather than
replaced by prose-only status messages.

Two mutually disjoint transports are planned from exact C0007 code commit
`9eb534a06db267203c2b9b88227edd44fc64f5db`. Their refs do not yet exist and
workers must not start until the planned-control commit passes Lean CI, both
refs are initialized at that exact code SHA, the records are changed to
`active`, and the active-control commit also passes Lean CI:

- [`B0011`](B0011.json): W07 local-lane branch
  `codex/reorg-2026-08-w07-stationary-ch17`, five exact historical owners, 34
  reviewed production destinations plus W07 test/delivery prefixes, owner
  `primary-human`, and sole operator `codex-local`. Its only authorized local
  worktree is
  `C:\Users\qed_s\higham-worktrees\reorg-w07-codex`;
- [`B0012`](B0012.json): W10 remote-lane branch
  `codex/reorg-2026-08-w10-norm-estimation-ch15`, 27 exact historical owners,
  43 reviewed production destinations plus W10 test/delivery prefixes, owner
  `remote-human`, and sole operator `claude-remote`. No local W10 worktree is
  authorized.

Both records have null delivery and integration fields, empty
`shared_request_ids`, and retirement `not_due`. Their independent hash-pinned
reviews [`B0011-overlap-review.md`](B0011-overlap-review.md) and
[`B0012-overlap-review.md`](B0012-overlap-review.md) reproduce the C0007
selectors/projections and prove zero owner, destination, direct-import,
signature-edge, and body/proof-edge overlap in either direction. Their sole
common direct production consumer is the integrator-owned
`NumStability/Algorithms.lean`.

Three mutually disjoint branches were implemented from exact C0006 code commit
`a32095e6e50189f7dcc39312bb4c6a36f421fab5` and accepted through separate true
merges at C0007 code commit `9eb534a06db267203c2b9b88227edd44fc64f5db`.
Planned-control commit
`94da2d1e25247d7e9b6661dc188c932cdc6cc1d5` passed
[Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30920452203)
before their refs or local worktrees were created. Their immutable delivery
tips and hash-pinned packet evidence are recorded below. All three records are
accepted and retired after the C0007 acceptance-control commit passed Lean CI:

- [`B0008`](B0008.json): W04 remote-lane branch
  `codex/reorg-2026-08-w04-ch21-underdetermined`, 29 exact historical owners,
  42 reviewed production destinations plus W04 test/delivery prefixes, and
  sole operator `codex-remote`, immutable delivery
  `12bd75d4d25b2d98344d26b0dc0b016f1e2f1814`; no local W04 worktree is
  authorized;
- [`B0009`](B0009.json): W09 local-lane branch
  `codex/reorg-2026-08-w09-test-matrices-ch28`, 72 exact historical owners,
  30 reviewed production destinations plus W09 test/delivery prefixes, sole
  operator `claude-local`, immutable delivery
  `69ee6cf790d1f3826075f33ea4907c9a4b5a637a`; its named delivery worktree
  `C:\Users\qed_s\higham-worktrees\reorg-w09-claude` was removed at retirement;
- [`B0010`](B0010.json): W11 local-lane branch
  `codex/reorg-2026-08-w11-randnla`, 18 exact historical owners, 33 reviewed
  production destinations plus W11 test/delivery prefixes, sole operator
  `codex-local`, immutable delivery
  `580c0298a47a533725e034c32c7702a7436fa6ed`; its named delivery worktree
  `C:\Users\qed_s\higham-worktrees\reorg-w11-codex` was removed at retirement.

Their projections P0009, P0010, and P0011 are retired immutable evidence. The
records link applied, independently C0006-based shared requests R0007, R0008,
and R0009, and their integration fields identify C0007 and its green code SHA.
Independent hash-pinned
reviews [`B0008-overlap-review.md`](B0008-overlap-review.md),
[`B0009-overlap-review.md`](B0009-overlap-review.md), and
[`B0010-overlap-review.md`](B0010-overlap-review.md) prove zero owner,
destination, direct-import, signature-edge, and body/proof-edge overlap in all
directions. `NumStability/Algorithms.lean` is their integrator-owned common
downstream aggregate. The additional W04/W11 downstream consumer
`NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` is
also integrator-owned and forbidden to both workers. C0007 is current; M04,
M09, and M11 are accepted, while M07 and M10 are ready and unactivated. The
three exact remote delivery refs were deleted atomically with exact expected-SHA
leases at `2026-08-08T22:05:06Z` by `primary-human` after the C0007
acceptance-control commit passed Lean CI. W04 never had a local worktree. The
ignored W09/W11 delivery artifacts were archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0007-W09-W11-20260808`;
their named worktrees were removed, and their local branches remain preserved
at the immutable delivery tips.

Two disjoint remote-lane branches were implemented from exact C0005 code commit
`240c0d041781385a647fbec461d6863537e562cb` and accepted through separate true
merges at C0006 code commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.
Their remote refs were initialized at the C0005 SHA only after the planned
control state passed Lean CI and were deleted only after the C0006
acceptance-control commit passed Lean CI:

- [`B0006`](B0006.json): W06, branch
  `codex/reorg-2026-08-w06-ch16-ch18-remaining`, 67 exact historical owners,
  49 reviewed production destinations plus test and delivery prefixes, sole
  operator `codex-remote`, retired projection P0007, and immutable delivery
  `436b38cbda2e06cf5c9ea3343f0bc6fe428f0b97`, with applied shared request
  R0005, now retired;
- [`B0007`](B0007.json): W08, branch
  `codex/reorg-2026-08-w08-matrix-inversion-ch14`, 42 exact historical owners,
  42 reviewed production destinations plus test and delivery prefixes, sole
  operator `claude-remote`, retired projection P0008, and immutable delivery
  `664d5d495975a05d74cd4c0c09f9207aff8cdd77`, with applied shared request
  R0006, now retired.

Their hash-pinned reviews are
[`B0006-overlap-review.md`](B0006-overlap-review.md) and
[`B0007-overlap-review.md`](B0007-overlap-review.md). They prove zero owner,
destination, direct-import, signature-edge, and body-edge overlap. Their sole
common direct downstream importer is the integrator-owned
`NumStability/Algorithms.lean`. C0007 is current, M06/M08 remain accepted, and
M04/M09/M11 are accepted while M07/M10 are ready but unactivated. The two exact remote delivery refs
were deleted atomically with expected-SHA leases at `2026-08-04T13:33:21Z` by
`primary-human`. Local worker branches and worktrees are preserved and were
never retirement targets.

[`B0001`](B0001.json) is retired: W01 delivery
`d30fecc70a1d2066e2d147b79d9e6b9d743a21e5` is an ancestor of green checkpoint
C0002. [`B0002`](B0002.json) is retired after acceptance at C0003: W02 delivery
`799d781971eed851cd90152c0d9acb0e828f9341` is an ancestor of checkpoint commit
`bb80c95a4625e07535dacdda12d246ee1a5795b3`, and its remote ref was deleted at
`2026-08-02T23:32:59Z` after the C0003 control record was published green.

Two phase branches were implemented from the exact C0004 code commit, accepted
at C0005 code commit `240c0d041781385a647fbec461d6863537e562cb`
through separate true merges, and retired after the C0005 acceptance-control
commit passed CI. The planned control commit
`50dcbbc9cf871b7b0aadf262140c0758c354d7fc` passed
[Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30781486823)
before either branch name or worktree was created:

- [`B0004`](B0004.json): W03, branch
  `codex/reorg-2026-08-w03-cholesky-ch10`, 26 exact historical owners and 34
  exact vacant destination/evidence prefixes, sole operator `claude-local`,
  projection P0005, delivery
  `a36ea332cb8e19ed4f6985d1a22e8e356c5dc9ce` from worktree
  `C:\Users\qed_s\higham-worktrees\reorg-w03-claude`;
- [`B0005`](B0005.json): W05, branch
  `codex/reorg-2026-08-w05-ch16-ch18`, 10 exact historical owners and 16 exact
  vacant destination/evidence prefixes, sole operator `codex-local`,
  projection P0006, delivery
  `23883bb9e477a2645ce76213687c73584651c077` from worktree
  `C:\Users\qed_s\higham-worktrees\reorg-w05-codex`.

The two records have zero owner overlap, destination overlap, direct imports,
or typed signature/body edges. Their only common direct downstream importer is
the integrator-owned `NumStability/Algorithms.lean` aggregate. The independent
hash-pinned reviews are [`B0004-overlap-review.md`](B0004-overlap-review.md)
and [`B0005-overlap-review.md`](B0005-overlap-review.md). B0004 links applied
R0003 and B0005 links applied R0004; both patches remain independently based
on C0004. Their exact delivery tips are ancestors of C0005, P0005 and P0006
passed against the same integrated candidate, and both records are retired.
The two exact remote refs were deleted at `2026-08-03T15:23:25Z` by
`primary-human`; local worktrees and branches were preserved and were never
retirement targets.

The final retired branch is:

- [`B0003`](B0003.json): W12, branch
  `codex/reorg-2026-08-w12-ch01-ch02-ch05`, 42 exact owners and 65 destination
  roots from C0002. Delivery
  `380d3cba83bb9e3704232720f371f28cbbc673da` is an ancestor of accepted C0004
  commit `b56f609f3bf66b5d7d0b677567cce82fee0c275b`. Its remote ref was deleted at
  `2026-08-03T01:04:19Z` after the C0004 acceptance-control commit passed CI.

Workers may change only the exact owned paths and vacant destination roots in
their record. Focused tests and delivery evidence must stay below the recorded
wave prefixes; phase controls, global aggregates, root tests, and architecture
manifests are forbidden. Workers never edit the registry or mark their own
delivery accepted.

W02 was integrated before W12. The C0003 refresh recorded seven import-only
same-path overlaps and preserved the delivered branch's 17 direct W12-to-W02
dependency pairs for integrator reconciliation. The C0004 integration rewrote
those pairs to accepted W02 canonical leaves, preserved the reviewed C0003
imports, updated the shared wiring, and passed every global gate. After the
C0004 control commit became green, B0003 was deleted remotely and recorded
retired.

Both worker branches were created from C0004 code SHA
`b56f609f3bf66b5d7d0b677567cce82fee0c275b`, not from the later control
commit, and their initial local and remote tips were verified equal to that
SHA before B0004 and B0005 advanced from `planned` to `active`.
