# Branch registry

One JSON record is tracked per phase branch. A planned branch must start from
the current accepted checkpoint and use an active lane baseline projection.
Delivery, integration, ancestry, and retirement fields are updated rather than
replaced by prose-only status messages.

[`B0001`](B0001.json) is retired: W01 delivery
`d30fecc70a1d2066e2d147b79d9e6b9d743a21e5` is an ancestor of green checkpoint
C0002. [`B0002`](B0002.json) is retired after acceptance at C0003: W02 delivery
`799d781971eed851cd90152c0d9acb0e828f9341` is an ancestor of checkpoint commit
`bb80c95a4625e07535dacdda12d246ee1a5795b3`, and its remote ref was deleted at
`2026-08-02T23:32:59Z` after the C0003 control record was published green.

Two phase branches were implemented from the exact C0004 code commit and are
accepted at C0005 code commit `240c0d041781385a647fbec461d6863537e562cb`
through separate true merges. The planned control commit
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
passed against the same integrated candidate, and both records now have
retirement due. The two remote refs remain present until this acceptance-control
commit passes CI; local worktrees and branches are not retirement targets.

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
