# Reorganization phases

The active operating contract is the
[`2026-08 repository reorganization completion`](2026-08-repository-reorganization-completion/README.md),
selected by [`active-phase.json`](active-phase.json). It is rooted at C0000 on
accepted predecessor code commit
`b1b18772d80185ec08f49c818919558645c330a1`; its current checkpoint is C0003
at green code commit `e20de2f931caa12221e708c341e9cb4f64d29b25`. C0003 accepts R03 on top of
C0002's accepted R11/R12 and C0001's accepted R01/R02 integrations. This
successor has precedence over
dated migration packets and historical handoffs.

After C0001 acceptance-control commit
`93883eb0ec69a01704ff24ac71713a03f0be5a49` passed Lean CI run 31542177523
(job 93946871439), B0001/B0002 were retired at
`2026-08-11T22:34:24Z`; their exact remote refs were deleted with expected-tip
leases and verified absent. Their ignored evidence is archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0001-R01-R02-20260811`,
and both clean named worker worktrees were removed without force. Local branch
refs remain preserved at the immutable delivery tips.

B0003/R11 (QR and Chapter 19) and B0004/R12 (Chapter 13 equations and Table 01)
were delivered from exact C0001 code
`117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` at immutable tips
`444a03259af510bdfe0921d1847b6add1b26ed73` and
`0726678a0f2db56e533f3b956a2f7f1531059d7d`, respectively. Separate true merge
commits `10169717ce4966e9963885b04e7b7733a3bc7730` and
`1495047a1befb1431f0501cf7a423c8e77f8661a` preserve both deliveries. After
both merges, the reviewed 133-path R0003/R0004 union was applied exactly once
from its common C0001 preimage; sequential whole-file request replacement was
not used. The bounded integration follow-up completes the Chapter 19
`Sensitivity` and `StoredLoop` aggregates and records self-ratcheting
exceptions for exactly the two retained historical imports in byte-identical
`Chapter19.Core`. Exact-code Lean CI run 31673501960 (job 94362951630) passed
for `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`. At C0002, M11/M12 are
accepted, B0003/B0004 are retired, P0003/P0004 are retired immutable evidence,
and R0003/R0004 are applied. Acceptance-control commit
`c92c48a348a0e09e7d6ac9d4ff1db7673a027648` passed Lean CI run 31678412178
(job 94378054384) before both exact remote refs were deleted with expected-tip
leases. Ignored delivery evidence is hash-verified under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0002-R11-R12-20260813`,
both clean named worker worktrees were removed without force, and local branch
refs remain preserved at the immutable delivery tips. The temporary
`codex-local` authorization expired at C0002 and `claude-lane` is restored to
its single `claude-local` operator. C0002 recorded 2,642 production modules and
356 distinct residual-debt rows, including 277 unclassified modules, so neither
bounded nor repository-wide completion was claimed. A fresh exact-C0002
singleton review advanced M03/R03 to ready/active controls B0005/P0005/R0005.
Planned-control commit `fb5a021b4640dd595a99f7560ce252ad9836a5b6`
passed Lean CI run 31691727184 (job 94420320315) before B0005 was created
explicitly from exact C0002 code, pushed as a new remote ref with a
nonexistent-tip lease, and activated with its clean LF-configured named
worktree. A reviewed temporary second-operator expansion (`claude-local`,
control `c4f66cbdf`) and a reviewed fanIn7 private-closure route amendment
(control `09b3962dc`) followed, each with green Lean CI. The R03 delivery landed
at immutable tip `1f8ff4ca5` (parent exact C0002), is preserved by true merge,
and the same-C0002 R0005 request was applied exactly once.

C0003 accepts M03/R03 at exact green code commit
`e20de2f931caa12221e708c341e9cb4f64d29b25` (Lean CI run 31799323377). Against
the expected R0005 postimage, 115 request paths are byte-exact and exactly six
contain only their reviewed bounded deviations: two aggregate-sort
reconciliations, tier and compatibility reconciliation, the layout ratchet,
and the `Chapter27.SoftwareEnvironment` consumer import-superset repair. The
complete merge-to-integration audit separately accounts for exactly 21
additional paths: 11 aggregate follow-ups, 3 R03 test paths, 4 narrative
documents, and 3 milestone-DAG/evidence paths. At C0003, P0005 is retired
immutable evidence and R0005 is applied. After exact green control-chain head
`a61438448beb02773ef6b0f4f50cbedf8d675d29` passed Lean CI run 31833811860
(job 94875463331), `primary-human` retired B0005 at
`2026-08-14T19:44:43Z`. Its exact remote delivery ref
`refs/heads/codex/reorg-completion-2026-08-r03-floating-point-foundations-ch01-ch12`
was deleted under an expected-tip lease and verified absent. Seven ignored material artifacts
totaling 117,422,618 bytes were archived and verified at
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814`;
the named worktree `C:\Users\qed_s\higham-worktrees\completion-r03-codex` was
removed without force after its `.lake`-only residue was moved recoverably to
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0003-R03-20260814\disposable-worktree-residue\completion-r03-codex`.
The local
delivery branch remains preserved at
`1f8ff4ca5b0b136901a2f47d43e1064dc09aa556`. The
[`R03 retirement review`](2026-08-repository-reorganization-completion/reviews/R03-retirement.md)
records the exact lease, archive, residue, worktree, and local-ref evidence;
the hash-pinned
[`R03 activation review`](2026-08-repository-reorganization-completion/reviews/R03-activation.md)
preserves the earlier authority and activation facts. The temporary
`claude-local` second-operator authority on `codex-lane` has expired, restoring
that lane to `codex-local` alone. M05 and M06 are ready; M07/R07 and every other
unaccepted milestone remain planned, and no successor wave is activated.

C0003 records 2,690 production modules and 310 distinct residual-debt rows:
254 unclassified, zero mixed, zero missing-module-doc, 217 noncanonical, and 15
declaration-bearing-umbrella rows, with zero unsorted aggregate imports. The
inventory has 2,356 complete rows, 334 in-scope rows, and 310 rows with debt.
Bounded-phase and repository-wide completion remain incomplete.
The planned-control commit `c48d241532ad3dee12f4107a5e8875c7054159be`
passed Lean CI run 31546978830 (job 93961477202) before the R11/R12 refs and
clean named worktrees were created and activated.

[`R11-R12-retirement.md`](2026-08-repository-reorganization-completion/reviews/R11-R12-retirement.md)
records the acceptance CI, exact-lease deletions, archive manifest, clean
worktree removal, and local-ref preservation.

The immutable predecessor
[`2026-08 repository reorganization`](2026-08-repository-reorganization/README.md)
remains the historical record. Its final accepted checkpoint is C0008 at code commit
`b1b18772d80185ec08f49c818919558645c330a1`. M01 through M12 are accepted;
M90 is ready but remains unactivated, and repository-wide completion remains
incomplete. B0011/W07 and B0012/W10 were delivered from exact C0007 at
immutable tips
`176c72838828795b89f4aa822479010c7860c8e5` and
`9e7604cbdbd2314bc4bf38bcd9e342c3accfb1d6`, respectively. Separate true
merge commits preserve both deliveries. C0008 accepts both waves; P0012/P0013
are retired immutable evidence and independently C0007-based R0010/R0011 are
applied. Both branch records are accepted and retired. After C0008
acceptance-control commit `5d047643efbc06e69d380a4266010d9f48d934e1`
passed [Lean CI](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/31469704946),
both exact remote refs were deleted atomically with exact expected-SHA leases
at `2026-08-11T07:47:20Z` by `primary-human`. The ignored W07 artifacts were
archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0008-W07-20260811`;
its named delivery worktree was removed without force, and both local branches
remain preserved at their immutable tips. The clean W10 post-delivery
integrator recovery/correction checkout at `C:\Users\qed_s\w10-worker`
remains preserved outside retirement. B0008/W04,
B0009/W09, and B0010/W11 are accepted at C0007 and retired;
P0009/P0010/P0011 are retired and R0007/R0008/R0009 are applied. After the
C0007 acceptance-control commit passed Lean CI, their three exact remote refs
were deleted atomically with exact expected-SHA leases at
`2026-08-08T22:05:06Z` by `primary-human`. W04 never had a local worktree. The
ignored W09/W11 delivery artifacts were archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0007-W09-W11-20260808`;
their named worktrees were removed, and their local branches remain preserved
at the immutable delivery tips.
B0006/W06 and B0007/W08 are accepted at C0006 and retired; their exact remote
refs were deleted at `2026-08-04T13:33:21Z` after the C0006 acceptance-control
commit passed Lean CI, while local branches and worktrees remain preserved.
B0004/W03 and B0005/W05 are
accepted at C0005 and retired; their exact remote delivery refs were deleted
after the C0005 acceptance-control commit passed Lean CI.

Closed or superseded phases remain here as immutable evidence. A retained
phase must identify its status and successor rather than silently changing its
original scope.
