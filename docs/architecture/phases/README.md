# Reorganization phases

The active operating contract is the
[`2026-08 repository reorganization completion`](2026-08-repository-reorganization-completion/README.md),
selected by [`active-phase.json`](active-phase.json). It is rooted at C0000 on
accepted predecessor code commit
`b1b18772d80185ec08f49c818919558645c330a1`; its current checkpoint is C0001
at green code commit `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`. C0001 accepts R01/R02. After
acceptance-control commit `93883eb0ec69a01704ff24ac71713a03f0be5a49`
passed Lean CI run 31542177523 (job 93946871439), B0001/B0002 were retired at
`2026-08-11T22:34:24Z`; their exact remote refs were deleted with expected-tip
leases and verified absent. Their ignored evidence is archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0001-R01-R02-20260811`,
and both clean named worker worktrees were removed without force. Local branch
refs remain preserved at the immutable delivery tips. This successor has
precedence over dated migration packets and historical handoffs.

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
`Chapter19.Core`. R11/R12 are integrated but remain unaccepted: M11/M12 are
ready, C0001 remains current, and C0002 awaits the full acceptance gates and
exact green code CI. Their selectors, format-2 projections, routes, private
closure, test plans, and same-preimage request union remain frozen. The
planned-control commit `c48d241532ad3dee12f4107a5e8875c7054159be` passed Lean CI run
31546978830 (job 93961477202) before both exact refs and clean named worktrees
were created and activated.

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
