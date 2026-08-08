# Reorganization phases

The active operating contract is the
[`2026-08 repository reorganization`](2026-08-repository-reorganization/README.md).
It has precedence over dated migration packets and historical handoffs.

Its current accepted checkpoint is C0007 at code commit
`9eb534a06db267203c2b9b88227edd44fc64f5db`. M03, M04, M05, M06, M08, M09,
and M11 are accepted; M07 and M10 remain ready and unactivated. B0008/W04,
B0009/W09, and B0010/W11 are accepted at C0007 with retirement due;
P0009/P0010/P0011 are retired and R0007/R0008/R0009 are applied. Their three
exact remote refs and the clean W09/W11 delivery worktrees remain present until
the C0007 acceptance-control commit passes Lean CI; W04 remains remote-only.
B0006/W06 and B0007/W08 are accepted at C0006 and retired; their exact remote
refs were deleted at `2026-08-04T13:33:21Z` after the C0006 acceptance-control
commit passed Lean CI, while local branches and worktrees remain preserved.
B0004/W03 and B0005/W05 are
accepted at C0005 and retired; their exact remote delivery refs were deleted
after the C0005 acceptance-control commit passed Lean CI.

Closed or superseded phases remain here as immutable evidence. A retained
phase must identify its status and successor rather than silently changing its
original scope.
