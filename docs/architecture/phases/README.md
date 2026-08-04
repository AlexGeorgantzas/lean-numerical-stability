# Reorganization phases

The active operating contract is the
[`2026-08 repository reorganization`](2026-08-repository-reorganization/README.md).
It has precedence over dated migration packets and historical handoffs.

Its current accepted checkpoint is C0006 at code commit
`a32095e6e50189f7dcc39312bb4c6a36f421fab5`. M03, M05, M06, and M08 are
accepted; M04, M07, M09, and M11 are ready but not activated. B0006/W06 and
B0007/W08 are accepted at C0006 with retirement due; their exact remote refs
remain live until the C0006 acceptance-control commit passes Lean CI, while
local branches and worktrees remain preserved. B0004/W03 and B0005/W05 are
accepted at C0005 and retired; their exact remote delivery refs were deleted
after the C0005 acceptance-control commit passed Lean CI.

Closed or superseded phases remain here as immutable evidence. A retained
phase must identify its status and successor rather than silently changing its
original scope.
