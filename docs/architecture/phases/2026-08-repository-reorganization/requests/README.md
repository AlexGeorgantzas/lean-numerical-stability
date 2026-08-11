# Shared-file requests

Workers do not edit integrator-owned manifests, root aggregates, tests, CI, or
phase checkpoints directly. The integrator creates one `Rxxxx.json` plus its
hash-pinned `Rxxxx.patch` here for every requested shared change. A request is
valid only through its target checkpoint and must become applied, rejected,
withdrawn, expired, or superseded when that checkpoint changes.

R0001 and R0002 are terminal applied records that retroactively register the
exact, hash-pinned integrator-owned deltas accepted at C0003 for W02 and at
C0004 for W12, respectively.

Accepted B0011/W07 and B0012/W10 link applied R0010 and R0011, respectively.
Workers kept global aggregates, test roots, tier/layout manifests, phase
controls, CI, and accepted consumers untouched. Both requests are independently
hash-pinned against exact C0007 and replay forward and reverse. Their only
intersections are `NumStabilityTest.lean`, `docs/architecture/tiers.json`, and
`docs/architecture/layout-exceptions.json`; the integrated postimages are
reviewed unions rather than sequential patch applications.
The immutable W10 worker packet also requests the accepted W06 destination
`NumStability/Algorithms/NormEstimation/OneNorm/All.lean`. Schema version 1
correctly prevents reclassifying that historical destination as shared, so its
exact postimage is tracked in the R0011 overlap review and integrated as a
separate W06/W10 overlap outside the 13-path formal request.

| Request | Wave | Requester / lane | Status | Target | Valid through | Paths | Patch SHA-256 | Blocks |
| --- | --- | --- | --- | --- | --- | ---: | --- | --- |
| [`R0003`](R0003.json) | W03 | `claude-local` / `local-lane` | applied | C0004 / `b56f609f3bf66b5d7d0b677567cce82fee0c275b` | C0004 | 47 | `8AABF97189D3788AA6D6FA79A03810500507A46E9F5CE78091E71D862BB93476` | W03 |
| [`R0004`](R0004.json) | W05 | `codex-local` / `local-lane` | applied | C0004 / `b56f609f3bf66b5d7d0b677567cce82fee0c275b` | C0004 | 27 | `65064084E1F5B53F4C6CD8C59802D9B443DFB05A5BCCA4682544E4AA74F710CC` | W05 |
| [`R0005`](R0005.json) | W06 | `codex-remote` / `remote-lane` | applied | C0005 / `240c0d041781385a647fbec461d6863537e562cb` | C0005 | 73 | `C7F94237B46745BFAC501780D806499431CECBFBDBFA7B70798E801716115D42` | W06 |
| [`R0006`](R0006.json) | W08 | `claude-remote` / `remote-lane` | applied | C0005 / `240c0d041781385a647fbec461d6863537e562cb` | C0005 | 76 | `54693108C1627E5DA067B16A520D009EFCCEEE2A2D81930B756CD5A69B6D9504` | W08 |
| [`R0007`](R0007.json) | W04 | `codex-remote` / `remote-lane` | applied | C0006 / `a32095e6e50189f7dcc39312bb4c6a36f421fab5` | C0006 | 8 | `5EB1ACF5C24D51ACB7F2FD6A258E8D53A2EFEBE09E77116539B4D85DE0D8114C` | W04 |
| [`R0008`](R0008.json) | W09 | `claude-local` / `local-lane` | applied | C0006 / `a32095e6e50189f7dcc39312bb4c6a36f421fab5` | C0006 | 6 | `BB602D4C854416DDA7F6FC7D69445093A53F496931718C34461BE476A32BF3AC` | W09 |
| [`R0009`](R0009.json) | W11 | `codex-local` / `local-lane` | applied | C0006 / `a32095e6e50189f7dcc39312bb4c6a36f421fab5` | C0006 | 7 | `E98E798A177831802DA9F36B1753EA1D31BDE707F17F0DF55E63D6DC6B4CDB68` | W11 |
| [`R0010`](R0010.json) | W07 | `codex-local` / `local-lane` | applied | C0007 / `9eb534a06db267203c2b9b88227edd44fc64f5db` | C0007 | 6 | `E05687DC8959C8B3B24DE30E996553A780839CB2C501D5A0BBBF6A39B40BF425` | W07 |
| [`R0011`](R0011.json) | W10 | `claude-remote` / `remote-lane` | applied | C0007 / `9eb534a06db267203c2b9b88227edd44fc64f5db` | C0007 | 13 | `71D9BD0B68C82848DAD3EBA4260A3F81FC4EF302524A68D14A449332BDA97F7A` | W10 |

R0010 and R0011 apply independently to exact C0007. Their hash-pinned overlap
reviews are [`R0010-overlap-review.md`](R0010-overlap-review.md) and
[`R0011-overlap-review.md`](R0011-overlap-review.md). The requests were applied
in green code commit `b1b18772d80185ec08f49c818919558645c330a1` and resolved
at C0008 at `2026-08-11T07:00:00Z` by `primary-human`; their validation
evidence is the hash-pinned C0008 gate record. After C0008 acceptance-control
commit `5d047643efbc06e69d380a4266010d9f48d934e1` passed Lean CI, both exact
remote refs were deleted atomically with exact expected-SHA leases at
`2026-08-11T07:47:20Z` by `primary-human`. The ignored W07 artifacts were
archived under
`C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0008-W07-20260811`;
its named delivery worktree was removed without force, and both local branches
remain preserved at their immutable delivery tips. Request application alone
did not authorize early branch deletion. The clean post-delivery W10 integrator
recovery/correction checkout
at `C:\Users\qed_s\w10-worker` remains preserved outside worker retirement.

Both patches are independently based on C0004 and apply cleanly to a fresh
C0004 index. They are phase-control artifacts on main and were intentionally
absent from the C0004-based worker branches. R0003 and R0004 were applied in
code commit `240c0d041781385a647fbec461d6863537e562cb` and resolved at C0005 at
`2026-08-03T15:09:38Z` by `primary-human`; their common validation artifact is
the hash-pinned C0005 gate record.

R0005 and R0006 are independently based on C0005 and validate against separate
disposable C0005 indexes. They register only integrator-owned shared files;
hash-pinned accepted-consumer and W07/W11 import-only overlap changes remain
outside the shared patches and are reconciled in the integrated tree. Fifteen
W06 umbrellas nested beneath retired B0005 destination prefixes are likewise
recorded as exact W05/W06 integration overlaps because schema version 1
correctly rejects reclassifying those historical destination paths as shared.
The independently hash-pinned overlap ledgers are
[`R0005-overlap-review.md`](R0005-overlap-review.md) and
[`R0006-overlap-review.md`](R0006-overlap-review.md).

R0005 and R0006 were applied in green code commit
`a32095e6e50189f7dcc39312bb4c6a36f421fab5` and resolved at C0006 at
`2026-08-04T13:15:16Z` by `primary-human`. Their validation evidence is the
hash-pinned C0006 gate record. After the C0006 acceptance-control commit passed
Lean CI, the related B0006/B0007 remote refs were deleted atomically with exact
expected-SHA leases at `2026-08-04T13:33:21Z`; request resolution alone did not
authorize early branch deletion.

B0008/W04, B0009/W09, and B0010/W11 were delivered from C0006 and link applied,
independently C0006-based requests R0007, R0008, and R0009. Their patches were
validated separately against disposable C0006 indexes. All three intersect on
the root test aggregate, tier manifest, and layout exceptions; R0007 and R0009
also intersect on the accepted least-squares Equality consumer. Those shared
postimages were reconciled as deliberate unions rather than sequential patch
applications. The hash-pinned ledgers are
[`R0007-overlap-review.md`](R0007-overlap-review.md),
[`R0008-overlap-review.md`](R0008-overlap-review.md), and
[`R0009-overlap-review.md`](R0009-overlap-review.md). The requests were applied
in green code commit `9eb534a06db267203c2b9b88227edd44fc64f5db` and resolved
at C0007 at `2026-08-08T21:26:00Z` by `primary-human`. Their validation evidence
is the hash-pinned C0007 gate record. B0008, B0009, and B0010 are accepted and
retired. After the C0007 acceptance-control commit passed Lean CI, their exact
remote refs were deleted atomically with exact expected-SHA leases at
`2026-08-08T22:05:06Z` by `primary-human`. Request resolution did not itself
authorize early branch deletion.
