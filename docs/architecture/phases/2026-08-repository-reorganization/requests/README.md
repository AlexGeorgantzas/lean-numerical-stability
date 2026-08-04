# Shared-file requests

Workers do not edit integrator-owned manifests, root aggregates, tests, CI, or
phase checkpoints directly. The integrator creates one `Rxxxx.json` plus its
hash-pinned `Rxxxx.patch` here for every requested shared change. A request is
valid only through its target checkpoint and must become applied, rejected,
withdrawn, expired, or superseded when that checkpoint changes.

R0001 and R0002 are terminal applied records that retroactively register the
exact, hash-pinned integrator-owned deltas accepted at C0003 for W02 and at
C0004 for W12, respectively.

| Request | Wave | Requester / lane | Status | Target | Valid through | Paths | Patch SHA-256 | Blocks |
| --- | --- | --- | --- | --- | --- | ---: | --- | --- |
| [`R0003`](R0003.json) | W03 | `claude-local` / `local-lane` | applied | C0004 / `b56f609f3bf66b5d7d0b677567cce82fee0c275b` | C0004 | 47 | `8AABF97189D3788AA6D6FA79A03810500507A46E9F5CE78091E71D862BB93476` | W03 |
| [`R0004`](R0004.json) | W05 | `codex-local` / `local-lane` | applied | C0004 / `b56f609f3bf66b5d7d0b677567cce82fee0c275b` | C0004 | 27 | `65064084E1F5B53F4C6CD8C59802D9B443DFB05A5BCCA4682544E4AA74F710CC` | W05 |
| [`R0005`](R0005.json) | W06 | `codex-remote` / `remote-lane` | applied | C0005 / `240c0d041781385a647fbec461d6863537e562cb` | C0005 | 73 | `C7F94237B46745BFAC501780D806499431CECBFBDBFA7B70798E801716115D42` | W06 |
| [`R0006`](R0006.json) | W08 | `claude-remote` / `remote-lane` | applied | C0005 / `240c0d041781385a647fbec461d6863537e562cb` | C0005 | 76 | `54693108C1627E5DA067B16A520D009EFCCEEE2A2D81930B756CD5A69B6D9504` | W08 |

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
hash-pinned C0006 gate record. The related B0006/B0007 remote refs remain live
until the C0006 acceptance-control commit passes Lean CI; request resolution
does not itself authorize early branch deletion.
