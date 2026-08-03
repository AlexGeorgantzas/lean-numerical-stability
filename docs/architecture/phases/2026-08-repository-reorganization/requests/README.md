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

Both patches are independently based on C0004 and apply cleanly to a fresh
C0004 index. They are phase-control artifacts on main and were intentionally
absent from the C0004-based worker branches. R0003 and R0004 were applied in
code commit `240c0d041781385a647fbec461d6863537e562cb` and resolved at C0005 at
`2026-08-03T15:09:38Z` by `primary-human`; their common validation artifact is
the hash-pinned C0005 gate record. No shared-file request is currently active.
