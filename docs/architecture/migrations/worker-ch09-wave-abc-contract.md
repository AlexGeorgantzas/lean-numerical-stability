# Chapter 9 destination-DAG waves A--C contract

This contract freezes the dependency-ordered continuation of the Chapter 9
source migration before any wave-A, wave-B, or wave-C production declaration
is moved.  The implementation base is `e931cbacebce8ce8bbb50273a67a4644448436e5`,
after the separately frozen layers-1--5 migration.  Compiler-command source
spans remain pinned to packet revision
`6487fc33088523b8f27ecde9ad613515b78f9977`.

## Frozen sequence

| Wave | Destination(s) | Declarations | Command groups | Private |
| --- | --- | ---: | ---: | ---: |
| A | `DoolittleClosure`, `Section08`, `Section10` | 66 | 55 | 1 |
| B | `Section11` | 1,109 | 1,109 | 0 |
| C | `Problems` | 1,212 | 1,140 | 5 |
| **Total** | **5 destinations** | **2,387** | **2,304** | **6** |

Wave A is dependency-closed over the already materialized first five layers.
Wave B depends on wave A through `Section10`, and wave C depends on wave B
through `Section11`.  The two historical declaration owners are the partial
giant `HighamChapter9` and the one-destination
`HighamChapter9DoolittleClosure` owner.

The exact normalized incident-graph fingerprints are:

- A: `CE5209AEF0A587FBBED2DE1CF20F78B24A9A82A8AB22AB510C8E8B4D457445C5`;
- B: `EA7B097EA96D43230726592D672714F58224A80EAAC56DDA6BAA261ED2070B96`;
- C: `C6C5041485BE4E94EF56F9AF1ED6F2CD4C3DE39111DF8AC8C91F918AEE06A13A`.

The checker independently reproduces the audited signature/body/internal
edge counts of `963/999/169`, `5458/6816/3602`, and
`6180/8510/4695`, respectively.  It rejects any cross-destination consumer of
one of the six private helpers; none exists in the frozen graph.

## Import and compatibility policy

Each canonical destination receives the 27 direct non-Chapter-9 imports from
the post-BlockLU giant-owner base plus exactly its earlier destination-DAG
dependencies.  This yields 151 frozen import rows.  The proposal's historical
wrapper expansion is deliberately not copied literally, because importing
future Chapter 9 destinations would introduce cycles.

Wave A turns `HighamChapter9DoolittleClosure` into a one-target compatibility
wrapper and leaves the giant owner partial.  Wave B leaves only `Problems` in
the giant.  Wave C turns the giant into a declaration-free ten-target
compatibility facade.  Canonical-only tests import one destination; old-only
tests import one historical path without a root or sibling import.

## Evidence and deferred gates

The full 4,420-row Chapter 9 proposal pre-check and the A/B/C pre-check pass
against the immutable format-2 archive with SHA-256
`1C2538B428B8EC3610B3C09BBB6A4CF23ECA9F0DB17EE4AE5B63E4F371AECDED`.
The checker self-test, deterministic layers-1--5 precursor comparison, scope
allowlist, Python compilation, and `git diff --check` also pass.

No Lean build, `.ilean` command re-hash, candidate format-2 extraction, stage
comparison, axiom probe, or global build is claimed by this contract commit.
Those gates remain mandatory for the integrator under the named build mutex.
No shared root, tier, layout exception, compatibility map, QR, LSQ, or Chapter
11 path is owned by this worker sequence.
