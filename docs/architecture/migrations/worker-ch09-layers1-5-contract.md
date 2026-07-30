# Chapter 9 destination-DAG layers 1--5 contract

This contract freezes the first dependency-closed Chapter 9 source migration
wave before any production declaration is moved.  The implementation base is
remote-main commit `32771e355612a6fca1b6153733d3f0dc124d26e2`; the reviewed
classification evidence is `9e7c8e32437d6ea28bf297fc4f08756288df9b26`, and
all eleven candidate production paths have byte-identical Git blobs at those
two revisions.  Exact source-command spans remain pinned to the packet graph
at `6487fc33088523b8f27ecde9ad613515b78f9977`.

## Frozen wave

The full Chapter 9 owner DAG mechanically yields these first five layers:

| Layer | Destinations | Declarations | Command groups |
| --- | ---: | ---: | ---: |
| 1 | `Section01`, `Theorem914Primitive` | 49 | 49 |
| 2 | `Section02` | 334 | 259 |
| 3 | `ComputedCorrection`, `Section03`, `Section04` | 545 | 461 |
| 4 | `Section05` | 163 | 141 |
| 5 | `Section06` | 584 | 584 |
| **Total** | **8** | **1,675** | **1,494** |

The three historical owners are `HighamChapter9` (partial in this wave),
`HighamChapter9Theorem914Primitive` (complete), and
`HighamChapter9ComputedCorrection` (complete).  Ten authored private
declarations have explicit destination-qualified rewrites; the frozen graph
has no cross-destination use of one of those private helpers.

## Evidence and enforcement

`check_ch09_layers1_5.py` deterministically derives every tracked artifact
from the reviewed full Chapter 9 contract and the immutable format-2 packet.
It rejects a different layer partition, owner or destination set, route,
compiler span, source-command hash, import set, private rewrite, or
evidence-to-base production change.  The baseline contains 11,393 signature
edges and 14,167 body/proof edges incident to the wave, including 8,966 typed
internal edges.

Stage mode requires a fresh format-2 graph.  It normalizes historical and
destination-qualified private names to their frozen logical identities, then
compares every incident signature and body/proof edge exactly.  It also
re-hashes every compiled destination command through the new `.ilean` spans,
requires all 1,494 commands to be byte-identical, and rejects uncontracted
declarations in any of the eight destinations.

The materializer is deliberately deterministic.  It creates eight canonical
source modules and isolated canonical-only/old-only tests, turns the two fully
migrated historical owners into exact import-only wrappers, and removes only
the reviewed commands from the giant historical owner while adding canonical
imports.  Later Chapter 9 destinations remain declaration-bearing in that
historical file until their own dependency-ordered wave.

The pre gate passed with the packet archive SHA-256
`1C2538B428B8EC3610B3C09BBB6A4CF23ECA9F0DB17EE4AE5B63E4F371AECDED`.
No shared root, aggregate, tier, layout-exception, or compatibility manifest is
owned by this worker wave.
