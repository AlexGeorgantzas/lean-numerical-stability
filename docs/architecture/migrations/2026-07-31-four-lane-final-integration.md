# Four-lane reorganization integration

Date: 2026-07-31

This checkpoint closes the bounded four-worker reorganization that started at
`6487fc33088523b8f27ecde9ad613515b78f9977`. It integrates the recovered local
and remote deliveries without force-pushing or discarding the preserved crash
recovery branches.

## Integrated lanes

- Block LU / Chapter 13: the Phase 12 cutover and sibling cleanup remain the
  accepted base, with the final combined-tree checker scoped to the selected
  declaration graph.
- QR / Chapter 19: 59 historical owners and 3,991 declarations are represented
  by 60 canonical destinations and 59 compatibility wrappers. The post gate
  preserved 3,331 byte-identical compiler command groups, 98 reviewed private
  rewrites, 25,540 signature edges, and 35,878 body/proof edges.
- Least squares / Chapter 20: 41 historical owners and 5,129 declarations are
  represented by 73 destinations. The post gate preserved 4,694 compiler
  command groups and validated 43 lane compatibility wrappers and the resolved
  QR handoff.
- Classification / Chapters 9 and 11: Chapter 9 moved 4,420 declarations into
  20 canonical destinations. Chapter 11 moved 6,385 declarations from 66
  historical owners into 73 destinations after the Chapter 9 dependency
  boundary was integrated.

## Final classified-boundary correction

The least-squares tier prefixes intentionally carry a terminal dot in the
coordinator contract. `check_layout.py` normalized those prefixes, while
`generate_baseline.py` did not. The inconsistency caused the strict-source CI
capture to omit 32 least-squares family modules from classification.

The final integration normalizes prefixes in both tools and removes the lane
checker's broad QR/source import exemptions. Eleven source-coupled LSQ leaves
are now registered exactly as `source`; the other family leaves remain
`reusable`. With those honest classifications, the strict graph has zero
reusable-to-source edges, zero reusable-to-mixed edges, and zero forbidden
reachable pairs.

## Validation

- GitHub Lean CI passed at `22bafeb75b37899b116e81b3f0e8d0b96655b74a`
  before the documentation/tier-audit correction (6,134 jobs).
- `check_layout.py`: 1,390 modules, 457 unclassified, zero mixed, zero unsorted
  aggregates.
- `check_compatibility.py`: 254 wrappers and 524 documented direct targets.
- `check_provenance.py`: 207 Apache-marked files and five evidenced upstream
  modules.
- strict source capture: 933 classified modules (67.122%), zero import cycles,
  and no forbidden classified edge or reachable pair.
- least-squares checker negative self-test: passed after removal of the import
  exemptions.
- Chapter 9 semantic post gate: 4,420 declarations, 23,898 typed internal
  edges, 56 destination-DAG edges, and 28 authored private rewrites passed.
- Chapter 11 semantic post gate: 6,385 declarations, 81,069 typed internal
  edges, 289 destination-DAG edges, and 146 authored private rewrites passed.
- `lake build NumStability NumStabilityTest` passed on the exact integrated
  Lean source tree, and `lake test` passed after the source-neutral manifest,
  checker, and README updates. The final GitHub run is the release gate for
  this checkpoint.

The remaining 457 unclassified modules and other ratcheted queues are future
repository-wide cleanup. They are not unfinished work from these four bounded
lanes.
