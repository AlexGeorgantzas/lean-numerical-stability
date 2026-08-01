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
  command groups and validated 43 physical lane compatibility wrappers (41
  migrated declaration-bearing owner rows plus two pre-existing compatibility
  wrappers) and the resolved QR handoff.
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

- The immutable handoff packet verified all 62 manifest entries, all 189
  recovered source-overlay files byte-for-byte, and the recovered Block LU
  branch scope (two commits, 189 touched paths, and 155 new paths).
- The Block LU ownership checker passed its negative self-test, pristine pre
  gate, complete 1,990/1,990-declaration stage gate, clean source-wave post
  gate, and final combined-tree post gate. The final graph differs from the
  frozen graph only by the four reviewed private-helper body-edge drops.
- The QR, least-squares, Chapter 9, and Chapter 11 post gates were rerun on the
  final combined tree and passed with the declaration and typed-edge counts
  recorded above.
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
- Ten representative final-tree axiom probes spanning Block LU, QR,
  least-squares, Chapter 9, and Chapter 11 reported exactly the accepted
  `[propext, Classical.choice, Quot.sound]` set.
- `lake build NumStability NumStabilityTest` passed on the exact integrated
  Lean source tree, and `lake test` passed after the source-neutral manifest,
  checker, and README updates.
- [GitHub Lean CI run 30657426120](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30657426120)
  passed the architecture/source-graph checks and the Lean build at
  completion-audit commit `298f57e88d4d83ace07151587dffebd1ac0637df` in 3 minutes
  15 seconds. The integrated Lean source first passed at
  `dfdeb3eb3f664d3ab7ae91f27267fa39de734b02`; the tree diff from that commit
  through `298f57e88` changes only this migration report.

The remaining 457 unclassified modules and other ratcheted queues are future
repository-wide cleanup. They are not unfinished work from these four bounded
lanes.
