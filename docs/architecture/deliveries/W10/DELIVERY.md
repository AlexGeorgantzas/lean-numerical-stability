# W10 delivery — norm estimation and Chapter 15

Wave W10 splits the 27 frozen owners of B0012 into canonical destinations: reusable
norm-estimation mathematics under `NumStability/Algorithms/NormEstimation/`, and exact
Chapter 15 correspondence under `NumStability/Source/Higham/Chapter15/`.

Base: C0007 `9eb534a06db267203c2b9b88227edd44fc64f5db`. Branch:
`codex/reorg-2026-08-w10-norm-estimation-ch15`. Projection: P0013. Selector: 27 owners,
SHA-256 `444AA9109E4990AD47E281D550EA7A80057A8DBC493D8AF1693760EE7434BBB0`.

## Scope

| quantity | value |
| --- | ---: |
| owners | 27 |
| declarations | 1029 |
| retained | 132 |
| relocated | 897 |
| to reusable NormEstimation | 492 |
| to Chapter 15 source | 405 |
| canonical destination modules | 96 |
| compatibility modules | 27 (13 declaration-bearing, 14 import-only) |
| test modules | 135 |
| source lines at base | 17,260 |

Retention is **132**, exactly the private reverse-closure floor recomputed from P0013
(80 private + 52 public). Nothing is retained beyond the floor. All **43** authorized
destinations are populated.

## Projection

The P0013 replay passed with every mandated count preserved: **1,029** declarations,
**2,394** signature edges, **4,844** body/proof edges, 897 relocated, 27 allow-modules and
43 allow-prefixes. 73 recorded arguments were replayed with only the candidate placeholder
substituted. See `PROJECTION.md`.

## Gates

Every gate within W10's authority passes on the worker branch, including both library
builds, all 135 test modules built as three separate sets, `lake test`,
`check_compatibility`, `check_provenance`, the candidate and the replay.

Two gates fail on the worker branch and pass under the disposable integrator patch
described in `INTEGRATOR_REQUESTS.md`: `check_layout` and `--strict-source`. Both failures
live entirely in files B0012 forbids this wave to touch — `tiers.json`,
`layout-exceptions.json`, the `Source/Higham` and `NumStabilityTest` aggregates, and 33
accepted consumers. The patch is deterministic, is reproduced by `patch.py`, and takes
strict-source reachability from 55 pairs to **0** and `check_layout` to **0** errors.

An honest note on measurement: an earlier PowerShell gate harness reported `check_layout`
as `exit=0` with an empty log while the checker was in fact failing with five errors --
`& $block *> file` did not carry the native exit code back. Every result in
`GATE_RESULTS.tsv` is now taken from a `subprocess.run` return code with its output
captured beside it, so no pass is inferred from silence.

## Findings

1. **A carried ambient binder has dependencies of its own.** Emitting `variable
   (P : PNormPair n)` positionally is not enough; whatever it mentions must be importable.
   The first repair over-corrected by matching binder names textually -- `n` is an
   extremely common local -- which created an import cycle. The rule is edge-based: carry a
   binder that mentions wave declarations only when an emitted declaration has a typed
   P0013 edge to one.
2. **A frozen projection cannot see the consumer boundary.** W10's in-wave reusable-to-
   source and canonical-to-historical edge counts are both zero, yet 55 module-level pairs
   appeared repository-wide, because P0013 holds only this wave's 1,029 declarations.
3. **The algorithm definitions are reusable; the printed results are source.**
   `oneNormPowerMethod`, `oneNormStep`, `lapackNormEstimator` and `lapackAltVec` were first
   routed to Source as Algorithms 15.3 and 15.4. Because the `CondEstimation` facade must
   import its destinations for historical paths to resolve, that made 53 accepted reusable
   modules reach Source. Routing the definitions reusable and leaving the `H15_Algorithm15_*`
   correspondence in Source resolved it and filled `R:OneNorm/LAPACK`, which had been
   authorized-but-unpopulated for exactly the same reason.

## Changed paths

36 entries: 27 owner facades rewritten, 96 canonical destinations,
135 test modules and the evidence artifacts. No integrator-owned file is touched;
`apply.py` rejects them structurally. See `CHANGED_PATHS.md`.
