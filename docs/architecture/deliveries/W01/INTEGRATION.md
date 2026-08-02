# W01 integration delta

The worker delivery report describes remote tip
`d30fecc70a1d2066e2d147b79d9e6b9d743a21e5`, whose implementation begins at
`81f30e4b88040f00e7bb5193d167fc9f68b09bfd`. Global acceptance required the
following integrator-owned refinements beyond that worker tree.

## Semantic boundary refinement

- `ExactSubtraction` (179 declarations) and `StandardModel` (47 declarations)
  moved from Chapter 2 implementation leaves to reusable
  `NumStability.Analysis.FloatingPointArithmetic` leaves. Their Chapter 2 paths
  remain import-only source-correspondence entry points.
- Seven reusable or reusable-reachable consumers were retargeted from the mixed
  historical facade to the exact reusable leaves they use: `DotProduct`,
  `FastTwoSum`, compensated `FiniteFormat`, Kahan `Finite`, summation-tree
  `Core`, IEEE `NaiveMaximum`, and `OperationLaws`.
- The four declaration-bearing historical facades are classified as reviewed
  `mixed` residuals. The floating-point facade is also a reviewed
  declaration-bearing umbrella because Lean-private declaration identities
  cannot move.

This refinement makes the repository-wide strict-source graph honest: reusable
modules have zero direct or transitive reachability into source or mixed tiers.

## Shared and aggregate wiring

- The valid part of the worker's shared-file proposal was applied before the
  later W02/W12 branches were activated: `BeneficialRounding` and `Accumulation`
  now import their exact reusable leaves instead of the historical facade.
  These paths belong to future immutable waves rather than the phase's global
  shared-path set, so the adjustment is recorded here instead of as an invalid
  `Rxxxx` shared-state request.
- Chapter 1 and Chapter 2 aggregates now reach every new source entry point.
- Nine reusable leaves are classified explicitly, and all 20 canonical,
  source-wrapper, and old-import tests are reachable from `NumStabilityTest`.

## Pre-checkpoint evidence

- focused Lean build: 20 isolated W01 tests plus affected shared and reusable
  consumers, 3,038 jobs, exit 0;
- layout: 1,406 modules, 411 unclassified, 4 reviewed mixed residuals,
  13 reviewed declaration-bearing umbrellas, zero unsorted aggregate imports;
- compatibility: 296 forwarding modules and 566 canonical targets, pass;
- provenance: 207 Apache-marked production files and 5 evidenced upstream
  modules, pass;
- strict source graph: zero forbidden reusable reachability, pass;
- phase-contract self-test: pass.

The accepted checkpoint record supplies the hash-pinned projection replay,
combined baseline, full build, full tests, and GitHub CI evidence.
