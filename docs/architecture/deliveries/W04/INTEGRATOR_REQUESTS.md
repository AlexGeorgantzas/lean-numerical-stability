# W04 integrator requests

W04 intentionally leaves every integrator-owned, accepted-owner, aggregate,
control, or W90 path untouched.  Four follow-up groups are required after
accepting this delivery, and one retained W90 boundary must remain historical.

## 1. Retarget the protected equality-constrained least-squares consumer

In
`NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean`,
replace exactly this import:

```lean
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec
```

with:

```lean
import NumStability.Source.Higham.Chapter21.Equation04.Pseudoinverse
```

Do not otherwise change that consumer.  The requested endpoint re-exports the
canonical reusable pseudoinverse contract together with the exact equation
21.4 wrappers used by the consumer.  W04 preserves the old import meanwhile,
so the worker branch remains buildable before integration.

The isolated `IntegratorCanonicalRetarget` test imports only that endpoint and
checks all ten W04 declarations referenced by the consumer.

## 2. Retarget the Wedin perturbation consumer

In `NumStability/Analysis/Perturbation/LeastSquares/Wedin.lean`, replace exactly:

```lean
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec
```

with:

```lean
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
```

The only W04 declaration used by `Wedin` is
`NumStability.RectMoorePenrosePseudoinverse`, owned by that exact canonical
leaf.

This single replacement removes every repository-wide strict-source failure
introduced by the temporary compatibility edge.  The worker-time strict
source scan reports 56 paths: 14 classified reusable entrypoints multiplied
by four exact Chapter 21 source targets, all passing through
`Wedin -> UnderdeterminedSpec`.  There are zero W04 reusable-destination to
Source paths.

## 3. Wire the W04 test aggregate

Create the integrator-owned module
`NumStabilityTest/Reorganization/W04.lean` importing every test module listed
in `docs/architecture/deliveries/W04/TEST_MATRIX.tsv`, then add:

```lean
import NumStabilityTest.Reorganization.W04
```

to `NumStabilityTest.lean`.  W04 builds every matrix entry explicitly and does
not edit either aggregate path.

## 4. Apply aggregate, tier, and reviewed layout-ratchet wiring

Import the new canonical leaves through the normal shared aggregate chain:

```text
NumStability.lean
NumStability/All.lean
NumStability/Algorithms/LinearSystems.lean
NumStability/Source.lean
NumStability/Source/Higham.lean
NumStability/Source/Higham/Chapter21.lean
NumStability/Source/Higham/Chapter21/Theorem04.lean
```

Add the 31 reusable production modules to the reusable tier in
`docs/architecture/tiers.json`; physical `NumStability/Source` modules remain
source-tier modules.  After aggregate and tier wiring, run the review-only
`python tools/architecture/check_layout.py --write-baseline` update to
`docs/architecture/layout-exceptions.json`.  This removes fifteen stale
missing-docstring entries for improved historical facades and records the five
reviewed destination names that the current naming heuristic flags:

```text
NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.StoredReplay.Closure
NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.ActualOutput
NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.HouseholderClosure.Closure
NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.HouseholderClosure.Uniform
NumStability.Source.Higham.Chapter21.Corrections.Problem19_12.RoundedReplay
```

The worker-time `check_layout.py` run exits 1 only on this forbidden shared
state: 124 tests not yet root-reachable; 31 reusable modules not yet tiered;
15 stale missing-docstring debt entries; the five names above; and missing
aggregate reachability of 1 / 28 / 1 / 32 / 32 / 39 / 14 descendants from
`NumStability`, `Algorithms.LinearSystems`, `All`, `Source`, `Source.Higham`,
`Source.Higham.Chapter21`, and `Source.Higham.Chapter21.Theorem04`,
respectively.  W04 does not work around any of those shared-path requirements.

## Retained W90 historical boundary

Do not retarget
`NumStability/Source/Higham/Chapter21/Theorem04/RowwiseBackwardError.lean`
away from `NumStability.Algorithms.Underdetermined.UnderdeterminedSolve` in
this integration.  It uses the retained declaration
`NumStability.higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma`,
so the historical import is required by the exact 220-declaration private
reverse closure.  The static audit pins this and the temporary `Wedin` import
as the only two allowed source-canonical-to-historical boundary edges; reusable
destinations reach neither edge.
