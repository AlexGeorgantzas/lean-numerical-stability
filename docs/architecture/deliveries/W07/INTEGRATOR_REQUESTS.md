# W07 integrator requests

W07 does not create `R0010` and does not edit any shared aggregate, test root,
tier manifest, layout exception, compatibility manifest, accepted consumer, or
phase-control file.  The exact shared postimage below is requested from the
integrator.  Every preimage is checkpoint C0007 at
`9eb534a06db267203c2b9b88227edd44fc64f5db`.

## IR-W07-1: expose the complete W07 test matrix

### Paths and C0007 blobs

- `NumStabilityTest/Reorganization/W07.lean`: absent at C0007.
- `NumStabilityTest.lean`:
  `a3e450a3790c414dfee8f2c6eb8f1fee7e9cec74`.

### Minimal delta and postimage

Add `NumStabilityTest/Reorganization/W07.lean` with this complete postimage:

```lean
import NumStabilityTest.Reorganization.W07.Canonical.C001
import NumStabilityTest.Reorganization.W07.Canonical.C002
import NumStabilityTest.Reorganization.W07.Canonical.C003
import NumStabilityTest.Reorganization.W07.Canonical.C004
import NumStabilityTest.Reorganization.W07.Canonical.C005
import NumStabilityTest.Reorganization.W07.Canonical.C006
import NumStabilityTest.Reorganization.W07.Canonical.C007
import NumStabilityTest.Reorganization.W07.Canonical.C008
import NumStabilityTest.Reorganization.W07.Canonical.C009
import NumStabilityTest.Reorganization.W07.Canonical.C010
import NumStabilityTest.Reorganization.W07.Canonical.C011
import NumStabilityTest.Reorganization.W07.Canonical.C012
import NumStabilityTest.Reorganization.W07.Canonical.C013
import NumStabilityTest.Reorganization.W07.Canonical.C014
import NumStabilityTest.Reorganization.W07.Canonical.C015
import NumStabilityTest.Reorganization.W07.Canonical.C016
import NumStabilityTest.Reorganization.W07.Canonical.C017
import NumStabilityTest.Reorganization.W07.Canonical.C018
import NumStabilityTest.Reorganization.W07.Canonical.C019
import NumStabilityTest.Reorganization.W07.Canonical.C020
import NumStabilityTest.Reorganization.W07.Canonical.C021
import NumStabilityTest.Reorganization.W07.Canonical.C022
import NumStabilityTest.Reorganization.W07.Canonical.C023
import NumStabilityTest.Reorganization.W07.Canonical.C024
import NumStabilityTest.Reorganization.W07.Canonical.C025
import NumStabilityTest.Reorganization.W07.Canonical.C026
import NumStabilityTest.Reorganization.W07.Canonical.C027
import NumStabilityTest.Reorganization.W07.Canonical.C028
import NumStabilityTest.Reorganization.W07.Canonical.C029
import NumStabilityTest.Reorganization.W07.Canonical.C030
import NumStabilityTest.Reorganization.W07.Canonical.C031
import NumStabilityTest.Reorganization.W07.Canonical.C032
import NumStabilityTest.Reorganization.W07.Canonical.C033
import NumStabilityTest.Reorganization.W07.Canonical.C034
import NumStabilityTest.Reorganization.W07.Focused.AcceptedChapter17Consumers
import NumStabilityTest.Reorganization.W07.Focused.AcceptedSemiconvergentConsumer
import NumStabilityTest.Reorganization.W07.Focused.Chapter17Boundary
import NumStabilityTest.Reorganization.W07.Focused.Drazin
import NumStabilityTest.Reorganization.W07.Focused.PrivateRetention
import NumStabilityTest.Reorganization.W07.Focused.ProtectedW06
import NumStabilityTest.Reorganization.W07.Focused.ReusableIteration
import NumStabilityTest.Reorganization.W07.Focused.RoundedExecution
import NumStabilityTest.Reorganization.W07.Focused.SemiconvergenceProjector
import NumStabilityTest.Reorganization.W07.OldPath.StationaryIteration
import NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationDrazin
import NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationRounded
import NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationSemiconvergent
import NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationSemiconvergentExistence

/-!
# W07 reorganization tests

Declaration-free aggregate for the complete 48-module W07 delivery test matrix.
-/
```

Insert exactly
`import NumStabilityTest.Reorganization.W07` in the case-fold-sorted import
block of `NumStabilityTest.lean`, between W06 and W08.  No other root delta is
requested.

### Rationale, protected tests, and gate

The worker owns only the leaf-test prefix, so it cannot create the sibling
aggregate or edit the root.  The postimage exposes all 34 canonical-only, five
old-path-only, and nine focused tests to the public test target.  It protects
the entire `TEST_MATRIX.tsv`, especially `Focused.ProtectedW06`,
`Focused.AcceptedChapter17Consumers`, and
`Focused.AcceptedSemiconvergentConsumer`.  It unblocks the layout test-root
reachability check and makes `lake build NumStability NumStabilityTest` compile
the W07 leaves through the normal root.

## IR-W07-2: wire both complete production aggregates

### Paths and C0007 blobs

- `NumStability/Algorithms/LinearSystems.lean`:
  `fd3b04b44f419223d6470c2609552f63e42868fd`.
- `NumStability/Source/Higham/Chapter17.lean`:
  `be9b42ad5f8149dbc409e8c8fa6467443cf9da0e`.

### Minimal LinearSystems delta

Insert these nine direct imports after `GaussJordan` and before
`IterativeRefinement.All`, preserving case-fold order:

```lean
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
```

### Minimal Chapter17 delta

Preserve the eight existing imports and add these 25 direct Results imports;
the combined 33-line import block must remain case-fold sorted:

```lean
import NumStability.Source.Higham.Chapter17.Equation01.ComputedIteration.Results
import NumStability.Source.Higham.Chapter17.Equation02.LocalError.Results
import NumStability.Source.Higham.Chapter17.Equation03.ComputedRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation04.FixedPoint.Results
import NumStability.Source.Higham.Chapter17.Equation05.ErrorExpansion.Results
import NumStability.Source.Higham.Chapter17.Equation06.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation07.NormwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation08.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation09.ComponentwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation10.LocalErrorSimplification.Results
import NumStability.Source.Higham.Chapter17.Equation12.PartialSumBound.Results
import NumStability.Source.Higham.Chapter17.Equation13.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation15.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation16.Jacobi.Results
import NumStability.Source.Higham.Chapter17.Equation17.SOR.Results
import NumStability.Source.Higham.Chapter17.Equation18.ResidualRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation19.ResidualBound.Results
import NumStability.Source.Higham.Chapter17.Equation20.ResidualSigma.Results
import NumStability.Source.Higham.Chapter17.Equation21.SingularIteration.Results
import NumStability.Source.Higham.Chapter17.Equation27.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation28.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation29.SingularSource.Results
import NumStability.Source.Higham.Chapter17.Equation33.StoppingTests.Results
import NumStability.Source.Higham.Chapter17.Section02.ScaleIndependence.Results
import NumStability.Source.Higham.Chapter17.Section04.PrintedConclusions.Results
```

### Rationale, protected tests, and gate

Both paths are complete-prefix aggregates in `layout-exceptions.json`.  Direct
wiring gives discoverability without creating another umbrella and preserves
the accepted eight Chapter 17 imports.  Canonical tests C001--C034 and
`Focused.ReusableIteration`, `Focused.Chapter17Boundary`, and
`Focused.Drazin` protect the destinations.  The LinearSystems delta unblocks
the exact layout failure that its aggregate misses nine canonical descendants.
The current Chapter17 aggregate reaches the new leaves only incidentally via
its accepted Equation modules, their historical `StationaryIteration` import,
and that facade's new direct imports.  Adding the 25 direct imports makes the
complete-prefix aggregate honest and independent of historical-facade
reachability, while exposing every leaf through `NumStability`.

## IR-W07-3: classify canonical leaves and historical owners

### Path and C0007 blob

`docs/architecture/tiers.json`:
`c1afc0ad364fc908364114bfd63c5e0a2058baee`.

### Minimal delta and postimage

Add exact `reusable` rows for the nine LinearSystems modules listed in
IR-W07-2.  The existing `NumStability.Source` prefix already classifies all 25
Results leaves `source`; do not add redundant Source rows.

Add exact `mixed` rows for:

```text
NumStability.Algorithms.StationaryIteration
NumStability.Algorithms.StationaryIterationDrazin
NumStability.Algorithms.StationaryIterationRounded
NumStability.Algorithms.StationaryIterationSemiconvergent
NumStability.Algorithms.StationaryIterationSemiconvergentExistence
```

This is the requested classification review for the four classify/document
owners as well as the declaration-bearing facade.  It intentionally refreshes
the frozen queue proposal: every historical owner contains or reaches both
generic and exact Chapter 17 material.  Marking one `reusable` would create a
false reusable-to-Source/mixed reachability violation.

Change these five existing exact rows from `reusable` to `mixed`:

```text
NumStability.Analysis.SemiconvergentBlockFormExists
NumStability.Analysis.SemiconvergentExistenceComplete
NumStability.Analysis.SemiconvergentExistenceFull
NumStability.Analysis.SemiconvergentLimitGeneral
NumStability.Analysis.SemiconvergentRealSpectrumComplete
```

This is classification only; do not edit any of those accepted consumers.
Their import chain reaches `StationaryIterationSemiconvergentExistence`, whose
unchanged declarations have typed dependencies on Chapter 17 Equation 01 and
Equation 28 endpoints.  Leaving any of the five consumers `reusable` therefore
creates forbidden reusable-to-Source reachability.  The other exact
semiconvergence modules, `SemiconvergentExistenceGaps` and
`SemiconvergentSpectral`, do not import that chain and remain `reusable`.

### Rationale, protected tests, and gate

`CHECK_STATIC.py`, all nine canonical-reusable tests, the old-path tests, and
the rounded/semiconvergence/Drazin/accepted-consumer focused tests protect this
classification.  The delta resolves nine new unclassified canonical modules
and five historical unclassified debts while keeping the genuinely reusable
W07 graph at zero Source reachability.  The executable replay below runs both
layout and the repository's real strict-source generator; classification of
only the historical owners is insufficient.  The complete ten-module mixed
postimage unblocks both gates.

No `docs/architecture/COMPATIBILITY.md` edit is requested. Its C0007 blob is
`3b95fff399efd299540efcc53ae99cacced95613`; the compatibility checker requires
every tabled module to be import-and-docstring-only, while
`StationaryIteration` honestly retains 29 declarations.  Its old-path test,
not a false compatibility tier, protects the historical surface.

## IR-W07-4: ratchet only the exact reviewed layout debt

### Path and C0007 blob

`docs/architecture/layout-exceptions.json`:
`bbedd2a796aa7b003f89193e746599140fb03524`.

### Minimal delta and postimage

Apply exactly these sorted-set changes under `legacy`:

- remove all five historical names from `unclassified_modules`;
- add all five historical names and the five accepted semiconvergence consumer
  names from IR-W07-3 to `mixed_modules`;
- remove all five historical names from `missing_module_docstrings`;
- add these six accepted pre-existing modules to
  `declaration_bearing_umbrellas`:
  `NumStability.Source.Higham.Chapter17.Equation08`, `Equation12`,
  `Equation15`, `Equation16`, `Equation17`, and `Equation20` (with the full
  common prefix).

Do not change `noncanonical_modules`, `unsorted_aggregate_imports`, complete
aggregate contracts, or direct-import ceilings.  The exact postimage debt
counts are 304 unclassified, 19 mixed, 86 missing-doc, 266 noncanonical, 27
declaration-bearing umbrellas, and zero unsorted aggregates.

### Rationale, protected tests, and gate

The five documentation removals are genuine W07 improvements.  The six new
umbrella shapes arise only because new Results directories sit beneath
accepted declaration-bearing Equation 08/12/15/16/17/20 modules; W07 has no
authority to move those declarations.  Their exact C0007 blobs are:

| Module | Blob |
| --- | --- |
| `Equation08` | `8a6b464983a928162efc0c34fdff9941733585fc` |
| `Equation12` | `14f8f1dfe120da42614623f3b2cd14b613fb409c` |
| `Equation15` | `660a177e7eec6ee8fc36a7a4a2829a4d9b48f6fb` |
| `Equation16` | `c03b252cd0349d5f0b232051730c3c3b7134bfa5` |
| `Equation17` | `d4cd7c7f4f3441e960c1c7f65f18ef99e60a7732` |
| `Equation20` | `95250de7f42e646a03150380b313ee31939b2e5d` |

The six accepted-consumer checks and `Focused.Chapter17Boundary` protect the
postimage.  This ratchet, combined with IR-W07-1--3, unblocks
`check_layout.py` without hiding any new W07 debt.

## Protected accepted consumers: no edit requested

W07 directly compiles, but does not modify, these accepted C0007 consumers:

| Path | C0007 blob | Protecting test |
| --- | --- | --- |
| `NumStability/Source/Higham/Chapter17/Equation08.lean` | `8a6b464983a928162efc0c34fdff9941733585fc` | `Focused.AcceptedChapter17Consumers` |
| `NumStability/Source/Higham/Chapter17/Equation12.lean` | `14f8f1dfe120da42614623f3b2cd14b613fb409c` | `Focused.AcceptedChapter17Consumers` |
| `NumStability/Source/Higham/Chapter17/Equation15.lean` | `660a177e7eec6ee8fc36a7a4a2829a4d9b48f6fb` | `Focused.AcceptedChapter17Consumers` |
| `NumStability/Source/Higham/Chapter17/Equation16.lean` | `c03b252cd0349d5f0b232051730c3c3b7134bfa5` | `Focused.AcceptedChapter17Consumers` |
| `NumStability/Source/Higham/Chapter17/Equation17.lean` | `d4cd7c7f4f3441e960c1c7f65f18ef99e60a7732` | `Focused.AcceptedChapter17Consumers` |
| `NumStability/Source/Higham/Chapter17/Equation20.lean` | `95250de7f42e646a03150380b313ee31939b2e5d` | `Focused.AcceptedChapter17Consumers` |
| `NumStability/Analysis/SemiconvergentBlockFormExists.lean` | `02d24da8e5f17980651158048dcdbe3eebda3cef` | `Focused.AcceptedSemiconvergentConsumer` |
| `NumStability/Analysis/SemiconvergentExistenceComplete.lean` | `175df8df8c72b4588bb120e444c0aea499ab85b3` | full root build and strict-source replay |
| `NumStability/Analysis/SemiconvergentExistenceFull.lean` | `969c676d52f7b3fa2fe79da35df828ab3ff38321` | full root build and strict-source replay |
| `NumStability/Analysis/SemiconvergentLimitGeneral.lean` | `e84fd5893d97fc6bdb3e34b9e1374733fcdd600d` | full root build and strict-source replay |
| `NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean` | `86ac278b764a1205d4df25268e7a8eec4f05f8bd` | full root build and strict-source replay |
| `NumStabilityTest/Reorganization/W06/Focused/ProtectedW07.lean` | `9055c6cb9a48a0c227d2c0031d27c42a155d8b87` | `Focused.ProtectedW06` |

Their minimal delta is empty.  Their tests prove that neither declaration
preservation nor W06's typed incident edge requires a forbidden consumer
retarget.

## Executable integration proof

### Exact worker-only gate output

The unintegrated worker intentionally leaves every shared path untouched. Its
`check_layout.py` run exited 1 after 182.417 seconds with this W07-relevant
state:

```text
Lean modules: 2490
unclassified modules: 318
mixed modules: 9
modules missing module docs: 86
legacy naming exceptions: 266
declaration-bearing umbrellas: 27
unsorted aggregate imports: 0
error: NumStabilityTest does not reach 48 test module(s): NumStabilityTest.Reorganization.W07.Canonical.C001, NumStabilityTest.Reorganization.W07.Canonical.C002, NumStabilityTest.Reorganization.W07.Canonical.C003, NumStabilityTest.Reorganization.W07.Canonical.C004, NumStabilityTest.Reorganization.W07.Canonical.C005, NumStabilityTest.Reorganization.W07.Canonical.C006, NumStabilityTest.Reorganization.W07.Canonical.C007, NumStabilityTest.Reorganization.W07.Canonical.C008, NumStabilityTest.Reorganization.W07.Canonical.C009, NumStabilityTest.Reorganization.W07.Canonical.C010, NumStabilityTest.Reorganization.W07.Canonical.C011, NumStabilityTest.Reorganization.W07.Canonical.C012, NumStabilityTest.Reorganization.W07.Canonical.C013, NumStabilityTest.Reorganization.W07.Canonical.C014, NumStabilityTest.Reorganization.W07.Canonical.C015, NumStabilityTest.Reorganization.W07.Canonical.C016, NumStabilityTest.Reorganization.W07.Canonical.C017, NumStabilityTest.Reorganization.W07.Canonical.C018, NumStabilityTest.Reorganization.W07.Canonical.C019, NumStabilityTest.Reorganization.W07.Canonical.C020, NumStabilityTest.Reorganization.W07.Canonical.C021, NumStabilityTest.Reorganization.W07.Canonical.C022, NumStabilityTest.Reorganization.W07.Canonical.C023, NumStabilityTest.Reorganization.W07.Canonical.C024, NumStabilityTest.Reorganization.W07.Canonical.C025, NumStabilityTest.Reorganization.W07.Canonical.C026, NumStabilityTest.Reorganization.W07.Canonical.C027, NumStabilityTest.Reorganization.W07.Canonical.C028, NumStabilityTest.Reorganization.W07.Canonical.C029, NumStabilityTest.Reorganization.W07.Canonical.C030, NumStabilityTest.Reorganization.W07.Canonical.C031, NumStabilityTest.Reorganization.W07.Canonical.C032, NumStabilityTest.Reorganization.W07.Canonical.C033, NumStabilityTest.Reorganization.W07.Canonical.C034, NumStabilityTest.Reorganization.W07.Focused.AcceptedChapter17Consumers, NumStabilityTest.Reorganization.W07.Focused.AcceptedSemiconvergentConsumer, NumStabilityTest.Reorganization.W07.Focused.Chapter17Boundary, NumStabilityTest.Reorganization.W07.Focused.Drazin, NumStabilityTest.Reorganization.W07.Focused.PrivateRetention, NumStabilityTest.Reorganization.W07.Focused.ProtectedW06, NumStabilityTest.Reorganization.W07.Focused.ReusableIteration, NumStabilityTest.Reorganization.W07.Focused.RoundedExecution, NumStabilityTest.Reorganization.W07.Focused.SemiconvergenceProjector, NumStabilityTest.Reorganization.W07.OldPath.StationaryIteration, NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationDrazin, NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationRounded, NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationSemiconvergent, NumStabilityTest.Reorganization.W07.OldPath.StationaryIterationSemiconvergentExistence
error: new unclassified modules: NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces, NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition, NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep, NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
error: stale missing module docstrings baseline; review the improvement and run --write-baseline: NumStability.Algorithms.StationaryIteration, NumStability.Algorithms.StationaryIterationDrazin, NumStability.Algorithms.StationaryIterationRounded, NumStability.Algorithms.StationaryIterationSemiconvergent, NumStability.Algorithms.StationaryIterationSemiconvergentExistence
error: new declaration bearing umbrellas: NumStability.Source.Higham.Chapter17.Equation08, NumStability.Source.Higham.Chapter17.Equation12, NumStability.Source.Higham.Chapter17.Equation15, NumStability.Source.Higham.Chapter17.Equation16, NumStability.Source.Higham.Chapter17.Equation17, NumStability.Source.Higham.Chapter17.Equation20
error: NumStability.Algorithms.LinearSystems misses 9 canonical descendant(s): NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces, NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition, NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep, NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions, NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
```

The reported deltas are only the forbidden shared wiring described above: the
48-module W07 test root is unreachable, the LinearSystems aggregate lacks nine
direct imports, nine reusable leaves are unclassified, five newly documented
owners retain stale exceptions, and six accepted Chapter17 parent modules need
umbrella exceptions. The Chapter17 leaves are incidentally reachable through
the historical facade, but IR-W07-2 supplies the required honest direct
aggregate imports.

The exact worker strict-source generation exited 2 after 17.698 seconds:

```text
error: source graph check failed: 125 classified reusable-to-source/mixed reachable pair(s)
```

Those 125 pairs are exactly the five unchanged accepted Analysis consumers in
IR-W07-3 times the 25 new Source leaves. There are no direct forbidden pairs,
and `CHECK_STATIC.py` separately proves zero worker-owned reusable-to-Source
and canonical-to-historical reachability. This shared-only failure is not
waived; the executable postimage proof below resolves it.

`CHECK_INTEGRATOR_PATCH.py` verifies every shared preimage blob above, creates
a disposable clone at C0007, overlays only W07-owned output, applies exactly
IR-W07-1--4 in that clone, stages the simulated postimage for generated-file
inspection, and runs both the repository's real layout checker and strict-source
baseline generator. The worker's shared paths are never edited. The replay
passed in 190.979 seconds and produced this concise result excerpt:

```text
Lean modules: 2490
unclassified modules: 304
mixed modules: 19
modules missing module docs: 86
legacy naming exceptions: 266
declaration-bearing umbrellas: 27
unsorted aggregate imports: 0
Layout contract satisfied; no legacy debt increased.
W07 integrator strict-source replay: 2490 modules, 2186 classified, 304 unclassified, 19 mixed, 504 reusable roots, zero forbidden edges and reachable pairs.
W07 integrator patch replay passed in a disposable clone; worker shared paths unchanged.
```
