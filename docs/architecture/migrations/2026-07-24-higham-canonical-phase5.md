# Canonical Higham path migration, phase 5

## Scope and decision

This batch removes every direct historical `NumStability.Higham.*` import from
the canonical `NumStability.Source.Higham` entry point. Twelve transitional
owners containing 4,201 lines, 81 public declarations, and 22 private proof
helpers move to the final source hierarchy. The old paths remain supported as
documented import-only wrappers, and the twelve still older `Analysis.*` or
`Algorithms.*` wrappers are redirected to the final owners rather than chained
through another compatibility module.

Canonical names follow `docs/architecture/NAMING.md`: two-digit chapter names,
zero-padded local locators, no repeated chapter number in a leaf, semantic
cross-chapter families, and declaration-free documented umbrellas. Public
declaration names and namespaces do not change.

The mixed no-guard dot-product file is the one exception to a mechanical source
move. Its source-independent algorithm is extracted into the target arithmetic
hierarchy; only the four explicitly Higham-numbered endpoints remain under
`Source.Higham.CrossChapter`.

## Exact ownership map

| Historical owner | Canonical owner | Public declarations | Private declarations |
| --- | --- | ---: | ---: |
| `Higham.Chapter02.Problem04` | `Source.Higham.Chapter02.Problem04` | 3 | 0 |
| `Higham.Chapter02.Problem07` | `Source.Higham.Chapter02.Problem07` | 9 | 0 |
| `Higham.Chapter02.Problem22` | `Source.Higham.Chapter02.Problem22` | 2 | 0 |
| `Higham.Chapter08.Lemma8_8Discrepancy` | `Source.Higham.Chapter08.Lemma08Discrepancy` | 6 | 0 |
| `Higham.Chapter10.Theorem10_7` | `Source.Higham.Chapter10.Theorem07` | 11 | 22 |
| `Higham.Chapter11.Theorem11_7Capstone` | `Source.Higham.Chapter11.Theorem07` | 10 | 0 |
| `Higham.Chapter13.Table13_1` | `Source.Higham.Chapter13.Table01` | 6 | 0 |
| same | `Source.Higham.Chapter13.Equation25` | 1 | 0 |
| `Higham.Chapter20.SourceAliases` | `Source.Higham.Chapter20.Equation32` | 1 | 0 |
| same | `Source.Higham.Chapter20.Lemma06` | 1 | 0 |
| same | `Source.Higham.Chapter20.Theorem01` | 1 | 0 |
| `Higham.CrossChapter.Chapter02To03NoGuardDot` | `Algorithms.Arithmetic.DotProduct.NoGuard.Core` | 9 | 0 |
| same | `Algorithms.Arithmetic.DotProduct.NoGuard.Tree` | 4 | 0 |
| same | `Source.Higham.CrossChapter.NoGuardDotProduct` | 4 | 0 |
| `Higham.CrossChapter.Chapter07To15PracticalBound` | `Source.Higham.CrossChapter.PracticalConditionBound` | 3 | 0 |
| `Higham.CrossChapter.Chapter09To12Solver` | `Source.Higham.CrossChapter.LUSolverWeights.Doolittle` | 3 | 0 |
| `Higham.CrossChapter.Chapter09To12GenericSolver` | `Source.Higham.CrossChapter.LUSolverWeights.Factorization` | 7 | 0 |

The exact first and last public anchors for the cohesive moves are:

| Destination | First anchor | Last anchor |
| --- | --- | --- |
| `Chapter02.Problem04` | `problem2_4_theorem2_3_nearest_finite` | `problem2_4_theorem2_3_finiteRoundToEven` |
| `Chapter02.Problem07` | `problem2_7_statement1_add_comm` | `problem2_7_statement6_midpoint_strict_between_false` |
| `Chapter02.Problem22` | `problem2_22_guard_digit_a_sub_b_exact` | `problem2_22_kahanHeronArea_relError_le_gamma9_unitRoundoff` |
| `Chapter08.Lemma08Discrepancy` | `higham8_8_printedRowDominanceCounterU` | `higham8_8_printed_rowDominance_condSkeel_claim_false` |
| `Chapter10.Theorem07` | `signedBorder_source_endgame` | `higham10_7_actual_algorithm_source_closed` |
| `Chapter11.Theorem07` | `growthBcorner_nonneg` | `higham11_7_bunch_tridiagonal_support_aware` |
| `Chapter13.Table01` | `higham13_table13_1_col_bdd_product_family_from_source_norms` | `higham13_table13_1_implementation1_family_from_partitioned_computation_and_product_transfer` |

The Chapter 10 block moves atomically with its eight private definitions and
fourteen private lemmas/theorems. They are proof dependencies of the public
terminal and cannot be copied, exposed, or separated from the destination.

Chapter 13 is split at the explicit `Equation (13.25)` heading. The equation
terminal does not reference the preceding Table 13.1 terminal and therefore has
an independent owner with the same two narrow BlockLU source prerequisites.
Chapter 20's three source aliases are independent numbered results and receive
one leaf each.

## No-guard declaration partition

`Algorithms.Arithmetic.DotProduct.NoGuard.Core` owns:

```text
fl_noGuardDotProduct
noGuard_add_fold_unroll
noGuardDot_factor_expansion_succ
noGuardDotGammaProxy
noGuardDotGamma
noGuardDotGammaValid
noGuardDotLocalFactor
noGuardDot_factor_expansion_sum_succ
noGuardDotLocalFactor_abs_sub_one_le
```

`Algorithms.Arithmetic.DotProduct.NoGuard.Tree` owns:

```text
SumTree.noGuardEval
SumTree.noGuard_backward_error
fl_noGuardDotProductTree
noGuardDotTree_factor_backward_error
```

`Source.Higham.CrossChapter.NoGuardDotProduct` owns only:

```text
higham3_4_noGuard_any_order_backward_error
higham3_5_noGuard_any_order_forward_error
higham3_3_3_4_noGuard_backward_error
higham3_5_noGuard_forward_error
```

`Algorithms.Arithmetic.DotProduct.NoGuard` is the declaration-free reusable
family entry point. `Core` imports the historical generic dot-product model;
`Tree` imports `Core` and `Algorithms.Summation.Tree.Core`; the source leaf
imports both reusable leaves. No reusable module imports `Source`.

## Cross-chapter solver family

The old solver file owns the rounded Doolittle specialization and moves to
`LUSolverWeights.Doolittle`. The generic factorization file owns the natural,
row-permuted, and completely permuted solver-weight results and moves to
`LUSolverWeights.Factorization`.

The old generic module imports the old solver only for hidden transitive
prerequisites and references none of its declarations. Both new leaves import
`Algorithms.HighamChapter9DoolittleClosure` and
`Algorithms.HighamChapter12` directly. The declaration-free
`Source.Higham.CrossChapter.LUSolverWeights` umbrella imports both leaves.

`Source.Higham.CrossChapter.PracticalConditionBound` retains its direct
`Analysis.HighamChapter7` and `Algorithms.CondEstimation` prerequisites.
`Source.Higham.CrossChapter` is a declaration-free complete aggregate over the
no-guard, practical-bound, and solver-weight source families.

## Chapter and root entry points

Add declaration-free complete chapter umbrellas for Chapters 02, 08, 10, 11,
13, and 20. The final `Source.Higham` import list is:

```text
NumStability.Source.Higham.Chapter02
NumStability.Source.Higham.Chapter04
NumStability.Source.Higham.Chapter08
NumStability.Source.Higham.Chapter10
NumStability.Source.Higham.Chapter11
NumStability.Source.Higham.Chapter13
NumStability.Source.Higham.Chapter14
NumStability.Source.Higham.Chapter20
NumStability.Source.Higham.Chapter24
NumStability.Source.Higham.Chapter25
NumStability.Source.Higham.CrossChapter
```

It contains no direct `NumStability.Higham.*` import. The historical
`NumStability.Higham` root continues to forward to `Source.Higham`.

## Compatibility and consumers

Convert all twelve transitional owners named in the first column of the
ownership table into documented import-only wrappers. Multi-target wrappers
import the exact final leaves, not an expandable chapter umbrella:

- `Higham.Chapter13.Table13_1` imports `Chapter13.Equation25` and
  `Chapter13.Table01`;
- `Higham.Chapter20.SourceAliases` imports `Chapter20.Equation32`, `Lemma06`,
  and `Theorem01`;
- `Higham.CrossChapter.Chapter02To03NoGuardDot` imports the reusable
  `Algorithms.Arithmetic.DotProduct.NoGuard` surface and the source leaf.

Redirect these twelve older wrappers to the same final targets:

```text
Analysis.Problem2_4
Analysis.Problem2_7
Analysis.Problem2_22
Algorithms.HighamChapter8Lemma88SourceDiscrepancy
Algorithms.Cholesky.Higham10Theorem10_7Source
Algorithms.Cholesky.BunchTridiagonalCapstoneCh11Closure
Algorithms.LU.BlockLUTable13_1Families
Algorithms.LeastSquares.Higham20SourceAliases
Algorithms.HighamChapter3NoGuardDotBridge
Algorithms.HighamChapter15Ch7PracticalBoundBridge
Algorithms.HighamChapter12Ch9GenericSolverBridge
Algorithms.HighamChapter12Ch9SolverBridge
```

`Analysis.Problem2_7` retains its independent
`FloatingPoint.OperationLaws` target. The declaration-bearing
`Algorithms.Cholesky.Higham1014SourceSuccess` consumer imports
`Source.Higham.Chapter10.Theorem07` directly. No production module may import
a path newly classified as compatibility.

## Tests and manifests

Add canonical-only smoke modules for all 17 declaration-bearing leaves and
aggregate-only smokes for the six chapter umbrellas, the reusable no-guard
umbrella, `LUSolverWeights`, and `CrossChapter`. Add isolated old-only tests for
each of the twelve new `NumStability.Higham.*` wrappers and for each of the
twelve older wrappers; a multi-target wrapper test checks a representative
declaration from every target. Register every smoke in `NumStabilityTest.lean`.

Update `EndpointCanonical` and `SourceCanonical` to import only final canonical
paths. Update the `Source.Higham`, historical `Higham`, `Source`, `Algorithms`,
and root smokes so the broad supported surfaces remain explicit.

Manifest changes are exact:

- classify the twelve old Higham paths as `compatibility`;
- classify `NoGuard.Core` and `NoGuard.Tree` as `reusable`;
- classify the nine new umbrellas as `aggregate`;
- let all declaration-bearing Higham leaves inherit the `source` prefix;
- add all twelve old-to-final rows and retarget all twelve older rows in
  `COMPATIBILITY.md`;
- remove the twelve migrated old owners from the naming-exception inventory;
- add complete-aggregate contracts for all nine new umbrellas; and
- add no naming, documentation, mixed-module, or source-boundary exception.

The expected production inventory is 857 modules and 207 classified modules,
with 650 unclassified, zero mixed, 442 naming exceptions, 227 missing module
docs, and the single already-reviewed FastMatMul declaration-bearing umbrella.

## Dependency-safe execution and gates

1. Extract and build the reusable no-guard Core and Tree leaves.
2. Move Chapters 02, 08, 10, and 11; redirect the Chapter 10 consumer.
3. Split Chapters 13 and 20 at their semantic locator boundaries.
4. Move the three cross-chapter source families with direct prerequisites.
5. Add all chapter/family/root umbrellas and redirect production consumers.
6. Convert old owners to wrappers, update manifests, and add isolated smokes.
7. Verify normalized declaration bodies and unique ownership for all 81 public
   declarations and 22 private helpers.
8. Build each leaf in isolation, then its umbrella, canonical root, historical
   root, older wrappers, and registered test driver.
9. Run layout, compatibility, provenance, aggregate-order, strict-source,
   notice, JSON, `git diff --check`, full build/test, and reproducible baseline
   gates before commit.

Public declaration renames and removal of compatibility wrappers remain outside
this batch and require a separate deprecation policy.
