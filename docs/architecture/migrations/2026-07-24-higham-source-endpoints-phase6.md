# Higham source endpoints, phase 6

## Scope and decision

This batch moves the remaining small, dependency-closed Higham source owners
for Chapters 4, 17, and 26 into `NumStability.Source.Higham`. The six current
owners contain 246 public declarations and five private proof helpers. Public
declaration names, namespaces, statements, and bodies remain unchanged. Each
old path becomes a documented direct import-only compatibility wrapper.

The canonical paths follow `docs/architecture/NAMING.md`: two-digit chapter
directories, zero-padded numbered locators, semantic subfamilies only where a
source section contains several cohesive surfaces, and declaration-free
documented umbrellas. Reusable production modules must not import the old
compatibility paths or rely on aggregate transitivity.

This is deliberately not a mass migration of every file whose name mentions a
Higham chapter. It closes three source endpoints whose declarations have no
hidden production consumers beyond the repository aggregates. Larger Chapter
1, 2, 9, 11, 12, 13, 20, and 23 families remain separate reviewed batches.

## Chapter 4 ownership map

`Algorithms.Problem44SixTerm` moves atomically to
`Source.Higham.Chapter04.Problem04`. It owns exactly 23 public declarations and
no private declarations:

```text
Problem44Term
Problem44Term.realValue
Problem44Term.smallValue
Problem44Accumulator
problem44Step
problem44AccumulatorOutput
problem44AccumulatorOutput_step_le
problem44Source
problem44Eval
problem44Output
problem44Fold_output_le
problem44Output_le_smallValue_sum
problem44_nat_list_sum_eq_of_perm
problem44Source_exact_sum
problem44Source_smallValue_sum
problem44PossibleOutputs
problem44Output_mem_Icc_of_perm
problem44WitnessOrder
problem44WitnessOrder_perm
problem44WitnessOrder_output
problem44Every_Icc_output_attained
problem44PossibleOutputs_eq_Icc
problem44_outputs_exactly_Icc
```

`Algorithms.HighamChapter4KaoWangScope` moves atomically to
`Source.Higham.Chapter04.Section02.KaoWangCitationDiscrepancy`. It owns exactly
38 public declarations and no private declarations, all below namespace
`NumStability.HighamChapter4KaoWang`:

```text
IntegerAdditionTree
IntegerAdditionTree.value
IntegerAdditionTree.leaves
IntegerAdditionTree.cost
IntegerAdditionTree.toSchedule
IntegerAdditionTree.value_leaf
IntegerAdditionTree.value_node
IntegerAdditionTree.leaves_leaf
IntegerAdditionTree.leaves_node
IntegerAdditionTree.cost_leaf
IntegerAdditionTree.cost_node
IntegerAdditionTree.toSchedule_leaves
IntegerAdditionTree.toSchedule_exactEval
IntegerAdditionTree.toSchedule_exactMergeCost
Realizes
AdditionTreeDecision
IsMinimumAdditionTree
IsRecursiveOrderTree
RecursiveOrderDecision
recursiveOrderDecision_implies_additionTreeDecision
balancedFour_not_recursive
higham43_runningBudget_exactArithmetic_eq_kaoWangCost
halfBiasedAddModel
twoOnes
twoOnes_cost
twoOnes_higham43_runningBudget_halfBiased
higham43_computedBudget_ne_kaoWangExactCost_witness
IsThreePartition
IsThreePartitionInstance
reductionW
reductionA
reductionL
reductionh
reductionH
reductionX
reductionThreshold
reductionX_length
ReductionCorrect
```

The second destination is a Section 4.2 source leaf, not Section 4.1 or
Equation 4.3. Higham's citation follows Equation (4.3) in Section 4.2, but the
formalized discrepancy concerns the cited exact addition-tree objective versus
the computed-intermediate-sum objective; it does not dispute Equation (4.3).
Add a declaration-free `Chapter04.Section02` aggregate and extend the existing
Chapter 4 aggregate with `Problem04` and `Section02`.

Both old algorithm paths become single-target wrappers. `Algorithms` removes
their direct imports and continues to expose the declarations through its
already-supported Chapter 4 source aggregate.

## Chapter 17 ownership map

The two historical owners contain exactly 44 public declarations and no
private declarations. Split them by printed locator as follows:

| Canonical owner | Public | Exact owned declarations |
| --- | ---: | --- |
| `Source.Higham.Chapter17.Equation08` | 2 | `summable_infNorm_matPow`; `tsum_infNorm_matPow_le` |
| `Source.Higham.Chapter17.Problem01` | 4 | `norm_complexified_pow`; `eventually_matPow_le_of_spectralRadius_le`; `summable_infNorm_matPow_of_spectralRadius`; `higham17_problem17_1` |
| `Source.Higham.Chapter17.Equation12` | 13 | `matPow_entry_mul_sum_le_geometric`; `summable_matPow_entry_mul`; `stationarySeriesEntry`; `stationarySeriesEntry_nonneg`; `stationarySeriesEntry_le`; `partialSumBound_of_stationarySeriesEntry_le`; `CAValues`; `cALiteral`; `isClosed_CAValues`; `cALiteral_mem`; `cALiteral_nonneg`; `CAValues_nonempty_of_entry_lower_bound`; `partialSumBound_cALiteral` |
| `Source.Higham.Chapter17.Equation15` | 1 | `literal_norm_form_forward_bound` |
| `Source.Higham.Chapter17.Equation16` | 1 | `literal_norm_form_jacobi_forward_bound` |
| `Source.Higham.Chapter17.Equation17` | 2 | `literal_norm_form_sor_forward_bound`; `literal_norm_form_gaussSeidel_forward_bound` |
| `Source.Higham.Chapter17.Equation20` | 15 | `residualSigmaEntry`; `residualSigmaEntry_nonneg`; `residual_entry_abs_le_geometric`; `summable_residualSigmaEntry`; `residualSigmaMatrix`; `finiteResidualSigmaMatrix_nonneg`; `finiteResidualSigmaMatrix_le_residualSigmaMatrix`; `finiteResidualSigma_le_infNorm_residualSigmaMatrix`; `bddAbove_residualSigmaValues`; `residualSigmaSup_le_infNorm_residualSigmaMatrix`; `infNorm_residualSigmaMatrix_le_residualSigmaSup`; `infNorm_residualSigmaMatrix_eq_residualSigmaSup`; `residualSigmaTsum_eq_infNorm_residualSigmaMatrix`; `residualSigmaTsum_eq_residualSigmaSup`; `residualSigmaTsum_le_diagonalizable_max_bound_of_infNorm_bound` |
| `Source.Higham.Chapter17.Equation22` | 6 | `blockJ_compBlock_eq`; `matPow_compBlock_tendsto_zero_of_blockJ_tendsto_topProjector`; `spectralRadius_complexifyMat_lt_one_of_matPow_tendsto_zero`; `Higham17_22SourceBlockForm`; `higham17_22_sourceBlockForm_of_forall_orbit_tendsto`; `higham17_22_exists_blockForm_spectralRadius_lt_one_of_forall_orbit_tendsto` |

Keep Equations 15, 16, and 17 separate. Equation 13 remains owned elsewhere,
Equation 14 is deliberately absent, and the existing endpoints correspond to
three distinct printed results. Do not create empty locator modules or a vague
`Equations13To17` family.

`Algorithms.StationaryIterationSeries` becomes a direct multi-target wrapper
over Equation 8, Equation 12, Equations 15--17, Equation 20, and Problem 1. It
must not import the Chapter 17 umbrella because that would newly expose
Equation 22. `Analysis.Ch17SemiconvergentBlockFormSourceClosure` becomes a
single-target wrapper over Equation 22.

Add a declaration-free Chapter 17 aggregate. Retarget `Algorithms` to that
aggregate, `Analysis` to Equation 22, and the library-lookup example to the
Chapter 17 aggregate.

## Chapter 26 ownership map

The two historical owners contain exactly 141 public declarations and five
private helpers: 107 public plus two private in `Higham26`, and 34 public plus
three private in `Higham26SourceSearch`.

| Canonical owner | Public | Private | Cohesive surface |
| --- | ---: | ---: | --- |
| `Source.Higham.Chapter26.Equation01` | 2 | 0 | `IsGlobalMax`, `DirectSearchSpec` |
| `Source.Higham.Chapter26.Equation02` | 1 | 0 | alternating-directions stopping predicate |
| `Source.Higham.Chapter26.AlternatingDirections.ExactExecution` | 8 | 0 | exact line search, coordinate step, sweep, trace, and run |
| `Source.Higham.Chapter26.AlternatingDirections.CrudeLineSearch` | 15 | 1 | initial, directed, doubling, crude, and monotonicity surfaces |
| `Source.Higham.Chapter26.Equation03` | 3 | 0 | one-norm relative-size stopping criterion |
| `Source.Higham.Chapter26.MultidirectionalSearch.Simplex` | 20 | 0 | simplex representation and transformation API |
| `Source.Higham.Chapter26.MultidirectionalSearch.Execution` | 4 | 1 | iteration, specification, convergence, and trace |
| `Source.Higham.Chapter26.MultidirectionalSearch.InitialSimplexGeometry` | 4 | 0 | scale, squared distance, and edge dot product |
| `Source.Higham.Chapter26.MultidirectionalSearch.RightAngledSimplex` | 5 | 0 | right-angled constructor and geometry |
| `Source.Higham.Chapter26.MultidirectionalSearch.RegularSimplex` | 10 | 2 | regular-simplex coefficients, constructor, and geometry |
| `Source.Higham.Chapter26.Equation04` | 1 | 0 | inverse residual stability measure |
| `Source.Higham.Chapter26.CubicRoots.DepressedCubic` | 3 | 0 | depressed-cubic coefficients and identity |
| `Source.Higham.Chapter26.CubicRoots.MonicCubic` | 2 | 0 | monic cubic and root transfer |
| `Source.Higham.Chapter26.Equation05.RealBranches` | 5 | 0 | real radicand and plus/minus branches |
| `Source.Higham.Chapter26.Equation05.ComplexBranches` | 7 | 0 | algebraic square root and complex branches |
| `Source.Higham.Chapter26.Equation05.CardanoRoots` | 8 | 0 | cube root, Vieta substitution, and four root endpoints |
| `Source.Higham.Chapter26.Equation05.ZeroBranchDiscrepancy` | 1 | 0 | printed zero-branch discrepancy |
| `Source.Higham.Chapter26.Equation06` | 7 | 0 | stable real and complex branch selection |
| `Source.Higham.Chapter26.Equation07` | 1 | 0 | cubic-root residual measure |
| `Source.Higham.Chapter26.Equation08` | 4 | 0 | linearized forward error and affine exactness |
| `Source.Higham.Chapter26.IntervalArithmetic.ExactOperations` | 15 | 1 | exact interval operations and containment |
| `Source.Higham.Chapter26.IntervalArithmetic.DependencyExamples` | 2 | 0 | subtraction and division dependency examples |
| `Source.Higham.Chapter26.IntervalArithmetic.DirectedRounding` | 13 | 0 | finite-range bounds and outward-rounded operations |

The private crude-fold helper remains atomic with `CrudeLineSearch`; the
private ordered-iteration helper remains atomic with `Execution`; the two
private regular-simplex sums remain atomic with `RegularSimplex`; and the
private fixed-multiplication bound remains atomic with `ExactOperations`.

Add declaration-free complete aggregates for `AlternatingDirections`,
`CubicRoots`, `Equation05`, `IntervalArithmetic`,
`MultidirectionalSearch`, and `Chapter26`.

## Chapter 26 import DAG and wrappers

Canonical leaves use direct prerequisites rather than old paths or umbrella
transitivity. In particular, exact alternating-directions execution imports
`Equation02`; crude search imports exact execution; multidirectional execution
imports `Simplex` and `Equation03`; the two concrete simplex leaves import
`Simplex` and `InitialSimplexGeometry`; Cardano roots import complex branches
and the monic-cubic leaf; Equation 6 imports both Equation 5 branch leaves;
directed rounding imports exact interval operations and floating-point
arithmetic.

The two wrappers are intentionally asymmetric. Historical `Higham26` imports
only the leaves owning its original 107 public and two private declarations,
so it does not expose declarations that were never on that surface.
`Higham26SourceSearch` imports the complete canonical Chapter 26 aggregate,
preserving its historical transitive exposure of `Higham26` together with its
own 34 public and three private declarations.

`Algorithms` replaces its two historical Chapter 26 imports with the canonical
Chapter 26 aggregate. Although source material does not belong in a reusable
algorithm leaf, `Algorithms` is explicitly the historical compatibility and
discovery aggregate; retaining this single canonical import preserves its
supported declaration surface while eliminating production use of old paths.

## Exact manifest and test delta

This batch adds 41 canonical production modules: 33 declaration-bearing source
leaves and eight declaration-free aggregates. The six old owners remain in the
module inventory and change from unclassified historical owners to classified
compatibility wrappers. The exact structural inventory is therefore:

```text
Production modules:               898
Classified modules:               254
Unclassified modules:             644
Mixed modules:                      0
Missing module docs:              225
Historical naming exceptions:     437
Declaration-bearing umbrellas:      1  (the reviewed FastMatMul aggregate)
```

`Algorithms` has 459 direct project imports after replacing six historical
imports with two canonical chapter imports and using its existing Chapter 4
import. Its direct Analysis imports fall to 44 and direct Source imports rise
to five. No reusable leaf gains a source dependency.

Add exactly 47 registered isolation tests: 33 canonical leaf smokes, eight
aggregate-only smokes, and six old-only wrapper smokes. Chapter 4 contributes
five tests, Chapter 17 contributes eleven, and Chapter 26 contributes 31.

## Compatibility, tests, and gates

Every historical owner in this batch remains a direct wrapper to final leaves.
No wrapper may forward through another compatibility module. Canonical-only
tests import each declaration-bearing leaf independently; aggregate-only tests
compile every new umbrella; old-only tests compile every wrapper without a
canonical sibling import. Multi-target wrapper tests check a representative
declaration from every target family.

Before commit, compare normalized declaration bodies with commit `1a35c7359`
and prove unique ownership for all 246 public declarations and five private
helpers. Then build leaves in dependency order, build chapter and root
aggregates, build every wrapper and registered smoke, and run the layout,
compatibility, provenance, aggregate-order, strict-source, notice, JSON,
`git diff --check`, full test, full build, and reproducible-baseline gates.

Public declaration renames and compatibility-wrapper removal are outside this
batch and require a separate deprecation policy.
