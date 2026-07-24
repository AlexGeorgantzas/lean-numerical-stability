# Phase 10B: Small Higham frontiers

Date: 2026-07-24

Execution base: `21e130ac8355de8ec1a74f22a73bf103e00bc48f`

This record is the authoritative pre-edit ownership map for the second Stage 1
slice after Phase 9. All Git blobs, line counts, import edges, declaration
counts, and manifest ceilings refer to the immutable execution base above.
The migration changes module ownership and imports only: declaration names,
namespaces, types, bodies, visibility, and source order remain unchanged.

## Scope and role decisions

This batch closes four independent, low-risk organization frontiers:

1. Higham Chapter 2, Problem 2.2 moves from the reusable-analysis tree into
   its source chapter;
2. the scalar boundary for Chapter 14, Problem 14.13 moves from the flat
   algorithms tree into its existing source chapter;
3. Chapter 21 row-scaling invariance moves from the underdetermined-algorithms
   tree into a new source chapter; and
4. the source-neutral Gaussian absolute-moment API used by Chapter 28 moves
   out of `Algorithms.TestMatrices` into reusable probability analysis.

The first three leaves are classified as `source`: their declarations and
module documentation explicitly implement numbered Higham problems or prose.
The Gaussian leaf is classified as `reusable`: none of its declaration names
or statements depends on Higham or Ginibre terminology, and it is a general
probability API with one current source-specific consumer.

The four leaves total 432 physical lines and 22 explicit public declaration
blocks. They are intentionally batched because their dependency and consumer
graphs do not overlap. Each ownership population remains an independent
preservation target. Large dependencies such as `MatrixInversion`,
`UnderdeterminedSolve`, and the broader Chapter 21 and Chapter 28 families are
outside this slice.

The slice is complete only when:

1. every declaration has exactly one canonical owner at the path recorded
   below;
2. all four historical paths are exact one-import compatibility wrappers;
3. no production module imports a historical path;
4. the three new probability/Chapter 21 umbrellas are documented, sorted,
   declaration-free complete aggregates;
5. canonical-only, aggregate-only, and old-only import tests pass;
6. source and compiled ownership audits preserve all four populations after
   normalizing only changed owner paths and generated private prefixes; and
7. the full repository architecture, test, build, baseline, and clean-checkout
   gates pass.

## Immutable source inventory

| Historical owner | Git blob | Lines | Explicit declarations | Compiled ownership |
| --- | --- | ---: | ---: | ---: |
| `Analysis.Problem2_2` | `9db1f4c211a6feb7429efa8da640330e403845d9` | 59 | 3 public theorems | 3 public theorems |
| `Algorithms.Ch14Problem1413Boundary` | `2773688fdeb7a747d42191ed061b4aeb84c76ff3` | 118 | 5 public theorems | 5 public theorems |
| `Algorithms.Underdetermined.Higham21Condition` | `476ca0e6cd69f107b53b658de0ec627481acce3b` | 101 | 2 public definitions + 4 public theorems | 6 public + 21 internal constants |
| `Algorithms.TestMatrices.Higham28GaussianAbsoluteMoment` | `28f6256be8c5a3cb2012cabb734fa0bcca16ae3b` | 154 | 8 public theorems | 8 public theorems |

There are no explicit private declarations in this slice. The compiled total
is 43 constants: 22 public and 21 generated internal constants. The Chapter 21
internal constants are generated equation/simplification artifacts of its two
definitions and four theorems; they remain part of that leaf's preservation
target.

### Chapter 2 ownership population

- `NumStability.FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds_left`
- `NumStability.FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds_right`
- `NumStability.FloatingPointFormat.problem2_2_lemma2_1_spacing_bounds`

Its compiled graph contains 12 signature edges and 15 body edges, with ten
overlapping targets and 17 union edges. Two body edges are internal to the
population; the 15 cross-module union targets all belong to
`Analysis.FloatingPointArithmetic`. It has no external declaration consumer.

### Chapter 14 ownership population

- `NumStability.ch14ext_problem14_13_kappa2_eq_one_fin_one`
- `NumStability.ch14ext_problem14_13_frobNorm_eq_abs_det_fin_one`
- `NumStability.ch14ext_problem14_13_gej_bound_fin_one`
- `NumStability.ch14ext_problem14_13_gej_bound_of_isRightInverse_pos`
- `NumStability.ch14ext_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows_pos`

Its compiled incident graph contains 13 signature and 32 body edges, including
four internal body edges and no incoming external declaration consumer.
External targets belong to `Algorithms.MatrixInversion`,
`Analysis.MatrixAlgebra`, and `Analysis.Norms`.

### Chapter 21 ownership population

- `NumStability.higham21RowScale`
- `NumStability.higham21RowScaledAplus`
- `NumStability.higham21_rowScaled_domain_projection`
- `NumStability.higham21_rowScaled_right_inverse`
- `NumStability.higham21_rowScaled_moorePenrose`
- `NumStability.higham21Cond2With_row_scaling`

Its compiled graph contains 16 signature and 23 body edges, with 18
intra-owner edges and no incoming external declaration consumer. External
targets belong to `UnderdeterminedSolve`, `UnderdeterminedSpec`,
`Analysis.MatrixAlgebra`, and `Analysis.Norms`.

### Gaussian ownership population

- `NumStability.integral_abs_mul_exp_neg_mul_sq`
- `NumStability.integral_abs_mul_standardGaussianPDF`
- `NumStability.two_div_sqrt_two_mul_pi`
- `NumStability.integral_abs_mul_standardGaussianPDF_eq_sqrt`
- `NumStability.integral_abs_mul_gaussianPDFReal_zero_two`
- `NumStability.integral_abs_mul_gaussianPDFReal_zero_two_eq`
- `NumStability.gaussianReal_prod_map_sub`
- `NumStability.integral_abs_standardGaussian_difference`

This population has no signature edge to another project declaration. Its
project body graph has seven intra-owner edges. The sole external declaration
consumer is `realGinibreAbsoluteCharacteristicMoment_one` in
`Higham28GinibreDeterminantMoment`.

## Exact old-to-new ownership map

| Historical owner | Canonical owner | Role |
| --- | --- | --- |
| `Analysis.Problem2_2` | `Source.Higham.Chapter02.Problem02` | source |
| `Algorithms.Ch14Problem1413Boundary` | `Source.Higham.Chapter14.Problem13` | source |
| `Algorithms.Underdetermined.Higham21Condition` | `Source.Higham.Chapter21.RowScalingInvariance` | source |
| `Algorithms.TestMatrices.Higham28GaussianAbsoluteMoment` | `Analysis.Probability.Gaussian.AbsoluteMoment` | reusable |

The new declaration-free aggregates are:

- `Source.Higham.Chapter21`, importing `RowScalingInvariance`;
- `Analysis.Probability`, importing `Probability.Gaussian`; and
- `Analysis.Probability.Gaussian`, importing `Gaussian.AbsoluteMoment`.

The existing `Source.Higham.Chapter02` and `Source.Higham.Chapter14`
aggregates gain their respective leaves. `Source.Higham` gains Chapter 21, and
`Analysis` gains Probability. Each historical leaf remains at its current path
and imports exactly its canonical owner.

## Dependency and consumer map

The immutable direct imports are:

- Problem 2.2 imports `Analysis.FloatingPointArithmetic`;
- Problem 14.13 imports `Algorithms.MatrixInversion`;
- row-scaling invariance imports
  `Algorithms.Underdetermined.UnderdeterminedSolve`; and
- Gaussian absolute moments import four Mathlib probability/integration
  modules and no project module.

Canonical leaves retain those mathematical dependencies unchanged.

The immutable direct production importers and their exact retargeting are:

- `Analysis` drops historical `Analysis.Problem2_2`; the source-specific leaf
  moves behind `Source.Higham.Chapter02`, matching the aggregate's canonical-
  descendant contract;
- `Algorithms` replaces historical Problem 14.13 and its direct Chapter 14
  Section 5 import with the complete `Source.Higham.Chapter14` aggregate;
- `Algorithms.Underdetermined.Higham21` replaces the historical condition leaf
  with the complete `Source.Higham.Chapter21` aggregate;
- `Algorithms.Underdetermined.Higham21Eq21_8` replaces the historical condition
  leaf with canonical `Source.Higham.Chapter21.RowScalingInvariance`, preserving
  its prior direct-import surface even though its own declarations do not
  consume the row-scaling API;
- `Algorithms.TestMatrices.Higham28GinibreDeterminantMoment` imports canonical
  `Analysis.Probability.Gaussian.AbsoluteMoment`; and
- `Algorithms` replaces the historical Gaussian leaf with the same canonical
  reusable leaf.

Problem 2.2 and Problem 14.13 have no declaration consumer. The Chapter 21
leaf likewise has no external declaration consumer; its broad historical
aggregate and `Higham21Eq21_8` import are both retargeted. The Gaussian leaf's
one compiled consumer is preserved by the direct canonical import above.

## Preservation audit

Each canonical implementation's declaration region must compare byte-for-byte
with the corresponding base blob after UTF-8/BOM and line-ending
normalization. Header comments, module documentation, imports, and
path-specific prose may change; declarations and namespace scaffolding may
not.

The compiled comparison normalizes only the four recorded owner module paths
and any matching generated private prefix. It then compares unique ownership,
normalized names, kinds, visibility, type structure, and body/proof structure
separately for each population. The expected result is the same 3, 5, 27, and
8 constants respectively, with no added, removed, duplicated, or mismatched
constant. The global declaration graph is expected to remain exactly 81,950
constants and 491,557 union dependency edges.

## Entry points, tests, and manifests

The implementation adds eleven isolated tests:

- four canonical-leaf tests;
- three new-aggregate tests (`Source.Higham.Chapter21`,
  `Analysis.Probability`, and `Analysis.Probability.Gaussian`); and
- four old-only compatibility tests, each importing exactly one wrapper.

Existing Chapter 2, Chapter 14, `Source.Higham`, `Analysis`, `Algorithms`,
`All`, root, `EndpointCanonical`, `EndpointMigration`, `SourceCanonical`, and
`SourceMigration` smokes are updated wherever the changed public surface is
in scope. Representative checks cover the Chapter 2 spacing package, the
Problem 14.13 scalar boundary, Chapter 21 row scaling and Moore--Penrose
transport, and the exact Gaussian-difference absolute moment.

The tier manifest records the four historical leaves as `compatibility`, the
three source leaves as `source`, the Gaussian leaf as `reusable`, and the three
new umbrellas as `aggregate`. The compatibility table records all four exact
maps. The layout manifest removes all four historical paths from unclassified
and noncanonical debt and adds the three complete-aggregate contracts. The
tier manifest records `Analysis.Probability` as a reusable public entry point.

Before incidental line-count changes, the expected structural ratchet is:

| Measure | Phase 10A | Expected Phase 10B |
| --- | ---: | ---: |
| Production modules | 957 | 964 |
| Classified modules | 334 | 345 |
| Unclassified modules | 623 | 619 |
| Aggregate modules | 63 | 66 |
| Compatibility modules | 89 | 93 |
| Internal modules | 2 | 2 |
| Reusable modules | 49 | 50 |
| Source modules | 126 | 129 |
| Upstream modules | 5 | 5 |
| Missing module docs | 222 | 220 |
| Legacy naming exceptions | 416 | 412 |
| Mixed modules | 0 | 0 |
| Declaration-bearing umbrellas | 0 | 0 |
| Unsorted aggregates | 0 | 0 |

The compatibility inventory grows from 89 to 93 wrappers and from 187 to 191
direct canonical targets. `Algorithms` moves from 445 to 444 direct project
imports; its direct `Analysis` imports move from 44 to 45 and its direct
`Source` imports remain ten. The expected global direct-import count is 4,018:
2,651 internal and 1,367 external edges.

## Documentation deltas

The implementation updates:

- the compatibility, tier, layout, endpoint, and generated-baseline records;
- both exact Problem 2.2 paths in `docs/source_coverage/higham_ch02.md`;
- the Problem 14.13 paths in the Chapter 14 source inventory, proof-source
  ledger, and formalization report;
- the row-scaling paths in the Chapter 21 source inventory, formalization
  report, and source-coverage ledger; and
- the public reusable-entry-point descriptions in `README.md` and root
  `ARCHITECTURE.md` for the new probability API.

## Post-map documentation ratchet

The immutable source inventory and ownership map above remain unchanged. The
touched historical `Higham21` aggregate also receives a missing module doc,
improving the expected missing-module-doc count from 221 to 220. Its
`Higham21Eq21_8` descendant retains the old condition module's import surface
through the canonical row-scaling leaf; this intentionally preserves import
compatibility even though no Eq. 21.8 declaration consumes that leaf.

Archived baselines remain immutable, and no Chapter 28 ledger currently names
the historical Gaussian path.

## Validation commands

Validation requires:

- isolated builds of all four canonical leaves and all three new aggregates;
- isolated builds of all four old-only wrapper tests;
- the registered `NumStabilityTest` target and `lake test`;
- `lake build NumStability NumStabilityTest`;
- `lake env lean examples/LibraryLookup.lean`;
- layout, compatibility, provenance, placeholder, classified-source-boundary,
  aggregate-ordering, Apache-normalization, Python-syntax, and JSON checks;
- exact source and compiled ownership comparisons for all four populations;
- global and family declaration-graph reproduction;
- baseline regeneration and clean reproduction;
- `git diff --check`; and
- a final clean-commit rerun before pushing to `main`.
