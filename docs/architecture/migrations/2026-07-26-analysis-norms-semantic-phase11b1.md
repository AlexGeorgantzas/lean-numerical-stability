# Analysis norms semantic split — Phase 11B1

This is the immutable pre-edit ownership record for organization Phase 11B1.
It partitions every compiled constant currently owned by
`NumStability.Analysis.Norms.Core` before any production Lean file is moved.

## Authority and bounded scope

Phase 11B1 starts from pushed Phase 11A evidence revision
`66e2451d005e380c69015e525dc9b3e33ce95194`. The clean Phase 11A
implementation revision is `63719a150fceecaa132f7c2ba5b57ba07e28bec7`,
whose normalized source-tree digest is
`de93ad72a7b6d7b31d3deccade5e1b587fc34c6a43b62b0eda7ad32df72d9b9e`.
The retained Phase 11A declaration/dependency stream has SHA-256
`7FFBDD7F54F4DD19C0FCD5962D41A01A09ED55F6E251DB7F4240B42D340E6A09`.

The transitional Core file has Git blob
`51bcd3539d7d7a9396d4284fc437fb009391ee76`, normalized-file SHA-256
`534C3D858667B5DD7D1461DC35148FCC4C92219E6B10DBA271799C12E962ACA2`,
23,631 physical lines, 22,413 nonblank lines, and 1,783 compiled constants.

This subphase does exactly three things:

1. split those 1,783 constants into graph-checked semantic reusable and
   Chapter 6 source leaves;
2. turn `Analysis.Norms.Core` into a reusable declaration-free aggregate while
   retaining `Analysis.Norms` as the historical compatibility facade; and
3. remove the audited stale Core import from
   `Source.Higham.Chapter23.BilinearAlgorithm`.

Phase 11B1 does **not** relocate `Algorithms.Chapter06Lemma66`,
`Analysis.Higham6Asides`, `Analysis.Higham6BlockAntidiag`, or
`Analysis.HighamChapter6Duality`. Their exact 69-constant audit is complete,
but their source moves and wrappers form Phase 11B2. Phase 11B is not complete
until that separately mapped follow-up is pushed. This bounded split makes the
broader Phase 11A forecast explicit instead of silently claiming those four
historical owners have moved.

No declaration rename, visibility change, proof rewrite, modern `module`
syntax migration, compatibility removal, or separate Lake library is in
scope.

## Target production tree

```text
NumStability/Analysis/
  Asymptotics.lean
  Asymptotics/
    Bounds.lean
  LinearOperators.lean
  LinearOperators/
    Basic.lean
    Triangularization.lean
  OperatorNorms.lean
  OperatorNorms/
    Attainment.lean
    Basic.lean
  VectorNorms.lean
  VectorNorms/
    Attainment.lean
    Basic.lean
    Duality.lean
    Interpolation.lean
  MatrixNorms.lean
  MatrixNorms/
    Attainment.lean
    Basic.lean
    Comparisons.lean
    Hadamard.lean
    Lp.lean
    SpectralRadius.lean
    UnitarilyInvariant.lean
  SingularValues.lean
  SingularValues/
    Basic.lean
    Realification.lean
    WeylMirsky.lean
  Conditioning.lean
  Conditioning/
    DistanceToSingularity.lean
    InversePerturbation.lean
  Norms.lean
  Norms/
    Core.lean

NumStability/Source/Higham/
  Chapter06.lean
  Chapter06/
    Norms.lean
    Problem01.lean
    Problem05.lean
    Problem09.lean
    Problem10.lean
    Theorem04.lean
```

Every umbrella and compatibility path in this tree is declaration-free. Child
modules never import a parent umbrella.

## Exact compiled ownership

The tracked declaration-ownership manifest is authoritative over all 1,783
constants. The named-source-command column is diagnostic only; nested named
commands and four anonymous instances make compiled rows the preservation
contract.

| Canonical owner | Named commands | Constants | Public | Internal | Private |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Analysis.VectorNorms.Basic` | 114 | 199 | 147 | 52 | 0 |
| `Analysis.VectorNorms.Interpolation` | 84 | 103 | 97 | 6 | 0 |
| `Analysis.VectorNorms.Duality` | 21 | 58 | 41 | 17 | 0 |
| `Analysis.VectorNorms.Attainment` | 7 | 7 | 7 | 0 | 0 |
| `Analysis.LinearOperators.Basic` | 17 | 31 | 24 | 7 | 0 |
| `Analysis.LinearOperators.Triangularization` | 8 | 13 | 8 | 5 | 0 |
| `Analysis.OperatorNorms.Basic` | 21 | 28 | 21 | 7 | 0 |
| `Analysis.OperatorNorms.Attainment` | 33 | 57 | 33 | 24 | 0 |
| `Analysis.MatrixNorms.Basic` | 91 | 109 | 91 | 18 | 0 |
| `Analysis.MatrixNorms.SpectralRadius` | 24 | 31 | 24 | 7 | 0 |
| `Analysis.MatrixNorms.Lp` | 127 | 208 | 129 | 79 | 0 |
| `Analysis.SingularValues.Basic` | 178 | 232 | 186 | 45 | 1 |
| `Analysis.SingularValues.Realification` | 33 | 38 | 33 | 5 | 0 |
| `Analysis.MatrixNorms.Comparisons` | 128 | 152 | 142 | 10 | 0 |
| `Analysis.MatrixNorms.UnitarilyInvariant` | 12 | 69 | 60 | 9 | 0 |
| `Analysis.MatrixNorms.Hadamard` | 44 | 53 | 44 | 9 | 0 |
| `Analysis.MatrixNorms.Attainment` | 55 | 67 | 55 | 12 | 0 |
| `Analysis.Conditioning.DistanceToSingularity` | 31 | 52 | 31 | 21 | 0 |
| `Analysis.Conditioning.InversePerturbation` | 78 | 114 | 78 | 36 | 0 |
| `Analysis.Asymptotics.Bounds` | 3 | 3 | 3 | 0 | 0 |
| `Source.Higham.Chapter06.Problem01` | 18 | 79 | 75 | 4 | 0 |
| `Source.Higham.Chapter06.Problem05` | 26 | 30 | 27 | 3 | 0 |
| `Source.Higham.Chapter06.Problem09` | 1 | 1 | 1 | 0 | 0 |
| `Source.Higham.Chapter06.Problem10` | 28 | 49 | 28 | 18 | 3 |
| **Total** | **1,182** | **1,783** | **1,385** | **394** | **4** |

The normalized ownership inventory is the sorted UTF-8 payload
`logical_name<TAB>destination_module<TAB>kind<TAB>visibility<LF>`, with
module-encoded private prefixes normalized to `_private.<module>.`. Its
SHA-256 is
`8CDC351C6BC9CE9952318B4E154B034E0F3713E1F9BDAB7DD52EECD5FA8F3E23`;
the payload is 218,032 bytes. The 1,784-line tracked manifest file has SHA-256
`5C1E9E020FE6D7665EAF8E92314C60AA0F8300EAE0A520C2C34D18AEC315E99A` and
is frozen in the same commit as this map.

## Physical and semantic seams

The following Phase 11A Core positions are useful review anchors. The tracked
manifest, not raw line slicing, decides ownership.

Primary source trunks, after the exceptions below, are the vector development
through historical Norms line 2,821, the matrix/Lp development through line
9,585, matrix attainment at lines 18,425–20,198, distance to singularity at
20,199–20,867, and inverse perturbation from 20,868 to the Phase 11A Core
seam. Core positions are historical Norms positions plus nine. These trunks
are review anchors only; the manifest is the exact boundary.

The independent semantic audit extracted these noncontiguous foundations:

- `VectorNorms.Interpolation` owns the complete endpoint/interpolation
  exponent block `lpRecipExp` through the last
  `LpInterpolationData.affineExponent_*` theorem (Core lines 125–486), plus
  the analytic interpolation trunk and
  `complexVecLpNorm_le_of_rowFunctional_bound`.
- `VectorNorms.Duality` owns `IsComplexLinearForm`, the abstract dual API,
  `NormedCVec.exists_normingFunctionalAt_of_unit_vector`, and
  `exists_unit_infNorm_pairing_oneNorm`. The `NormedCVec` carrier, instances,
  normed-space adapter, and `exists_unit_complexVectorNorm` remain in Basic.
- `VectorNorms.Attainment` owns the seven generic vector-norm ratio/max
  declarations. Pure vector support, weighted-infinity-norm, endpoint-pairing,
  and vector norm-sum declarations are also removed from their former matrix/
  singular-value neighborhoods and placed in the appropriate vector leaves.
- `LinearOperators.Basic` owns the 31-constant `ComplexVectorMap`, linearity,
  map algebra, Mathlib-linear-map adapter, and norm-pullback API.
  `LinearOperators.Triangularization` owns the 13-constant basis/flag/quotient
  triangularization development.
- `OperatorNorms.Basic` owns mixed subordinate bound/value definitions,
  algebra, existence, and spectral-radius comparison carriers. Its
  57-constant Attainment sibling owns unit-image, ratio, dual-pairing,
  rank-one, and finite-dimensional maximizing-vector results.
- `MatrixNorms.SpectralRadius` owns the 31-constant concrete spectral carrier,
  triangular similarity, weighted-norm, and arbitrarily-close induced-norm
  construction. `complexMatrixVecMulCoordinateMatrix` remains shared
  foundational support in `MatrixNorms.Basic`: SingularValues signatures and
  bodies depend on one of its generated proof constants, so moving it under
  SpectralRadius would create the false reverse edge
  `SingularValues.Basic -> MatrixNorms.SpectralRadius` without a proof rewrite.
- `MatrixNorms.Attainment` owns the matrix unit-set/max/ratio API, including
  the real-imaginary and positive-semidefinite quadratic maximum results.
  Endpoint admissibility and Riesz–Thorin comparison wrappers instead belong
  to `MatrixNorms.Comparisons`; foundational matrix bound/value existence and
  pullback results belong to `MatrixNorms.Basic`.
- `Asymptotics.Bounds` owns the three generic squeeze and vanishing-bound
  convergence lemmas formerly embedded in InversePerturbation.

Other audited noncontiguous assignments:

- `SingularValues.Basic` owns the singular-value/SVD development beginning at
  historical line 9,586, `ComplexSquareContractionMidpointProperty`, and
  `complexMatrixSingularValue_ne_zero_of_rank_eq_card`, including their
  generated constants.
- `SingularValues.Realification` owns the real-matrix complexification bridge,
  `complexNorm_ofReal_eq_abs`, `opNorm2Le_to_rectOpNorm2Le`, and the real/
  imaginary operator-bound transfer family.
- `MatrixNorms.UnitarilyInvariant` owns the 69-constant generic fixed-shape and
  dimension-uniform unitarily invariant/operator-ideal API. It deliberately
  excludes `ComplexSquareContractionMidpointProperty` and every
  `highamProblem65*` declaration.
- `MatrixNorms.Comparisons` owns the audited generic comparison complement,
  including `rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le` and
  `complexMatrixLpNormOfReal_two_eq_top_singularValue`.
- `VectorNorms.Basic` additionally owns the physically later
  `IsComplexVectorNorm.sum_le`; its signature and proof closure is purely
  vector-norm infrastructure, so leaving it in MatrixNorms.Basic would be a
  semantic misclassification.
- `MatrixNorms.Hadamard` owns source-independent real/complex Hadamard and
  Fourier–Vandermonde infrastructure, excluding the four Problem 6.1 witness
  capstones.

The 69 constants of `MatrixNorms.UnitarilyInvariant` are all generated and
explicit constants below `ComplexMatrixFixedUnitaryInvariantNorm`,
`ComplexMatrixFixedOperatorIdealNorm`, and
`ComplexMatrixOperatorIdealNormFamily`, plus the four concrete Frobenius
fixed/family definition and norm constants. The owner has 60 public and nine
generated internal constants and no private constant.

## Exact Chapter 6 source closures

`Problem01` contains all uppercase `HighamProblem61*` and lowercase
`highamProblem61_*` declarations plus their generated constants. The lowercase
pattern includes the separating underscore so it cannot capture Problem 6.10.
It also contains these distributed witnesses:

- `highamProblem61_s2_hadamard_calc`;
- `highamProblem61_hadamard_s2_quotient_witness`;
- `highamProblem61_complexHadamard_s2_quotient_witness`; and
- `highamProblem61_fourierVandermonde_s2_quotient_witness`.

`Problem05` is the exact 30-constant closure consisting of:

- all 27 compiled `highamProblem65*` constants;
- `complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_of_perm`;
- `complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_basisPerm`; and
- `ComplexMatrixFixedUnitaryInvariantNorm.toOperatorIdealNormOfSVD`.

Generic Frobenius product inequalities remain in `SingularValues.Basic`.
Moving them to the source leaf would create reusable-to-source declaration
edges.

`Problem09` owns only `highamProblem69_frobenius_op2_bounds`.

`Problem10` owns the 49-constant block-shear source family from
`ComplexTwoBlockVec` through
`complexMatrixBlockShearOp2_eq_goldenRatio_of_op2_eq_one`, including three
generated private constants.

## Project dependency DAG

Allowed direct imports within the migrated family are bounded by this acyclic
graph. It is the 29-edge transitive reduction of the compiled owner graph;
isolated compilation may remove an edge but may not add a family edge that
violates it. The existing reusable foundation import
`Analysis.MatrixAlgebra` may be retained where required; no other project
import is permitted in these leaves:

```text
VectorNorms.Basic
Asymptotics.Bounds
LinearOperators.Triangularization

VectorNorms.Interpolation -> VectorNorms.Basic
VectorNorms.Duality       -> VectorNorms.Basic
VectorNorms.Attainment    -> VectorNorms.Basic

LinearOperators.Basic -> VectorNorms.Basic

OperatorNorms.Basic -> LinearOperators.Basic
OperatorNorms.Attainment -> OperatorNorms.Basic
OperatorNorms.Attainment -> VectorNorms.Duality

MatrixNorms.Basic -> OperatorNorms.Basic
MatrixNorms.Basic -> VectorNorms.Duality
MatrixNorms.Basic -> VectorNorms.Interpolation
MatrixNorms.SpectralRadius -> MatrixNorms.Basic
MatrixNorms.SpectralRadius -> LinearOperators.Triangularization

MatrixNorms.Lp -> MatrixNorms.Basic
SingularValues.Basic -> MatrixNorms.Basic
SingularValues.Realification -> SingularValues.Basic
MatrixNorms.UnitarilyInvariant -> SingularValues.Basic

MatrixNorms.Comparisons -> MatrixNorms.Lp
MatrixNorms.Comparisons -> SingularValues.Realification
MatrixNorms.Hadamard -> MatrixNorms.Comparisons
MatrixNorms.Attainment -> MatrixNorms.Comparisons
MatrixNorms.Attainment -> OperatorNorms.Attainment
MatrixNorms.Attainment -> VectorNorms.Attainment

Conditioning.DistanceToSingularity -> MatrixNorms.Attainment
Conditioning.InversePerturbation -> Asymptotics.Bounds
Conditioning.InversePerturbation -> Conditioning.DistanceToSingularity

Chapter06.Problem01 -> MatrixNorms.Hadamard
Chapter06.Problem05 -> MatrixNorms.UnitarilyInvariant
Chapter06.Problem09 -> SingularValues.Basic
Chapter06.Problem10 -> SingularValues.Basic
```

The existing `Chapter06.Theorem04` leaf retargets directly to
`Conditioning.InversePerturbation`; it is a consumer, not one of the 24
manifest destinations.

The compiled declaration graph for this assignment has zero owner cycles and
zero reusable-to-source paths. Mathlib imports are minimized from the original
33-import set by isolated compilation. The checker rejects any external import
outside the original 32 Mathlib modules, any project import beyond
`Analysis.MatrixAlgebra` and the family DAG above, and any BilinearAlgorithm
import set other than the two audited Mathlib replacements. Any required
departure is a measured map deviation and must be documented.

## Aggregates and compatibility surface

Sorted declaration-free aggregates:

- `Asymptotics`: `Bounds`;
- `LinearOperators`: `Basic`, `Triangularization`;
- `OperatorNorms`: `Attainment`, `Basic`;
- `VectorNorms`: `Attainment`, `Basic`, `Duality`, `Interpolation`;
- `MatrixNorms`: `Attainment`, `Basic`, `Comparisons`, `Hadamard`, `Lp`,
  `SpectralRadius`, `UnitarilyInvariant`;
- existing `SingularValues`: `Basic`, `Realification`, `WeylMirsky`;
- `Conditioning`: `DistanceToSingularity`, `InversePerturbation`;
- `Norms.Core`: `Asymptotics`, `Conditioning`, `LinearOperators`,
  `MatrixNorms`, `OperatorNorms`, `SingularValues.Basic`,
  `SingularValues.Realification`, and `VectorNorms`;
- `Source.Higham.Chapter06.Norms`: `Problem01`, `Problem05`, `Problem09`,
  `Problem10`, `Theorem04`; and
- `Source.Higham.Chapter06`: the `Chapter06.Norms` aggregate.

Core imports the two singular-value leaves directly. It must not import the
`SingularValues` umbrella, because that would add the independently extracted
Weyl–Mirsky API to Core's Phase 11A surface.

The historical facade changes from

```text
Analysis.Norms -> Analysis.Norms.Core + Chapter06.Theorem04
```

to

```text
Analysis.Norms -> Analysis.Norms.Core + Chapter06.Norms
```

The dedicated source-family aggregate preserves two direct compatibility
targets while preventing later unrelated Chapter 6 additions from silently
expanding the historical Norms surface. Compatibility inventory therefore
remains 104 wrappers and 204 direct targets.

`Analysis` imports the reusable `Asymptotics`, `Conditioning`,
`LinearOperators`, `MatrixNorms`, `OperatorNorms`, `SingularValues`, and
`VectorNorms` family entry points plus `Source.Higham.Chapter06`, replacing its
direct Core and Theorem 6.4 imports while preserving the aggregate's complete
historical surface.

## Direct-consumer retargets

| Current Core importer | Phase 11B1 import |
| --- | --- |
| `Algorithms.Chapter06Lemma66` | `Analysis.MatrixNorms.Comparisons` |
| `Algorithms.LeastSquares.LSPerturbation` | `Analysis.SingularValues.Realification` |
| `Algorithms.LeastSquares.LSQRSolve` | `Analysis.SingularValues.Realification` |
| `Algorithms.MatrixPowersComplex` | `Analysis.MatrixNorms.Basic` |
| `Algorithms.MatrixPowersLp` | `Analysis.MatrixNorms.Lp` |
| `Algorithms.MatrixPowersLpJordan` | `Analysis.MatrixNorms.Lp` |
| `Algorithms.PNormPowerMethodGeneralP` | `Analysis.MatrixNorms.Lp` and `Analysis.SingularValues.Realification` |
| `Algorithms.QR.Higham19Problem19_9` | `Analysis.SingularValues.Realification` |
| `Algorithms.QR.Higham19TurnbullAitken` | `Analysis.VectorNorms.Basic` |
| `Algorithms.TestMatrices.Higham28Moments` | `Analysis.MatrixNorms.Basic` |
| `Analysis.Higham6Asides` | `Analysis.SingularValues.Basic` |
| `Analysis.Higham6BlockAntidiag` | `Analysis.MatrixNorms.Comparisons` |
| `Analysis.HighamChapter6Duality` | `Analysis.VectorNorms.Duality` |
| `Analysis.HighamChapter7` | `Analysis.Asymptotics.Bounds`, `Analysis.Conditioning.DistanceToSingularity`, `Analysis.MatrixNorms.SpectralRadius`, and `Source.Higham.Chapter06.Problem05` |
| `Analysis.MatrixPowersBaiDemmelGuDistance` | `Analysis.Conditioning.DistanceToSingularity` |
| `Analysis.MatrixPowersLp185Primary` | `Analysis.MatrixNorms.Lp` |
| `Analysis.SingularValues.WeylMirsky` | `Analysis.SingularValues.Basic` |
| `Source.Higham.Chapter14.Problem15` | `Analysis.SingularValues.Realification` |
| `Source.Higham.Chapter22.VandermondeSystems` | `Analysis.MatrixNorms.Hadamard` |
| `Source.Higham.Chapter23.BilinearAlgorithm` | remove Core; add only `Mathlib.Data.Matrix.Mul` and `Mathlib.Data.Real.Basic` |
| `Source.Higham.Chapter23.ThreeM` | `Analysis.MatrixNorms.Basic` |
| `Source.Higham.Chapter27.SoftwareEnvironment` | `Analysis.VectorNorms.Basic` |
| `Source.Higham.Chapter06.Theorem04` | `Analysis.Conditioning.InversePerturbation` |

The Bilinear leaf also removes unused `Topology` and `Filter` opens. Its full
downstream family must rebuild after the edit even though the compiled graph
contains zero Core declaration edges.

No production module may import `Analysis.Norms`. After Phase 11B1, no
production declaration-bearing module may import `Analysis.Norms.Core`.

## Tier and structural forecast

All 20 declaration-bearing Analysis leaves are `reusable`. The four new
Problem leaves inherit `source`. The six new Analysis family umbrellas,
`Source.Higham.Chapter06.Norms`, and the now-structural Core are `aggregate`.
Core plus the Asymptotics, Conditioning, LinearOperators, MatrixNorms,
OperatorNorms, SingularValues, and VectorNorms umbrellas are the eight
reusable entry points for the transitive source-boundary check.

| Measure | Phase 11A | Phase 11B1 forecast |
| --- | ---: | ---: |
| Production modules | 993 | 1,024 |
| Classified modules | 384 | 416 |
| Classification coverage | 38.671% | 40.625% |
| Unclassified modules | 609 | 608 |
| Aggregate modules | 77 | 85 |
| Compatibility modules | 104 | 104 |
| Reusable modules | 58 | 78 |
| Source modules | 138 | 142 |
| Internal modules | 2 | 2 |
| Upstream modules | 5 | 5 |
| Mixed modules | 0 | 0 |
| Compatibility wrappers | 104 | 104 |
| Compatibility direct targets | 204 | 204 |
| Missing module docs | 217 | 217 |
| Legacy naming exceptions | 403 | 403 |

Direct-import totals are intentionally generated after isolated import
minimization; the exact per-leaf project DAG above is frozen, while external
Mathlib imports may narrow. The generated baseline is authoritative and every
departure from this structural forecast must be explained.

## Ownership-manifest enforcement

`docs/architecture/declaration-ownership/norms-phase11b1.tsv` contains one row
for every Phase 11A Core constant. The checker must enforce all of the
following before the semantic split is accepted:

1. the Phase 11A TSV hash and historical owner match this map;
2. every manifest logical name is unique and the set is exactly the 1,783 Core
   declaration rows;
3. pre-migration mode confirms each source row still belongs to Core;
4. post-migration mode confirms exact destination owner, name, kind, and
   visibility, including all generated constants;
5. no declaration is owned by Core, a family umbrella, or a source aggregate;
6. owner counts and the normalized ownership hash match this map;
7. the owner dependency graph is acyclic and contains no reusable-to-source
   path; and
8. the manifest's target-to-baseline bijection normalizes the entire candidate
   declaration and edge stream for an exact Phase 11A comparison.

The manifest is an enforceable input, not generated evidence inferred from the
post-migration result.

The Phase 11A incident-edge payload contains 18,895 rows (7,403 signature and
11,492 body), SHA-256
`0C10D731ED3654D863518B70D6BB4842E3BAE6824CBEC6E848AAA27DC0FE1DD3`.
The 12,625 edges internal to the partition have SHA-256
`542908FA07DB01630D126EFB3812D04783DF5524D82988DC1FA3D46179CC8B7A`.
The post-split checker must reproduce both digests even when the full baseline
stream is unavailable, and the release evidence additionally performs the
full-stream multiset comparison.

## Import and surface tests

Add isolated one-import tests for every new canonical leaf and umbrella:

- `Asymptotics` plus `Bounds`;
- `LinearOperators` plus its two leaves;
- `OperatorNorms` plus its two leaves;
- `VectorNorms` plus its four leaves;
- `MatrixNorms` plus its seven leaves;
- `SingularValues.Basic` and `SingularValues.Realification`, while updating the
  existing SingularValues aggregate test;
- `Conditioning` plus its two leaves;
- the four Chapter 6 Problem leaves and `Chapter06.Norms`.

Update the existing Core test to check representatives from all 20 reusable
owners. Update the old-only `Analysis.Norms` test to check representatives from
all reusable owners, Problems 6.1/6.5/6.9/6.10, and Theorem 6.4. Update the
Chapter 6 aggregate test to check every source child. Update Analysis,
Source.Higham, Higham, SourceCanonical, SourceMigration, Source, All, and root
smokes, plus `examples/LibraryLookup.lean`.

Every source-leaf test imports only that leaf; every reusable-leaf test imports
only that leaf; and the historical test imports only `Analysis.Norms`.

## Live documentation and manifest contract

Update README, ARCHITECTURE, LIBRARY_LOOKUP, TIERS, COMPATIBILITY, endpoint and
outlier reviews, the Chapter 6 coverage ledger, tier inventory, layout debt,
and aggregate/reusable-entry-point contracts. Current comments and examples
must name canonical owners. Dated baselines, this map, and earlier migration
records remain immutable.

Core is removed from the unclassified manifest only after every one of its
declarations has a checked owner. The Phase 11B2 historical source owners
remain explicitly unclassified/noncanonical until that follow-up moves them.

## Exact graph preservation

The Phase 11A-to-11B1 normalized declaration/dependency comparison must be
empty in both directions. The manifest maps all 24 destinations (20 reusable
owners and four source owners) back to
`NumStability.Analysis.Norms.Core` and maps every candidate name to its exact
Phase 11A name before comparing declaration rows and both endpoints of every
signature/body edge.

Public and internal names must be byte-identical. Four private constants have
module-encoded names and therefore use exact manifest rewrites:

- `complex_re_star_mul_ofReal_mul` in `Analysis.SingularValues.Basic`; and
- the three `complexTwoBlockBuild.match_1` generated constants in
  `Source.Higham.Chapter06.Problem10`.

No broader private-prefix rewrite is permitted. The expected global graph
remains exactly 81,950 declarations, 305,425 signature edges, 439,195
body/proof edges, and 491,557 union edges.

## Validation gates

Phase 11B1 is complete only after all of the following pass:

1. every leaf and umbrella builds in isolation in the DAG order above;
2. every direct consumer and Bilinear downstream importer builds;
3. all canonical-only, Core, Chapter 6, historical-only, entry-point, All, and
   root import tests pass;
4. the exact ownership manifest passes in pre- and post-migration modes;
5. no production facade import, declaration-bearing umbrella, child-to-parent
   import, duplicate import, or unsorted aggregate exists;
6. layout, compatibility, provenance, placeholder, exact debt, aggregate,
   source-boundary, and `git diff --check` gates pass;
7. `lake build NumStability`, `lake test`, and
   `lake build NumStability NumStabilityTest` pass sequentially;
8. `lake env lean examples/LibraryLookup.lean` passes;
9. the fresh Phase 11B1 declaration stream matches the Phase 11A stream exactly
   after manifest normalization;
10. strict-source baseline capture and both reproducibility modes pass;
11. representative axiom audits do not exceed
    `[propext, Classical.choice, Quot.sound]`;
12. no `sorry`, `admit`, or new top-level `axiom`/`constant` is introduced;
13. full gates are repeated from a clean implementation commit before baseline
    and evidence commits; and
14. independent source, documentation, ownership-manifest, and frozen full-diff
    reviews report no unresolved findings.

## Required Phase 11B2 follow-up

Phase 11B2 moves the already audited 69 compiled constants from the four
historical Chapter 6 owners to canonical source leaves, leaves declaration-free
compatibility wrappers, removes four naming and unclassified exceptions, and
adds canonical-only and old-only tests. Its map must be committed before those
production edits. Phase 11B2 also decides whether the 28-constant historical
`Higham6Asides` owner remains a cohesive source leaf or becomes a small
declaration-free family over more specific prose-topic leaves.

Only after Phase 11B2 passes may the repository claim that the Chapter 6
mislocation promise made in Phase 11A is complete.
