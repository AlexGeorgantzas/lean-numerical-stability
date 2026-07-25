# Phase 10E: Higham Chapter 14/21/28 frontier map

Date: 2026-07-24

Execution base: eabb6bdffaee9a42f96bdb9a37aa194d5421755d

This is the immutable pre-edit ownership and validation record for Phase 10E.
It is committed before any production Lean file, test, entry point, manifest,
exception list, or documentation page is changed. Any implementation departure
must be recorded later in the Phase 10E build-evidence file; this map itself is
not amended after implementation begins.

## Scope and objective

Phase 10E advances each of the three remaining Higham source families through
one dependency-contained frontier:

1. move the source-specific Hyman determinant formalization from the flat
   Algorithms Chapter-14 path to canonical Problem 14.14 ownership;
2. move the source-specific attainment refinements for Theorem 21.3 from the
   historical underdetermined-solver path to canonical Theorem 21.3 ownership;
3. extract the generic homogeneous-space measure-uniqueness lemmas used by the
   Chapter-28 Stewart development from a source-flavoured test-matrix path into
   reusable probability analysis.

The exact destination tree is:

    NumStability/Analysis/Probability/
      Haar.lean
      Haar/
        HomogeneousSpaceUniqueness.lean
    NumStability/Source/Higham/Chapter14/
      Problem14.lean
    NumStability/Source/Higham/Chapter21/
      Theorem03.lean
      Theorem03/
        Attainment.lean

The three historical paths remain import-only compatibility modules:

- NumStability.Algorithms.Ch14HymanDeterminant;
- NumStability.Algorithms.Underdetermined.Higham21Theorem21_3Attainment; and
- NumStability.Algorithms.TestMatrices.Higham28HaarFibers.

This phase is deliberately an ownership-only migration. It does not rename a
declaration, change a namespace, alter a type or proof, minimize implementation
imports, or split the large dependencies that the moved files currently use.

## Frozen source inventory

The files below are frozen at the execution base. SHA-256 is over the working
tree bytes; Git blob identity is also recorded so the source can be recovered
unambiguously.

| Historical owner | Git blob | SHA-256 | Lines | Direct imports | Explicit declarations | Compiled constants |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Algorithms.Ch14HymanDeterminant | c34c5572491273fa67c092654fcb89d91a921151 | 44D9AEE5DAC63F27E7B2AB257272E5338B75416C528177B68C6E20EB929F83D8 | 657 | 13 | 11 | 39: 12 public, 24 internal, 3 private |
| Algorithms.Underdetermined.Higham21Theorem21_3Attainment | 5c0012e1c6bca80435c8f2c3592e19e55227b161 | D9B19A2281DC2117EBE6ED588698B188048393BFA85D8A434589ABCD51457B6B | 557 | 4 | 18 | 29: 18 public, 11 internal |
| Algorithms.TestMatrices.Higham28HaarFibers | e428859f70f9bf088601ebfb68c843a834797ef4 | AB2722D7FC8B0E843670A739F7D274B5E05920B3B7B91E433EEBDE8B5630FF03 | 213 | 2 | 3 | 4: 3 public, 1 internal |

The authoritative compiled baseline is
benchmark-results/architecture/phase10d-declarations.tsv. Across these three
owners it records exactly 72 constants: 33 public, 36 generated internal, and
3 private. Their outgoing graph has 125 signature edges and 269 body/proof
edges. The global baseline is 81,950 declarations, 305,425 signature edges,
439,195 body/proof edges, and 491,557 union edges.

### Frozen imports

Algorithms.Ch14HymanDeterminant directly imports:

- Mathlib.Data.Real.Basic;
- Mathlib.Algebra.BigOperators.Group.Finset.Basic;
- Mathlib.Algebra.BigOperators.Ring.Finset;
- Mathlib.Algebra.BigOperators.Fin;
- Mathlib.LinearAlgebra.Matrix.Determinant.Basic;
- Mathlib.Tactic.Linarith;
- Mathlib.Tactic.Ring;
- NumStability.FloatingPoint.Model;
- NumStability.Analysis.Rounding;
- NumStability.Analysis.MatrixAlgebra;
- NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution;
- NumStability.Algorithms.DotProduct; and
- NumStability.Algorithms.MatrixInversion.

Algorithms.Underdetermined.Higham21Theorem21_3Attainment directly imports:

- Mathlib.Tactic.FinCases;
- Mathlib.Tactic.NormNum;
- Mathlib.Topology.MetricSpace.Pseudo.Defs; and
- NumStability.Algorithms.Underdetermined.UnderdeterminedSolve.

Algorithms.TestMatrices.Higham28HaarFibers directly imports:

- Mathlib.MeasureTheory.Group.LIntegral; and
- Mathlib.MeasureTheory.Integral.Prod.

All implementation imports above are retained verbatim in the canonical
owners. Import minimization is outside this phase.

## Exact declaration ownership

### Chapter 14, Problem 14.14

All declarations in Algorithms.Ch14HymanDeterminant move intact to
Source.Higham.Chapter14.Problem14. The explicit declarations, in source order,
are:

- ch14ext_backSub_zeroDiag_perturbed;
- ch14ext_flDiagProdAux;
- ch14ext_flDiagProd;
- ch14ext_flDiagProdAux_expand;
- ch14ext_flDiagProd_relError;
- ch14ext_hymanSchur_eq_of_leftInverse;
- ch14ext_flHymanDet;
- ch14ext_hyman_flDet_backward_error;
- ch14ext_hyman_flDet_backward_error_original;
- ch14ext_hyman_diagonalSimilarity_bound_invariant; and
- ch14ext_hyman_flDet_diagonalSimilarity.

Their namespace remains NumStability.Ch14Ext. The compiled population is exact
at 39 constants: 12 public, 24 generated internal, and 3 private. In particular,
the public generated equation theorem ch14ext_flDiagProdAux.eq_def and the
private match splitter/equation constants must survive. Private owner prefixes
are normalized only for the owner-comparison gate. The owner has 49 signature
and 124 body/proof outgoing edges. No declaration outside this owner has an
incoming compiled edge to one of its constants at the frozen baseline.

The source text is explicitly tied to Higham Section 14.6.1 and Problem 14.14;
it is therefore a source module, not reusable Algorithms infrastructure.

### Chapter 21, Theorem 21.3

All declarations in
Algorithms.Underdetermined.Higham21Theorem21_3Attainment move intact to
Source.Higham.Chapter21.Theorem03.Attainment. The explicit declarations, in
source order, are:

- higham21SigmaMinRow_eq_zero_of_square_nontrivial_kernel;
- higham21_theorem21_3_square_sigma_term_eq_zero;
- higham21_theorem21_3_square_nonzero_formula_eq_phi;
- higham21_theorem21_3_square_nonzero_etaF_eq_phi;
- higham21_theorem21_3_exists_exact_attaining_perturbation_of_pairing_ne_zero;
- higham21_theorem21_3_etaF_is_attained_of_pairing_ne_zero;
- higham21_theorem21_3_nonzero_formula_mem_closure_attainable_costs;
- higham21_theorem21_3_nonzero_etaF_mem_closure_attainable_costs;
- higham21_theorem21_3_exact_attainment_or_pairing_obstruction;
- higham21Thm21_3ScalarNonattainmentA;
- higham21Thm21_3ScalarNonattainmentB;
- higham21Thm21_3ScalarNonattainmentY;
- higham21Thm21_3ScalarNonattainmentY_ne_zero;
- higham21_theorem21_3_scalar_pairing_obstruction;
- higham21_theorem21_3_scalar_formula_is_not_exactly_attainable;
- higham21_theorem21_3_scalar_formula_not_mem_attainable_costs;
- higham21_theorem21_3_scalar_etaF_is_not_attained; and
- higham21_theorem21_3_scalar_attainable_costs_not_closed.

Their namespace remains NumStability. The compiled population is exact at 29
constants: 18 public and 11 generated internal. The non-obvious generated
constant NumStability.undetResidualHigham.eq_1 is part of this owner and must
move with it. The owner has 76 signature and 144 body/proof outgoing edges. No
declaration outside this owner has an incoming compiled edge to one of its
constants at the frozen baseline.

The canonical implementation continues to depend on the large historical
UnderdeterminedSolve module. Splitting that dependency belongs to a later
roadmap stage and must not be combined with this source move.

### Reusable Haar homogeneous-space uniqueness

All declarations in Algorithms.TestMatrices.Higham28HaarFibers move intact to
Analysis.Probability.Haar.HomogeneousSpaceUniqueness:

- MeasureTheory.measure_eq_of_right_fiber_average;
- MeasureTheory.measure_eq_of_left_fiber_average; and
- MeasureTheory.measure_eq_of_invariant_probability_of_pretransitive.

Their namespace remains MeasureTheory. The compiled population is exact at
four constants: three public theorems and generated internal theorem
MeasureTheory.measure_eq_of_left_fiber_average._simp_1_1. The owner has zero
signature and one body/proof outgoing edge. It has three incoming compiled
edges from outside the owner, all through the sole production consumer
Algorithms.TestMatrices.Higham28OrthogonalSphere.

These theorems are generic finite homogeneous-space measure-uniqueness results;
they contain no Chapter-28 declaration prefix or source locator. Canonical
Source.Higham.Chapter28 ownership would therefore be a category error. The
Chapter-28 consumer remains source-specific while importing this reusable API.

## Import-surface preservation and retargeting

The old paths preserve their complete historical surfaces with one direct
canonical target each:

| Historical path | Canonical target |
| --- | --- |
| Algorithms.Ch14HymanDeterminant | Source.Higham.Chapter14.Problem14 |
| Algorithms.Underdetermined.Higham21Theorem21_3Attainment | Source.Higham.Chapter21.Theorem03.Attainment |
| Algorithms.TestMatrices.Higham28HaarFibers | Analysis.Probability.Haar.HomogeneousSpaceUniqueness |

Production import changes are exact:

- Source.Higham.Chapter14 adds Problem14;
- Algorithms removes its direct historical Hyman import and receives the same
  surface through its already-present Source.Higham.Chapter14 import;
- Source.Higham.Chapter21 adds the new Theorem03 aggregate;
- Algorithms.Underdetermined.Higham21 replaces the historical Theorem-21.3
  leaf import with Source.Higham.Chapter21.Theorem03 while retaining the broad
  Source.Higham.Chapter21 import during the incremental migration;
- Analysis.Probability adds the new Haar aggregate;
- Algorithms.TestMatrices.Higham28OrthogonalSphere replaces the historical
  Haar import with the canonical reusable leaf.

No canonical production module may import one of the three historical paths.
The compatibility wrappers themselves are the only allowed importers after the
migration.

## Aggregates, tests, and manifests

Two new declaration-free sorted aggregates are required:

- Analysis.Probability.Haar over HomogeneousSpaceUniqueness; and
- Source.Higham.Chapter21.Theorem03 over Attainment.

The existing Chapter14, Chapter21, and Probability aggregates add the new
canonical children. No aggregate may acquire declarations.

Eight isolated import tests are required:

- Source/Chapter14/Problem14;
- Compatibility/Source/Chapter14/AlgorithmsCh14HymanDeterminant;
- Source/Chapter21/Theorem03;
- Source/Chapter21/Theorem03/Attainment;
- Compatibility/Source/Chapter21/AlgorithmsUnderdeterminedHigham21Theorem21_3Attainment;
- Analysis/Probability/Haar;
- Analysis/Probability/Haar/HomogeneousSpaceUniqueness; and
- Compatibility/Analysis/Probability/AlgorithmsTestMatricesHigham28HaarFibers.

Existing Chapter14, Chapter21, Probability, Algorithms, Source, All, and root
entry-point smokes gain representative checks. Every new test is registered in
NumStabilityTest.lean. The old-only tests must import exactly the historical
path so they genuinely validate compatibility rather than receiving the API
from an umbrella.

The tier manifest records:

- Problem14 and Theorem03.Attainment as source;
- Theorem03, Haar, and the existing chapter/probability umbrellas as aggregate;
- HomogeneousSpaceUniqueness as reusable; and
- all three old paths as compatibility.

The compatibility inventory gains three one-to-one rows. Layout exceptions add
complete-aggregate contracts for Haar and Theorem03 and remove the three old
paths from unclassified and noncanonical debt. Only the historical Theorem-21.3
path is currently in missing-module-doc debt, so that debt drops by one.

## Provenance

The Hyman and Theorem-21.3 implementations currently use the repository's
default MIT license and receive SPDX-License-Identifier: MIT in their canonical
files. The Haar implementation carries an Apache-2.0 notice; that notice,
copyright, author, and LICENSES/Apache-2.0.txt pointer move unchanged to the
canonical file. Wrappers contain no copied implementation. The move must leave
the audited Apache production-file count unchanged.

## Expected structural ratchet

Against the clean Phase 10D baseline:

| Metric | Phase 10D | Expected Phase 10E |
| --- | ---: | ---: |
| Production modules | 977 | 982 |
| Classified modules | 362 | 370 |
| Unclassified modules | 615 | 612 |
| Aggregate modules | 70 | 72 |
| Compatibility modules | 97 | 100 |
| Compatibility direct targets | 196 | 199 |
| Reusable modules | 56 | 57 |
| Source modules | 132 | 134 |
| Internal modules | 2 | 2 |
| Upstream modules | 5 | 5 |
| Mixed modules | 0 | 0 |
| Missing module-doc exceptions | 219 | 218 |
| Noncanonical-name exceptions | 409 | 406 |
| Declaration-bearing umbrella exceptions | 0 | 0 |
| Unsorted aggregate exceptions | 0 | 0 |

The compiled declaration and edge totals must remain exactly unchanged. The 72
frozen constants must retain exact names, kinds, visibility, types, and
bodies/proofs after normalizing only the three old owner names to their exact
canonical destinations and normalizing the Hyman private-owner prefix.

## Mandatory validation gates

Implementation is accepted only after all of the following pass:

1. focused builds of the five new canonical modules, three wrappers, the three
   retargeted consumers, and affected aggregates;
2. all eight isolated import tests plus updated entry-point smokes;
3. the static module-layout, compatibility, tier, and provenance checks;
4. strict source-coverage validation and check-mode regeneration;
5. root lake build and lake test;
6. LibraryLookup.lean;
7. a fresh declaration graph extraction showing unchanged global names,
   kinds, visibility, signature edges, and body/proof edges after exact owner
   normalization;
8. a fresh architecture baseline matching the structural ratchet or a
   documented evidence-backed departure;
9. the same gates from a clean implementation commit; and
10. an independent full-diff review with no unresolved findings.

## Explicitly deferred work

This batch does not claim completion of Chapters 14, 21, or 28. It deliberately
defers:

- the remaining Chapter-14 GJE, Methods B/C/D, Corollaries 14.6/14.7, Problems
  14.2/14.15, and related source families;
- the remaining Chapter-21 equations, perturbation, Givens/MGS, SNE, and
  Theorem-21.4 families, plus the later UnderdeterminedSolve/Spec split;
- the Chapter-28 Hilbert, Cauchy, Randsvd, Stewart, Gaussian/Haar, Ginibre,
  Pascal, Toeplitz, companion, moments, probability, and contract families;
- declaration renames or source-neutral API aliases; and
- import minimization or proof refactoring.

Those items remain in roadmap stage 1 or their later dedicated stages.
