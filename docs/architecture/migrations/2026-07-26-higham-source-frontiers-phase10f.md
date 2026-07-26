# Higham source frontiers, phase 10F (2026-07-26)

This is the immutable pre-edit ownership record for organization Phase 10F.
It was written on branch `codex/organization-phase-10f-higham-frontiers` at
base revision `b43ef1e0dbc36c22f959fba757a8c97a6df55cf3`, after Phase 10E was
pushed to `main` and after the intervening remote `.gitignore` change was
merged. No production, test, manifest, or live architecture-document edit for
Phase 10F precedes this record.

Phase 10F moves three bounded source frontiers and, unlike the preceding
one-owner moves, splits the Chapter 14 file at a genuine semantic boundary.
The exact canonical tree is:

    NumStability/Analysis/
      SingularValues.lean
      SingularValues/
        WeylMirsky.lean
    NumStability/Source/Higham/Chapter14/
      Problem15.lean
    NumStability/Source/Higham/Chapter21/
      Theorem04.lean
      Theorem04/
        RowwiseBackwardError.lean
    NumStability/Source/Higham/
      Chapter28.lean
      Chapter28/
        Equation02.lean
        Equation02/
          RatioDiscrepancy.lean

The three historical paths remain import-only compatibility modules:

- `NumStability.Algorithms.Chapter14Problem1415Weyl`;
- `NumStability.Algorithms.Underdetermined.Higham21RowwiseMeasure`; and
- `NumStability.Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy`.

This phase preserves every non-private declaration name, namespace, type,
proof, and visibility. Private constants retain their suffixes, types, proofs,
and edges after the explicitly recorded owner-prefix normalization. It does not
rename APIs, minimize imports, migrate the dependencies that remain in
historical files, or reorganize the downstream Chapter 14, Chapter 21, or
Chapter 28 families.

## Frozen baseline

The authoritative compiled input is
`benchmark-results/architecture/phase10e-declarations.tsv`, whose SHA-256 is
`03BC2291A655E9AC394966B6C435E0A25E74B0A56E6EFEEACCDC606C1E8FDE18`.
It describes the same production source tree captured in the clean Phase 10E
baseline, with source digest
`ecf887859377fc8e794d2d4a714943a165bc6fa708b85553c96e50c60b886b9b`.

| Historical owner | Git blob | SHA-256 | Lines | Direct imports | Explicit declarations | Compiled constants |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| `Algorithms.Chapter14Problem1415Weyl` | `33a1603da5093bad50d8eb25dbba9c4b47966f2f` | `B783E3D4AA12223950725DABBC620A0A3255C30504294FE0F6A5CDB8DFAD7998` | 581 | 5 | 21 | 27: 11 public, 3 internal, 13 private |
| `Algorithms.Underdetermined.Higham21RowwiseMeasure` | `87fdcb8119490143ff2a42d73c5970e7c1663188` | `098245ACC618A1E4D80C0530C1121591296C4794C278AED0D127EE60CE1A272F` | 151 | 1 | 10 | 19: 18 public, 1 internal |
| `Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy` | `77444adf045069b5705f66f02522150ed4fad5a0` | `B286D644F43BFB23457F5834CDF8DFF7D7F589C936B19E2213A4F054F67D99F7` | 217 | 1 | 11 | 27: 11 public, 16 internal |

Across the three owners the frozen population is exactly 73 compiled
constants: 40 public, 20 generated internal, and 13 private. Their outgoing
graph contains 97 signature edges and 196 body/proof edges. The global graph is
81,950 declarations, 305,425 signature edges, 439,195 body/proof edges, and
491,557 union edges.

### Frozen direct imports

`Algorithms.Chapter14Problem1415Weyl` imports:

- `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`;
- `Mathlib.LinearAlgebra.Dimension.Constructions`;
- `Mathlib.Order.Interval.Finset.Fin`;
- `NumStability.Analysis.Norms`; and
- `NumStability.Algorithms.MatrixInversion`.

`Algorithms.Underdetermined.Higham21RowwiseMeasure` imports only
`NumStability.Algorithms.Underdetermined.UnderdeterminedSolve`.

`Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy` imports only
`NumStability.Algorithms.TestMatrices.Higham28HilbertAsymptotic`.

## Chapter 14: reusable Weyl--Mirsky versus Problem 14.15

A whole-file move to Source is rejected. The historical module explicitly
contains an honest reusable all-index singular-value perturbation development,
and `Algorithms.LeastSquares.Higham20Lemma20_11` consumes that generic API
outside Chapter 14. The file is split immediately before the current
`ch14ext_complexMatrixEuclideanLin_add` documentation/declaration (current
source line 304/305).

### Reusable owner

`Analysis.SingularValues.WeylMirsky` receives the declarations through
`ch14ext_singularValue_abs_sub_le_of_euclideanLin_diff_bound`:

- private square-root, orthonormal-coordinate, dimension, and intersection
  helpers;
- `ch14ext_singularValue_mul_norm_le_norm_euclideanLin_of_mem_leadSpan`;
- `ch14ext_norm_le_singularValue_mul_norm_of_mem_trailSpan`;
- `ch14ext_singularValue_le_of_euclideanLin_diff_bound`; and
- `ch14ext_singularValue_abs_sub_le_of_euclideanLin_diff_bound`.

This owner has exactly 17 compiled constants: 4 public, 3 generated internal,
and 10 private. It has 14 outgoing signature edges and 43 outgoing body/proof
edges. All project dependency targets are in `Analysis.Norms`. After the split,
it has three incoming body edges: two from
`Algorithms.LeastSquares.Higham20Lemma20_11` and one from canonical Problem 15.

The leaf retains the three frozen Mathlib imports and `Analysis.Norms`.
`Analysis.SingularValues` is a declaration-free complete aggregate over the
Weyl--Mirsky leaf.

### Source owner

`Source.Higham.Chapter14.Problem15` receives
`ch14ext_complexMatrixEuclideanLin_add` and everything following it:

- the real-matrix operator-difference certificate;
- the Problem-14.15 all-index real singular-value specialization;
- the corrected absolute determinant bound;
- the determinant nonsingularity and sign-preservation development;
- the two signed determinant conclusions; and
- the scalar counterexample to the printed guard.

This owner has exactly 10 compiled constants: 7 public and 3 private. It has 24
outgoing signature edges and 48 outgoing body/proof edges. Its project targets
are `Analysis.MatrixAlgebra`, `Analysis.Norms`, `Algorithms.MatrixInversion`,
and the new Weyl--Mirsky leaf. Exactly one cross-split body edge runs in the
allowed direction from Problem 15 to reusable Weyl--Mirsky; there is no
Analysis-to-Source edge.

The source leaf directly imports `Analysis.MatrixAlgebra`, `Analysis.Norms`,
`Analysis.SingularValues.WeylMirsky`, and `Algorithms.MatrixInversion`. These
imports make its elaborated dependencies explicit instead of relying on the
current transitive contents of `MatrixInversion` or Weyl--Mirsky. It retains the
`NumStability.Ch14Ext` namespace and all public/internal `ch14ext_` declaration
names. The historical wrapper imports only the canonical Problem 15 leaf,
which transitively preserves the former complete surface.

Frozen external use consists of two body edges from
`Algorithms.LeastSquares.Higham20Lemma20_11` into the reusable half and one
body edge from `Algorithms.Ch14GaussJordanSPDCorollary` into the source half.
The former consumer retargets to Weyl--Mirsky; the latter retargets to Problem
15. `Algorithms.lean` drops the historical import because its existing
`Source.Higham.Chapter14` import will expose Problem 15.

## Chapter 21: printed row-wise measure and Theorem 21.4

All declarations in `Algorithms.Underdetermined.Higham21RowwiseMeasure` move
intact to `Source.Higham.Chapter21.Theorem04.RowwiseBackwardError`:

- `Higham21RowwiseBackwardErrorFeasible` and its generated API;
- `higham21RowwiseBackwardErrorValuesR`;
- `higham21RowwiseBackwardErrorOmegaR`;
- the lower/upper and fixed-right-hand-side bridge theorems; and
- `higham21_theorem21_4_computed_qhat_omegaR_le_gamma`.

The compiled population is exactly 19 constants: 18 public and one generated
internal. It has 48 outgoing signature edges and 66 outgoing body/proof edges.
Four downstream historical modules account for six incoming signature and
seven incoming body/proof edges: `Higham21Givens`, `Higham21GivensRounded`,
`Higham21GivensClosure`, and `Higham21MGSRounded`.

The source leaf retains its sole import of `UnderdeterminedSolve`.
`Source.Higham.Chapter21.Theorem04` is a declaration-free complete aggregate.
Direct importers `Higham21Givens` and `Higham21MGSRounded` retarget to the
canonical leaf. The historical `Higham21` aggregate replaces the old leaf with
canonical `Theorem04`. The transitive Givens consumers receive no new direct
import, but they are mandatory focused-build targets.

This bounded destination is preferable to splitting a Section 21.3 definition
from Theorem 21.4: the file culminates in the concrete Householder Theorem-21.4
endpoint, and a further source/API split would exceed an ownership-only move.

## Chapter 28: equation (28.2) ratio discrepancy

All declarations in
`Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy` move intact to
`Source.Higham.Chapter28.Equation02.RatioDiscrepancy`. The owner includes the
normalized determinant, exact recurrence and central-binomial bound, divergence
theorems, literal-model rewrites, and final
`higham28_not_HilbertDetAsymptotic` endpoint.

The compiled population is exactly 27 constants: 11 public and 16 generated
internal. It has 11 outgoing signature edges, 39 outgoing body/proof edges, and
no incoming compiled edge from another owner. Its sole production importer is
`Algorithms.lean`.

The canonical leaf retains its current import of the unclassified historical
`Algorithms.TestMatrices.Higham28HilbertAsymptotic`. That dependency is
deliberate incremental debt, not a claim that equation (28.2) is fully
migrated. A later Equation-02 batch must move the exact/leading-log dependency
and retarget this leaf without changing its public destination.

`Source.Higham.Chapter28.Equation02` and `Source.Higham.Chapter28` are
declaration-free complete aggregates over their current physical descendants.
The Chapter 28 aggregate must be described as an incremental canonical entry
point, not as complete Chapter 28 source coverage. `Source.Higham` adds the new
chapter aggregate, and `Algorithms.lean` replaces the historical discrepancy
import with `Source.Higham.Chapter28`.

The Apache-2.0 copyright, SPDX identifier, author, and license pointer move
unchanged to the canonical implementation. The old wrapper contains no copied
implementation header, so the audited Apache production-file count stays
unchanged.

## Production import contract

No production module may import any of the three moved historical paths after
the migration. The wrappers themselves are the only historical entry points.
Exact production changes are:

- add `Analysis.SingularValues` to the Analysis entry point;
- add Problem 15 to canonical Chapter 14;
- add Theorem 04 to canonical Chapter 21;
- add Chapter 28 to `Source.Higham`;
- retarget the two explicit Chapter-14 consumers to the appropriate semantic
  half;
- retarget `Higham21Givens` and `Higham21MGSRounded` to the Theorem-04 leaf;
- retarget the historical `Higham21` aggregate to canonical Theorem 04; and
- replace the two direct historical imports in `Algorithms.lean` with the
  canonical aggregate exposure described above.

Child leaves import leaves, never their parent aggregates. Aggregates remain
declaration-free and their imports remain sorted.

## Tests and manifests

Eleven isolated one-import tests are required and must be registered in sorted
order in `NumStabilityTest.lean`:

- `Import/Analysis/SingularValues`;
- `Import/Analysis/SingularValues/WeylMirsky`;
- `Import/Source/Chapter14/Problem15`;
- `Import/Compatibility/Source/Chapter14/AlgorithmsChapter14Problem1415Weyl`;
- `Import/Source/Chapter21/Theorem04`;
- `Import/Source/Chapter21/Theorem04/RowwiseBackwardError`;
- `Import/Compatibility/Source/Chapter21/AlgorithmsUnderdeterminedHigham21RowwiseMeasure`;
- `Import/Source/Chapter28`;
- `Import/Source/Chapter28/Equation02`;
- `Import/Source/Chapter28/Equation02/RatioDiscrepancy`; and
- `Import/Compatibility/Source/Chapter28/AlgorithmsTestMatricesHigham28HilbertRatioDiscrepancy`.

Old-only tests import exactly one historical path. Canonical leaf/aggregate
tests import exactly one canonical path. Representative generic Weyl, Problem
15, row-wise/Theorem-04, recurrence/divergence, and final discrepancy checks are
also added to the affected Analysis, Chapter 14, Chapter 21, Higham, Source,
Algorithms, SourceCanonical, SourceMigration, All, and root smoke surfaces.
`SourceCanonical` must cover each new canonical source target;
`SourceMigration` must cover both the canonical targets and all three
historical forwarding paths.

The tier manifest records:

- `Analysis.SingularValues.WeylMirsky` as reusable;
- the three canonical source leaves as source;
- `Analysis.SingularValues`, `Chapter21.Theorem04`, `Chapter28`, and
  `Chapter28.Equation02` as aggregate; and
- all three historical paths as compatibility.

The compatibility inventory gains three one-to-one rows. Layout exceptions add
four complete-aggregate contracts and remove all three historical paths from
unclassified and noncanonical debt. Only the Chapter-21 historical owner lacks
a module docstring, so missing-doc debt drops by one.

The exact Phase 10E-to-10F structural forecast is:

| Measure | Phase 10E | Phase 10F forecast |
| --- | ---: | ---: |
| Lean modules | 982 | 990 |
| Direct imports | 4,048 | 4,060 |
| Internal direct imports | 2,680 | 2,692 |
| External direct imports | 1,368 | 1,368 |
| Classified modules | 370 | 381 |
| Classification coverage | 37.678% | 38.485% |
| Unclassified modules | 612 | 609 |
| Aggregate modules | 72 | 76 |
| Compatibility modules | 100 | 103 |
| Reusable modules | 57 | 58 |
| Source modules | 134 | 137 |
| Internal modules | 2 | 2 |
| Upstream modules | 5 | 5 |
| Mixed modules | 0 | 0 |
| Compatibility wrappers | 100 | 103 |
| Compatibility direct targets | 199 | 202 |
| Missing module docs | 218 | 217 |
| Legacy naming exceptions | 406 | 403 |

The generated baseline, not the forecast, is authoritative. Any difference
must be explained in final build evidence rather than hidden by unrelated debt
cleanup.

## Validation gates

Phase 10F is complete only after all of the following pass:

1. focused builds of all canonical leaves, aggregates, wrappers, direct
   consumers, and transitive compiled consumers named above;
2. all eleven isolated canonical-only and old-only import tests;
3. affected Analysis, Chapter 14, Chapter 21, Chapter 28, Higham, Source,
   Algorithms, SourceCanonical, SourceMigration, All, and root smokes;
4. layout, compatibility, provenance, source-boundary, aggregate-ordering,
   placeholder, and exact legacy-debt contracts;
5. `lake build NumStability`, `lake test`, and
   `lake build NumStability NumStabilityTest`;
6. `lake env lean examples/LibraryLookup.lean`;
7. a fresh declaration/dependency extraction with an exact normalized
   Phase-10E/Phase-10F comparison;
8. a strict-source architecture baseline and reproducibility check;
9. independent production, documentation, and full-diff review; and
10. repetition of the full gates from a clean implementation commit before
    baseline and evidence commits.

For the exact graph comparison, both new Chapter-14 owner modules normalize to
the single historical owner. Their private prefixes normalize independently
from `_private.NumStability.Analysis.SingularValues.WeylMirsky.0.` and
`_private.NumStability.Source.Higham.Chapter14.Problem15.0.` to
`_private.NumStability.Algorithms.Chapter14Problem1415Weyl.0.`. The Chapter-21
and Chapter-28 owners normalize one-to-one. No other name or owner rewrite is
permitted.

## Explicitly deferred work

This phase does not migrate:

- the remaining Chapter-14 GJE, Methods B/C/D, Corollaries 14.6/14.7, Problem
  14.2, or their supporting families;
- the remaining Chapter-21 equations, perturbation, Givens/MGS, SNE, and
  Theorem-21.4 source-closure families, or the mixed
  `UnderdeterminedSolve`/`UnderdeterminedSpec` base;
- the Chapter-28 Hilbert exact/leading-log dependency, Cauchy, Randsvd,
  Stewart, Gaussian/Haar, Ginibre, Pascal, Toeplitz, companion, moments,
  probability, and contract families;
- declaration renames, public aliases, proof refactors, or import minimization;
  or
- the later `Analysis.Norms` giant-file split, except that the new reusable
  Weyl--Mirsky leaf establishes a semantic consumer for that future work.
