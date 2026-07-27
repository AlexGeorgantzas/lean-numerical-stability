# Chapter 6 historical source-tail migration, phase 11B2 (2026-07-27)

This is the immutable pre-edit ownership record for organization Phase 11B2.
It was written on branch
`codex/organization-phase-11b2-chapter06-source-tail` at base revision
`aad584a2d50252860adcc38f0b7f5c92c738d2f2`, after Phase 11B1 was
validated and pushed to `main`. No production, test, manifest,
compatibility-table, or live architecture-document edit for Phase 11B2
precedes this record.

Phase 11B2 completes the bounded Chapter 6 source-location promise made by
Phases 11A and 11B1. It moves exactly 69 compiled constants from four
historical, noncanonical owners into nine canonical Higham Chapter 6 source
leaves, retains the four old paths as declaration-free one-target wrappers,
and introduces two declaration-free source-family aggregates. It changes no
declaration name, namespace, type, proof, or visibility.

The exact target tree is:

```text
NumStability/
  Algorithms/
    Chapter06Lemma66.lean                         compatibility wrapper
  Analysis/
    Higham6Asides.lean                            compatibility wrapper
    Higham6BlockAntidiag.lean                     compatibility wrapper
    HighamChapter6Duality.lean                    compatibility wrapper
  Source/Higham/
    Chapter06.lean                                complete chapter aggregate
    Chapter06/
      Asides.lean                                 historical-asides aggregate
      Asides/
        ConditionNumberBounds.lean                source implementation
        EuclideanNormDifferentiability.lean       source implementation
        MaxNormInconsistency.lean                 source implementation
        UnitaryInvariance.lean                    source implementation
      BlockAntidiagonalNorm.lean                   source-family aggregate
      BlockAntidiagonalNorm/
        InducedLp.lean                            source implementation
        OperatorTwo.lean                          source implementation
      Equation01.lean                             source implementation
      Equation02.lean                             source implementation
      Lemma06.lean                                source implementation
      Norms.lean                                  unchanged Phase 11B1 aggregate
```

No `Basic`, `Defs`, `Lemmas`, generic `Source`, or proof-progress module is
introduced. `Lemma06`, `Equation01`, and `Equation02` use the repository's
zero-padded Higham locator dialect. The two deeper families exist because they
have real independently importable subtopics, not for visual symmetry.

## Frozen baseline

The authoritative compiled input is
`benchmark-results/architecture/phase11b1-declarations.tsv`, whose SHA-256 is
`89A22BFBB70513DE4FEE3734AABC1FDADA3FC7C737164923808CBCD4FC79EB30`.
The full frozen graph contains exactly 81,950 declarations, 305,425 signature
edges, 439,195 body/proof edges, and 491,557 union edges.

The four historical source files are frozen as follows:

| Historical owner | Lines | Nonblank | Imports | Compiled constants | Public | Internal | Private | Git blob | File SHA-256 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `NumStability.Algorithms.Chapter06Lemma66` | 195 | 162 | 1 | 20 | 18 | 2 | 0 | `e77cf90076df969fd8913a0cf23d85ff22976235` | `7DBA23F91B7EF716F87369029FB725BC9AD20ACBFF2CF3727A448EFAEB5BE9A4` |
| `NumStability.Analysis.Higham6Asides` | 601 | 557 | 5 | 28 | 25 | 1 | 2 | `ae339421293be1685e40236d7da100234a4caf65` | `6835CCFB433E17565A8FB7B70B38BEF48BF8B2F8D94FB15EC5AF4F7F8C6D855C` |
| `NumStability.Analysis.Higham6BlockAntidiag` | 287 | 264 | 3 | 18 | 10 | 7 | 1 | `bc5a22d3183c077516563c3acd49619bf903f61b` | `571405FD9DB25F98DCC28D0410912EF89B6CE0E4D85105FFF687BFF87A350269` |
| `NumStability.Analysis.HighamChapter6Duality` | 76 | 65 | 2 | 3 | 3 | 0 | 0 | `1c8c1b00563a7507546af5553348a1bc528bc445` | `7659D24307EEE256400E0157C89EA4BB656577F5613EC7CA6BCE0B09CDD520D2` |

The partition is exactly 69 constants: 56 public, ten generated/internal, and
three private; seven are definitions and 62 are theorems. The reviewed,
normalized 69-row target-partition payload is 7,026 bytes with SHA-256
`77BCFAC7F5987F2EF16DFF59EB621924FDECE8754593D0C3679782326C75090B`.

The tracked five-column ownership manifest additionally records each
historical owner. Its normalized 11,091-byte row payload has SHA-256
`28FDFD53016CDD5365ED32089DED59625F1E37007C119F9705B7F7C26B948581`;
the 11,100-byte file, including `format\t1`, has SHA-256
`33A67750AD55F9C1E856A3B8FF2868CF81EBE0E5144BF75EA992BB905E77E8FD`.

The exact typed incident stream contains 440 edges: 158 signature and 282
body/proof edges, collapsing to 293 union edges. Its canonical 40,382-byte
serialization has SHA-256
`9E879119F3FEB28FC64A6B554C59F110C685AFDB9C8BAE83D918709536950C28`.
The induced internal stream contains 126 typed edges (37 signature and 89
body/proof), collapsing to 95 union edges. Its canonical 12,627-byte
serialization has SHA-256
`880A472E8600F18DCA192C89FB7B3AF0A2157E395FB93426281646C4028C9987`.
These payloads are checker inputs, not values inferred from the post-migration
tree.

## Exact destination ownership and declaration order

The following order is the historical source order. Generated constants are
listed immediately after the command that creates them. Parenthetical labels
record `kind/visibility` where the entry is not an ordinary public theorem.

### `Source.Higham.Chapter06.Lemma06` -- 20 constants

This leaf receives all of `Algorithms.Chapter06Lemma66`, preserving the
`NumStability.Lemma66` namespace:

1. `NumStability.Lemma66.lemma66_colNormSq` (definition/public);
2. `NumStability.Lemma66.lemma66_colNorm2` (definition/public);
3. `NumStability.Lemma66.lemma66_colNorm2.eq_1` (theorem/internal);
4. `NumStability.Lemma66.lemma66_colNorm1` (definition/public);
5. `NumStability.Lemma66.lemma66_colNorm1.eq_1` (theorem/internal);
6. `NumStability.Lemma66.lemma66_colNormSq_nonneg`;
7. `NumStability.Lemma66.lemma66_colNorm2_nonneg`;
8. `NumStability.Lemma66.lemma66_colNorm1_nonneg`;
9. `NumStability.Lemma66.lemma66_colNorm2_sq`;
10. `NumStability.Lemma66.lemma66_frobeniusSq_eq_sum_colNormSq`;
11. `NumStability.Lemma66.lemma66_entry_le_colNorm2`;
12. `NumStability.Lemma66.lemma66_colNorm2_le_colNorm1`;
13. `NumStability.Lemma66.lemma66_colNormSq_le_of_colNorm2_le`;
14. `NumStability.Lemma66.lemma66_a_frobenius_le`;
15. `NumStability.Lemma66.lemma66_a_abs_entry_le`;
16. `NumStability.Lemma66.lemma66_a_op2_le`;
17. `NumStability.Lemma66.lemma66_colNormSq_le_of_abs_entry_le`;
18. `NumStability.Lemma66.lemma66_colNorm2_le_of_abs_entry_le`;
19. `NumStability.Lemma66.lemma66_c_op2_le`; and
20. `NumStability.Lemma66.lemma66_a_op2_sharp`.

The owner has three public definitions, 15 public theorems, and two internal
theorems.

### `Source.Higham.Chapter06.Asides.EuclideanNormDifferentiability` -- 2 constants

This leaf receives the corrected p. 105 differentiability prose:

1. `NumStability.higham6_euclideanNorm_not_differentiableAt_zero`; and
2. `NumStability.higham6_euclideanNorm_hasFDerivAt_of_ne_zero`.

Both are public theorems. The module docstring must state explicitly that the
first theorem refutes the literal claim at zero and the second gives the
correct nonzero real Frechet derivative; `Correction` is omitted from the
filename because the paired counterexample/corrected theorem already makes
the status explicit in the API and documentation.

### `Source.Higham.Chapter06.Equation01` -- 4 constants

This leaf receives the equality prose attached to Higham equation (6.1):

1. `NumStability.higham6_holder_commonRay_norm_eq`;
2. `NumStability.higham6_holder_scalar_equality_of_powerProfile`;
3. `NumStability.higham6_holder_equality_of_powerProfile_sameRay`; and
4. `NumStability.higham6_holder_endpoint_equality_standardBasis`.

All four are public theorems.

### `Source.Higham.Chapter06.Asides.UnitaryInvariance` -- 6 constants

This leaf owns the operator-2 adapter and two-sided unitary-invariance chain:

1. `NumStability.ch6aside_op2_eq_l2`;
2. `_private.NumStability.Analysis.Higham6Asides.0.NumStability.ch6aside_l2_one`
   (theorem/private; expected target private name recorded below);
3. `_private.NumStability.Analysis.Higham6Asides.0.NumStability.ch6aside_l2_unitary`
   (theorem/private; expected target private name recorded below);
4. `NumStability.ch6aside_op2_two_sided_unitary_invariant`;
5. `NumStability.ch6aside_frobeniusSq_eq_trace`; and
6. `NumStability.ch6aside_frobenius_two_sided_unitary_invariant`.

The owner has four public and two private theorems.

### `Source.Higham.Chapter06.Asides.ConditionNumberBounds` -- 7 constants

This leaf owns the p. 108--109 condition-number and submultiplicativity chain:

1. `NumStability.ch6aside_complexMatrixMul_eq_matMul`;
2. `NumStability.ch6aside_conditionNumber_ge_one`;
3. `NumStability.ch6aside_op2_mul_le`;
4. `NumStability.ch6aside_op2_conditionNumber_ge_one`;
5. `NumStability.ch6aside_frobenius_one`;
6. `NumStability.ch6aside_frobenius_mul_le`; and
7. `NumStability.ch6aside_conditionF_ge_sqrt_n`.

All seven are public theorems. `ch6aside_op2_mul_le` has the one exact
cross-leaf body dependency on `ch6aside_op2_eq_l2`, so this leaf depends on
`Asides.UnitaryInvariance`.

### `Source.Higham.Chapter06.Asides.MaxNormInconsistency` -- 6 constants

This leaf receives the max-norm inconsistency and sharp all-ones witness chain:

1. `NumStability.ch6aside_maxNorm_mul_le`;
2. `NumStability.ch6aside_maxNorm_allOnes`;
3. `NumStability.ch6aside_maxNorm_allOnes_mul`;
4. `NumStability.ch6aside_maxNorm_equality_allOnes`;
5. `NumStability.ch6aside_maxNorm_not_consistent`; and
6. `NumStability.ch6aside_maxNorm_not_consistent._proof_1_1`
   (theorem/internal).

The owner has five public and one internal theorem.

### `Source.Higham.Chapter06.BlockAntidiagonalNorm.OperatorTwo` -- 3 constants

This leaf receives the older operator-2 reduction from `Higham6Asides`:

1. `NumStability.ch6aside_blockAntidiag_hermitian`;
2. `NumStability.ch6aside_blockAntidiag_sq`; and
3. `NumStability.ch6aside_blockAntidiag_op2_eq`.

All three are public theorems. The last has the second and only other
cross-leaf body dependency in the partition, again on
`NumStability.ch6aside_op2_eq_l2` in `Asides.UnitaryInvariance`.

### `Source.Higham.Chapter06.BlockAntidiagonalNorm.InducedLp` -- 18 constants

This leaf receives all of `Analysis.Higham6BlockAntidiag` and proves the full
finite-conjugate-exponent identity:

1. `NumStability.ch6aside_withLpBlockSwapCLM` (definition/public);
2. `NumStability.ch6aside_withLpBlockSwapCLM._proof_1` (theorem/internal);
3. `NumStability.ch6aside_withLpBlockSwapCLM._proof_2` (theorem/internal);
4. `NumStability.ch6aside_withLpBlockSwapCLM._proof_3` (theorem/internal);
5. `NumStability.ch6aside_withLpBlockSwapCLM_apply`;
6. `_private.NumStability.Analysis.Higham6BlockAntidiag.0.NumStability.ch6aside_withLpBlockSwapCLM_bound`
   (theorem/private; expected target private name recorded below);
7. `NumStability.ch6aside_withLpBlockSwapCLM_norm`;
8. `NumStability.ch6aside_matrixLpCLM` (definition/public);
9. `NumStability.ch6aside_matrixLpCLM._proof_1` (theorem/internal);
10. `NumStability.ch6aside_matrixLpCLM._proof_2` (theorem/internal);
11. `NumStability.ch6aside_matrixLpCLM._proof_3` (theorem/internal);
12. `NumStability.ch6aside_matrixLpCLM_apply`;
13. `NumStability.ch6aside_matrixLpCLM_isComplexMatrixLpNormValue`;
14. `NumStability.ch6aside_matrixLpCLM_norm_eq`;
15. `NumStability.ch6aside_blockAntidiagLpCLM` (definition/public);
16. `NumStability.ch6aside_blockAntidiagLpCLM.eq_1` (theorem/internal);
17. `NumStability.ch6aside_blockAntidiagLpCLM_components`; and
18. `NumStability.ch6aside_blockAntidiag_lp_eq`.

The owner has three public definitions, seven public theorems, seven internal
theorems, and one private theorem.

### `Source.Higham.Chapter06.Equation02` -- 3 constants

This leaf receives all of `Analysis.HighamChapter6Duality` in source order:

1. `NumStability.higham6_dual_of_dual_norm_eq_original`;
2. `NumStability.HighamDoubleDualEvaluationSet` (definition/public); and
3. `NumStability.higham6_doubleDualEvaluation_isGreatest`.

It has one public definition and two public theorems.

## Why `Higham6Asides` is split

The historical file is only 601 lines, so size alone would not justify a
split. Its source and graph, however, expose six independent semantic seams:

- lines 35--73: the p. 105 Euclidean-norm differentiability discrepancy;
- lines 75--198: equality prose for numbered equation (6.1);
- line 205 and lines 220--319: the multiplication adapter and
  condition-number bounds;
- lines 215 and 321--436: the operator-2 adapter and unitary invariance;
- lines 438--524: max-norm inconsistency and sharpness; and
- lines 526--599: the operator-2 block-antidiagonal reduction.

The first, second, fifth, and sixth topics have no declaration dependency on
one another. Only the shared `ch6aside_op2_eq_l2` theorem connects the unitary
leaf to `ConditionNumberBounds` and `BlockAntidiagonalNorm.OperatorTwo`.
There is no outside compiled consumer of any of the 28 constants. Keeping all
six topics in a canonical `Asides` implementation leaf would therefore encode
historical accretion rather than source locator or mathematical ownership.

The canonical `Chapter06.Asides` module is instead a declaration-free
historical-surface aggregate. Its documented completeness contract imports its
four physical children plus the two independently located pieces that were
published by the old file:

```text
Asides.ConditionNumberBounds
Asides.EuclideanNormDifferentiability
Asides.MaxNormInconsistency
Asides.UnitaryInvariance
BlockAntidiagonalNorm.OperatorTwo
Equation01
```

This deliberate cross-directory aggregate is the exact 28-constant canonical
target of the historical `Analysis.Higham6Asides` wrapper. It is not a naming
precedent for new declaration-bearing modules.

The block-antidiagonal family is also kept in two leaves. Combining the three
operator-2 constants with the 18 induced-`Lp` constants would make each old
wrapper re-export declarations formerly owned only by the other historical
path. The split preserves both old import closures while presenting one
canonical `BlockAntidiagonalNorm` discovery aggregate.

## Source/reusable boundary decision

No constant in this 69-constant partition remains in, or is newly extracted
to, a reusable owner in Phase 11B2.

Several statements are mathematically generic: the column-norm helpers in
`Lemma06`, the matrix-operation adapters, the general double-dual isometry,
and the `WithLp` off-diagonal continuous-linear-map construction. They still
belong to this bounded source move for three concrete reasons:

1. every published name is explicitly source-shaped (`Lemma66`, `higham6_`,
   `ch6aside_`, or `HighamDoubleDualEvaluationSet`);
2. the generic-looking helpers are proof support for a named Higham result and
   have no outside compiled consumer, except for eight typed edges into five
   `Lemma06` declarations from two other source-shaped, currently unclassified
   Higham correspondence modules; and
3. their reusable foundations already live in the Phase 11B1
   `VectorNorms`, `MatrixNorms`, `SingularValues`, and `OperatorNorms` owners
   (or in Mathlib). Moving these source wrappers into a reusable module would
   pollute that module with provenance names rather than expose new generic
   mathematics.

Consequently the audit found no reusable declaration that must be withheld
from the source tree. A future declaration-renaming API extraction, if users
need one of these helpers independently, is a separate migration and must not
be combined with this ownership-only batch.

## Exact declaration-dependency DAG

The four historical owners form an edgeless induced owner DAG: none imports a
compiled declaration from another one of the four. Splitting the historical
Asides owner creates exactly two cross-leaf body edges and no cross-leaf
signature edge:

```text
Asides.ConditionNumberBounds
  -> Asides.UnitaryInvariance

BlockAntidiagonalNorm.OperatorTwo
  -> Asides.UnitaryInvariance
```

The exact edge witnesses are:

- `ch6aside_op2_mul_le -> ch6aside_op2_eq_l2`; and
- `ch6aside_blockAntidiag_op2_eq -> ch6aside_op2_eq_l2`.

Every other candidate leaf is isolated from the other candidate leaves. The
compiled project-owner dependency sets are:

| Target leaf | Reusable declaration owners used | Candidate source owner used |
| --- | --- | --- |
| `Lemma06` | `MatrixNorms.Basic`, `MatrixNorms.Comparisons`, `SingularValues.Basic`, `VectorNorms.Basic` | none |
| `Asides.EuclideanNormDifferentiability` | none | none |
| `Equation01` | `VectorNorms.Basic` | none |
| `Asides.UnitaryInvariance` | `MatrixNorms.Basic`, `SingularValues.Basic` | none |
| `Asides.ConditionNumberBounds` | `MatrixNorms.Basic`, `SingularValues.Basic` | `Asides.UnitaryInvariance` |
| `Asides.MaxNormInconsistency` | `MatrixNorms.Basic`, `SingularValues.Basic` | none |
| `BlockAntidiagonalNorm.OperatorTwo` | `MatrixNorms.Basic`, `SingularValues.Basic` | `Asides.UnitaryInvariance` |
| `BlockAntidiagonalNorm.InducedLp` | `MatrixNorms.Basic`, `MatrixNorms.Comparisons`, `MatrixNorms.Lp`, `OperatorNorms.Basic`, `VectorNorms.Basic` | none |
| `Equation02` | `VectorNorms.Basic`, `VectorNorms.Duality` | none |

These are declaration-owner edges, not a license for broad aggregate imports.
Each leaf must be isolated and given the narrow direct Mathlib/project imports
needed to elaborate it. No candidate leaf may import `Analysis.Norms.Core`,
`Analysis.Norms`, `Source.Higham.Chapter06`, `Chapter06.Asides`,
`Chapter06.BlockAntidiagonalNorm`, or `Chapter06.Norms`.

There are exactly eight incoming typed edges from outside the partition: one
signature and seven body/proof edges. All target `Lemma06`; none targets any of
the other 49 constants. They are:

- body:
  `Lemma66Op2Bridge.lemma66c_absMatrix_op2_le_sqrt_card ->
  Lemma66.lemma66_c_op2_le`;
- body:
  `Lemma66Op2Bridge.lemma66c_ch14_residual_op2_le_sqrt_card ->
  Lemma66.lemma66_c_op2_le`;
- signature and body:
  `higham19_lemma66_colNorm2_real_eq_columnFrob ->
  Lemma66.lemma66_colNorm2`;
- body:
  `higham19_lemma66_colNorm2_real_eq_columnFrob ->
  Lemma66.lemma66_colNormSq`;
- body:
  `higham19_section19_7_lemma66_residual_bridge ->
  Lemma66.lemma66_a_abs_entry_le`;
- body:
  `higham19_section19_7_lemma66_residual_bridge ->
  Lemma66.lemma66_colNorm1`; and
- body:
  `higham19_section19_7_lemma66_residual_bridge ->
  Lemma66.lemma66_colNorm2`.

The two external declaration owners are
`Algorithms.Ch10Ch14Lemma66Op2Bridge` and
`Algorithms.QR.Higham19Theorem5SourceClosure`. Both are source-shaped
historical correspondence modules, not classified reusable entry points.
They retarget directly to canonical `Source.Higham.Chapter06.Lemma06`.
The post-migration source-boundary checker must still prove that no classified
reusable entry point reaches any new source leaf.

## Aggregate and compatibility contracts

`Source.Higham.Chapter06.Norms` is frozen and remains exactly the Phase 11B1
five-import aggregate over Problems 6.1, 6.5, 6.9, and 6.10 and Theorem 6.4.
None of the 69 Phase 11B2 declarations is added to it. This is required to
keep the historical `Analysis.Norms` compatibility facade from silently
gaining source declarations that it never exposed.

The declaration-free `Source.Higham.Chapter06.BlockAntidiagonalNorm`
aggregate imports, in sorted order:

```text
BlockAntidiagonalNorm.InducedLp
BlockAntidiagonalNorm.OperatorTwo
```

The declaration-free root `Source.Higham.Chapter06` aggregate imports, in
sorted order:

```text
Chapter06.Asides
Chapter06.BlockAntidiagonalNorm
Chapter06.Equation02
Chapter06.Lemma06
Chapter06.Norms
```

`Equation01` and `BlockAntidiagonalNorm.OperatorTwo` are reached through the
documented `Asides` historical-surface aggregate. `InducedLp` is reached
through the block family. The root remains an incremental aggregate over all
canonical Chapter 6 descendants, not a claim that the book chapter has no
unformalized prose.

The four historical paths become exact, declaration-free, one-target wrappers:

| Historical path | Canonical target |
| --- | --- |
| `NumStability.Algorithms.Chapter06Lemma66` | `NumStability.Source.Higham.Chapter06.Lemma06` |
| `NumStability.Analysis.Higham6Asides` | `NumStability.Source.Higham.Chapter06.Asides` |
| `NumStability.Analysis.Higham6BlockAntidiag` | `NumStability.Source.Higham.Chapter06.BlockAntidiagonalNorm.InducedLp` |
| `NumStability.Analysis.HighamChapter6Duality` | `NumStability.Source.Higham.Chapter06.Equation02` |

This raises the compatibility inventory from 104 wrappers/204 direct targets
to exactly 108 wrappers/208 direct targets. A wrapper contains only a module
docstring and its one documented import. It must not contain declarations,
opens, scoped opens, variables, local instances, options, or unrelated
imports.

Production retargets are bounded as follows:

- `Algorithms.Ch10Ch14Lemma66Op2Bridge` and
  `Algorithms.QR.Higham19Theorem5SourceClosure` import `Lemma06` directly;
- the historical `Algorithms` aggregate replaces its three old imports with
  canonical `Lemma06`, `Asides`, and `BlockAntidiagonalNorm`, preserving the
  same union of declarations without importing `Equation02`;
- the `Analysis` aggregate removes its three historical Analysis imports. Its
  existing canonical `Source.Higham.Chapter06` import supplies their
  replacements, including `Equation02`; and
- no other production module imports one of the four historical paths.

The dedicated historical `Analysis.Norms` facade and its two targets are
unchanged. No declaration-bearing production module may import any of the
four new wrappers.

## Exact graph preservation

The normalized Phase 11B1-to-11B2 declaration and dependency comparison must
be empty in both directions. For every one of the 69 constants, the new owner
normalizes to the exact historical owner recorded in this map. Public and
internal logical names are byte-identical.

The three private constants require only these exact name rewrites; no broad
private-prefix rule is permitted:

```text
_private.NumStability.Source.Higham.Chapter06.Asides.UnitaryInvariance.0.NumStability.ch6aside_l2_one
  -> _private.NumStability.Analysis.Higham6Asides.0.NumStability.ch6aside_l2_one

_private.NumStability.Source.Higham.Chapter06.Asides.UnitaryInvariance.0.NumStability.ch6aside_l2_unitary
  -> _private.NumStability.Analysis.Higham6Asides.0.NumStability.ch6aside_l2_unitary

_private.NumStability.Source.Higham.Chapter06.BlockAntidiagonalNorm.InducedLp.0.NumStability.ch6aside_withLpBlockSwapCLM_bound
  -> _private.NumStability.Analysis.Higham6BlockAntidiag.0.NumStability.ch6aside_withLpBlockSwapCLM_bound
```

The normalization applies to declaration rows and to both endpoints of every
signature and body/proof edge. It must reproduce the frozen 69-row partition,
the typed incident stream, and the internal stream hashes above. The expected
global graph remains exactly 81,950 declarations, 305,425 signature edges,
439,195 body/proof edges, and 491,557 union edges. No generated helper may be
added, lost, or reassigned; aggregate and wrapper modules own zero constants.

## Tests, manifests, and structural forecast

Canonical one-import smoke tests are required for all nine declaration leaves
and both new aggregates. In particular, the `Asides` test checks
representatives from all six pieces in its historical-surface contract, and
the `BlockAntidiagonalNorm` test checks both operator-2 and induced-`Lp`
results. Each leaf test imports only that leaf.

Four distinct old-only tests import exactly one historical wrapper apiece and
check representative declarations from its frozen old surface. The Asides
old-only test checks all six semantic seams, while the block old-only test
checks only induced-`Lp` declarations. Canonical and historical tests must not
receive the same declarations through an unrelated aggregate.

The existing Chapter 6 aggregate smoke is extended to representatives from
`Norms`, `Asides`, `BlockAntidiagonalNorm`, `Equation02`, and `Lemma06`.
The existing `Chapter06.Norms` and historical `Analysis.Norms` tests retain
their Phase 11B1 representative set and are not expanded with these 69
declarations. Affected `Algorithms`, `Analysis`, `Source.Higham`, `Higham`,
`SourceCanonical`, `SourceMigration`, `Source`, `All`, root, and
`examples/LibraryLookup.lean` surfaces gain only the representatives that
their documented reachability contracts promise.

The tier manifest records the nine declaration leaves as `source`, the two
new family modules as `aggregate`, and the four historical paths as
`compatibility`. It removes all four historical paths from unclassified and
legacy-naming exception sets. The layout aggregate contract adds `Asides` and
`BlockAntidiagonalNorm`; the compatibility policy adds the four one-target
rows above.

The bounded structural forecast is:

| Measure | Phase 11B1 | Phase 11B2 forecast |
| --- | ---: | ---: |
| Production modules | 1,024 | 1,035 |
| Classified modules | 416 | 431 |
| Classification coverage | 40.625% | 41.643% |
| Unclassified modules | 608 | 604 |
| Aggregate modules | 85 | 87 |
| Compatibility modules | 104 | 108 |
| Reusable modules | 78 | 78 |
| Source modules | 142 | 151 |
| Internal modules | 2 | 2 |
| Upstream modules | 5 | 5 |
| Mixed modules | 0 | 0 |
| Compatibility wrappers | 104 | 108 |
| Compatibility direct targets | 204 | 208 |
| Missing module docs | 217 | 217 |
| Legacy naming exceptions | 403 | 399 |

Direct-import totals are intentionally generated after isolated compilation
and import minimization. The declaration partition, compatibility counts,
module-role counts, and exception reduction above are frozen; any structural
forecast deviation must be explained in the final evidence rather than hidden
with unrelated cleanup.

## Live documentation contract

The implementation updates only current navigation and policy documents that
describe the moved surface: `README.md`, `ARCHITECTURE.md`,
`docs/LIBRARY_LOOKUP.md`, `docs/architecture/TIERS.md`,
`docs/architecture/COMPATIBILITY.md`,
`docs/architecture/reviews/ENDPOINTS.md`,
`docs/architecture/reviews/OUTLIERS.md`, and
`docs/source_coverage/higham_ch06.md`, plus the executable tier/layout
manifests and relevant import tests. Dated baselines, Phase 11A and 11B1 maps,
and historical audit reports remain immutable.

Every new declaration-bearing module receives a module docstring that states
its Higham page/equation/lemma provenance, exact mathematical scope, and main
declarations. Both aggregates and all four wrappers receive explicit
declaration-free completeness/compatibility docstrings.

## Validation gates

Phase 11B2 is complete only after all of the following pass:

1. every one of the nine canonical leaves and both aggregates builds in DAG
   order and in isolation;
2. the four historical wrappers compile in genuinely isolated old-only tests;
3. both declaration consumers, the `Algorithms` and `Analysis` aggregates,
   and all affected root/source entry points build;
4. the 69-row ownership map, private-name rewrites, exact incident/internal
   payloads, and normalized full declaration graph reproduce this frozen map;
5. `Chapter06.Norms` and `Analysis.Norms` retain their Phase 11B1 surface and
   no production declaration-bearing module imports an old path;
6. layout, compatibility, provenance, source-boundary, aggregate-ordering,
   placeholder, exact-debt, and strict-source reproducibility checks pass;
7. `git diff --check`, `lake build NumStability`, `lake test`, and
   `lake build NumStability NumStabilityTest` pass sequentially;
8. `lake env lean examples/LibraryLookup.lean` passes;
9. representative `#print axioms` checks do not exceed
   `[propext, Classical.choice, Quot.sound]`;
10. no `sorry`, `admit`, or new top-level `axiom`/`constant` command is
    introduced;
11. independent source, consumer/test, manifest, documentation, and frozen
    full-diff reviews report no unresolved finding; and
12. full gates are repeated from a clean implementation commit before baseline
    and final evidence commits.

## Bounded exclusions and next phase

Phase 11B2 does not rename declarations or namespaces, create generic aliases,
remove compatibility wrappers, change the historical `Analysis.Norms` surface,
rewrite proofs, adopt a new Lean module-system dialect, or reorganize any
Chapter 10, 14, 19, or 20 consumer beyond its direct import retarget.

After this phase passes, the Chapter 6 historical source-tail promise is
complete. The repository then proceeds, in the already documented strict
order, to the semantic split of `Algorithms.LinearSystems.LU.BlockLU`. That
next phase requires its own committed pre-edit map and may not absorb deferred
Chapter 6 cleanup.
