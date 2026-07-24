# Phase 7: FastMatMul and Higham Chapter 23

Date: 2026-07-24

Execution base: `4362b519c5bec29e0456fcb0a2cbee69924fa84e`

This record is the authoritative pre-edit ownership map for Phase 7. Source
line intervals below are inclusive and refer to the immutable execution base.
Together with the old owner and first/last declaration anchors, each interval
identifies the exact declaration bodies moved by this phase. Declaration names,
types, bodies, visibility, and the namespace `NumStability` are preserved.

## Scope and completion rule

Phase 7 performs two coupled migrations:

1. split the nine explicit declarations in the historical
   `Algorithms.FastMatMul` root into a reusable recurrence leaf and an internal
   legacy-bounds leaf, leaving the root as a complete declaration-free
   aggregate; and
2. split the six source-numbered `Algorithms.FastMatMul.Higham23*` owners into
   semantic `Source.Higham.Chapter23` leaves, leaving import-only compatibility
   wrappers at all six old paths.

The root split is not sufficient on its own. This phase is complete only when
the canonical Chapter 23 entry point exists, no production module imports an
old Chapter 23 path, all wrappers preserve their historical transitive
surfaces, and all manifests and isolated-import tests pass.

## Root declaration extraction

The old root has nine explicit declarations. Structure elaboration and proof
elaboration produce 54 compiled constants: 47 public and seven internal. The
pre/post compiled inventory must preserve all 54.

| New owner | Exact explicit declarations |
| --- | --- |
| `Algorithms.FastMatMul.Recurrences` | `StrassenRecurrence`; `strassen_recurrence_monotone`; `WinogradStrassenRecurrence` |
| `Algorithms.FastMatMul.Internal.LegacyBounds` | `StrassenErrorBound`; `WinogradStrassenErrorBound`; `conventional_componentwise_implies_cubic`; `WinogradInnerProductError`; `BilinearAlgorithmError`; `ThreeMMethodError` |

The historical `Algorithms.FastMatMul` path remains public and imports only
`Internal.LegacyBounds`, `Recurrences`, and canonical
`Source.Higham.Chapter23` after the source migration.

## Chapter 23 source inventory

The six old owners contain exactly 317 public and 20 private explicit
declarations.

| Historical owner | Public | Private |
| --- | ---: | ---: |
| `Algorithms.FastMatMul.Higham23` | 87 | 0 |
| `Algorithms.FastMatMul.Higham23Recursive` | 73 | 5 |
| `Algorithms.FastMatMul.Higham23Remaining` | 72 | 15 |
| `Algorithms.FastMatMul.Higham23Bini` | 49 | 0 |
| `Algorithms.FastMatMul.Higham23ThreeMStrassen` | 26 | 0 |
| `Algorithms.FastMatMul.Higham23Problem23_8` | 10 | 0 |
| **Total** | **317** | **20** |

### Exact old-to-new body map

The counts are public/private explicit declarations. For anonymous instances,
the declaration interval is authoritative even though no source identifier is
available.

| Historical owner | Base lines | Canonical owner | Count | First declaration | Last declaration |
| --- | ---: | --- | ---: | --- | --- |
| `Higham23` | 30--387 | `Chapter23.WinogradInnerProduct` | 5/0 | `higham23_eq23_2_winograd_identity` | `higham23_winograd_componentwise_error` |
| `Higham23` | 389--441 | `Chapter23.BalancedScaling` | 2/0 | `higham23_balanced_sum_sq_le` | `higham23_balanced_winograd_error` |
| `Higham23` | 443--494 | `Chapter23.GammaAsymptotics` | 7/0 | `higham23GammaRemainder` | `higham23_error_bound_gamma_split` |
| `Higham23` | 496--568 | `Chapter23.ConventionalMultiplication` | 5/0 | `higham23FlMatrixMul` | `higham23_eq23_17_conventional_normwise` |
| `Higham23` | 570--722 | `Chapter23.BlockAlgorithms` | 11/0 | `Higham23Block2` | `higham23_eq23_5_strassen_costs` |
| `Higham23` | 724--783 | `Chapter23.BilinearAlgorithm` | 7/0 | `Higham23BilinearAlgorithm` | `higham23_bilinearEvaluate_correct` |
| `Higham23` | 785--1440 | `Chapter23.ThreeM` | 30/0 | `higham23ThreeM` | `higham23_eq23_24_threeM_imaginary_normwise_firstOrder` |
| `Higham23` | 1442--1615 | `Chapter23.ErrorRecurrences` | 20/0 | `higham23StrassenErrorCoefficient` | `higham23_winogradStrassen_error_step` |
| `Higham23Recursive` | 25--139 | `Chapter23.Theorem02.RecursiveMatrix` | 25/1 | anonymous `Zero` instance | `Higham23RecursiveMatrix` and its ring instance |
| `Higham23Recursive` | 142--641 | `Chapter23.Theorem02.ErrorRelations` | 25/0 | `higham23RecursiveFlAdd` | `higham23_recursiveProduct_transfer` |
| `Higham23Recursive` | 644--872 | `Chapter23.Theorem02.ExactMajorant` | 10/0 | `higham23_recursiveFourTermRecombination_error` | `higham23_strassenExactMajorant_nonneg` |
| `Higham23Recursive` | 876--906 | `Chapter23.Theorem02.Execution` | 1/0 | `higham23FlStrassenRecursive` | same |
| `Higham23Recursive` | 909--937 | `Chapter23.Theorem03.Execution` | 1/0 | `higham23FlWinogradStrassenRecursive` | same |
| `Higham23Recursive` | 941--1517 | `Chapter23.Theorem02.ErrorBound` | 11/4 | `higham23_theorem23_2_strassen_exactMajorant` | `higham23_theorem23_2_strassen_closedCoefficient_firstOrder` |
| `Higham23Remaining` | 25--113 | `Chapter23.Theorem03.Certificates` | 5/0 | `Higham23RecursiveCertificate` | `higham23_recursiveCertificate_product` |
| `Higham23Remaining` | 115--794 | `Chapter23.Theorem03.ExactMajorant` | 24/6 | `higham23WinogradN1` | `higham23_theorem23_3_winograd_exactMajorant` |
| `Higham23Remaining` | 796--987 | `Chapter23.Theorem03.ErrorBound` | 9/4 | `higham23WinogradStepResidual` | `higham23_theorem23_3_winograd_closedCoefficient_firstOrder` |
| `Higham23Remaining` | 989--1648 | `Chapter23.Equation11` | 34/5 | `higham23MillerFlatten` | `higham23_eq23_11_miller_normwise` |
| `Higham23Bini` | 23--380 | `Chapter23.BiniLotti.RecursiveAlgebra` | 23/0 | `Higham23BiniMatrix` | `higham23_biniCertificate_product` |
| `Higham23Bini` | 382--438 | `Chapter23.BiniLotti.Execution` | 8/0 | `higham23BiniFlattenBlock` | `higham23BiniExactMajorant` |
| `Higham23Bini` | 440--667 | `Chapter23.BiniLotti.ExactMajorant` | 2/0 | `higham23_biniExactMajorant_nonneg` | `higham23_theorem23_4_biniLotti_exactMajorant` |
| `Higham23Bini` | 669--1030 | `Chapter23.BiniLotti.FirstOrder` | 16/0 | `higham23BiniMajorantFamily` | `higham23_biniLotti_scaledRemainder_isBigO_u_sq` |
| `Higham23ThreeMStrassen` | 25--102 | `Chapter23.ThreeMStrassen.Execution` | 11/0 | `Higham23RecursiveComplex` | `higham23ThreeMStrassenImagMajorant` |
| `Higham23ThreeMStrassen` | 106--252 | `Chapter23.ThreeMStrassen.ExactMajorant` | 1/0 | `higham23_threeMStrassen_exactMajorant` | same |
| `Higham23ThreeMStrassen` | 254--551 | `Chapter23.ThreeMStrassen.FirstOrder` | 14/0 | `higham23ThreeMStrassenRealFamily` | `higham23_threeMStrassen_sourceCoefficient` |
| `Higham23Problem23_8` | 22--189 | `Chapter23.Problem08` | 10/0 | `higham23Problem23_8BlockOne` | `higham23_problem23_8_power_exponent` |

The intervals identify the authoritative declaration bodies and may include
local section scaffolding. Leading declaration doc comments at split seams are
excluded from the preceding interval and assigned to the declaration they
document; they are not part of normalized declaration-body comparison. New
file headers, direct imports, the enclosing namespace, and module docs are not
declaration bodies.

`Problem08` retains the historical Problem 23.8 owner name, while intentionally
co-locating the Problem 23.9 upper-triangular corollary because it is a direct
specialization of the Problem 23.8 block-inverse formula.

### Generated non-public auxiliary audit

The immutable Phase 6 declaration TSV and the Phase 7 declaration TSV were
also compared at the compiled-environment level. The seven former declaration
owners contain 753 compiled constants; the 28 replacement declaration leaves
contain 770. This net increase of 17 is entirely file-split-dependent Lean
equation-compiler and proof elaboration output:

- the public name/kind/visibility multiset is unchanged;
- all 20 source-written `private` declaration blocks are byte-for-byte equal
  after UTF-8/LF normalization;
- 12 old private matcher equation helpers disappear: the `eq_1`, `eq_2`, and
  `splitter` helpers for `Higham23BiniMatrix.match_1`,
  `Higham23RecursiveMatrix.match_1`, and two formerly duplicated owners of
  `higham23RecursiveFlAdd.match_1`;
- 19 private helpers appear: the three matcher equation helpers for each of
  `higham23BiniExactMajorant`, `higham23BiniFirstOrderCoefficient`,
  `higham23StrassenErrorCoefficient`, `higham23FlStrassenRecursive`,
  `higham23StrassenExactMajorant`, and
  `higham23FlWinogradStrassenRecursive`, plus
  `higham23StrassenStepMQuadratic._proof_4`; and
- ten internal helpers appear: matcher implementations for
  `higham23BiniExactMajorant`, `higham23BiniFlEvaluate`,
  `higham23BiniFirstOrderCoefficient`, `higham23StrassenErrorCoefficient`,
  `higham23FlStrassenRecursive`, `higham23StrassenExactMajorant`, and
  `higham23FlWinogradStrassenRecursive`, together with proof auxiliaries for
  `higham23MillerFirstOrderCoefficient`, `higham23StrassenStepMajorant`, and
  `higham23ThreeMStrassenRealFirstOrder`.

The measured delta is therefore seven private and ten internal constants
(nine definitions and eight theorems), with no added or changed public or
source-written private declaration. Generated private ownership prefixes were
normalized only for this auxiliary-name comparison; declaration bodies and
visibility were compared without weakening.

## Canonical hierarchy

The 26 declaration-bearing leaves above are complemented by five sorted,
documented, declaration-free aggregates:

- `Source.Higham.Chapter23`;
- `Source.Higham.Chapter23.Theorem02`;
- `Source.Higham.Chapter23.Theorem03`;
- `Source.Higham.Chapter23.BiniLotti`; and
- `Source.Higham.Chapter23.ThreeMStrassen`.

The Chapter 23 aggregate imports the eight base leaves, the four family
aggregates, `Equation11`, and `Problem08`.

## Direct canonical dependency graph

Every declaration leaf uses canonical direct project imports. No canonical
module imports a compatibility wrapper or the broad `FastMatMul` aggregate.

- `BalancedScaling` imports `WinogradInnerProduct`.
- `ConventionalMultiplication` imports `GammaAsymptotics`.
- `ThreeM` imports `GammaAsymptotics` and `WinogradInnerProduct`.
- `Theorem02.RecursiveMatrix` imports `BlockAlgorithms`.
- `Theorem02.ErrorRelations` imports `Theorem02.RecursiveMatrix`.
- `Theorem02.ExactMajorant` imports `ErrorRelations` and `RecursiveMatrix`.
- `Theorem02.Execution` imports `ConventionalMultiplication`,
  `ErrorRelations`, and `RecursiveMatrix`.
- `Theorem02.ErrorBound` imports `BlockAlgorithms`,
  `ConventionalMultiplication`, `ErrorRecurrences`, `GammaAsymptotics`, and all
  four earlier Theorem02 leaves.
- `Theorem03.Execution` imports `ConventionalMultiplication`,
  `Theorem02.ErrorRelations`, and `Theorem02.RecursiveMatrix`.
- `Theorem03.Certificates` imports the two Theorem02 recursive machinery
  leaves.
- `Theorem03.ExactMajorant` imports `BlockAlgorithms`,
  `ConventionalMultiplication`, the two Theorem02 machinery leaves,
  `Certificates`, and `Execution`.
- `Theorem03.ErrorBound` imports `ErrorRecurrences`, `GammaAsymptotics`, and
  all three earlier Theorem03 leaves.
- `Equation11` imports `BilinearAlgorithm` and `GammaAsymptotics`.
- `BiniLotti.Execution` imports `BilinearAlgorithm`, `Equation11`, and
  `RecursiveAlgebra`.
- `BiniLotti.ExactMajorant` imports the earlier Bini--Lotti leaves,
  `BilinearAlgorithm`, and `Equation11`.
- `BiniLotti.FirstOrder` imports all earlier Bini--Lotti leaves,
  `Equation11`, `ErrorRecurrences`, and `GammaAsymptotics`.
- `ThreeMStrassen.Execution` imports `ThreeM`, `Theorem02.ErrorRelations`, and
  `Theorem02.Execution`.
- `ThreeMStrassen.ExactMajorant` imports `Execution`,
  `Theorem02.ExactMajorant`, and `Theorem02.ErrorBound`.
- `ThreeMStrassen.FirstOrder` imports the earlier 3M--Strassen leaves,
  `ErrorRecurrences`, and the relevant Theorem02 leaves.
- `Problem08` imports `BlockAlgorithms` and `Theorem02.RecursiveMatrix`.

Independent source leaves may additionally import
`Algorithms.FastMatMul.Recurrences` and the reusable algorithm/analysis or
Mathlib modules required by their bodies.

## Exact compatibility surfaces

The six old paths remain import-only wrappers. They deliberately do not all
import the complete Chapter 23 aggregate because that would widen historical
surfaces.

Let `L` denote `Algorithms.FastMatMul.Internal.LegacyBounds`, which preserves
the six legacy-root declarations historically exported by every old Chapter 23
path. Let `H` denote all eight base leaves, `T2` and `T3` the two
theorem-family aggregates, `E3` `Theorem03.Execution`, `E11` `Equation11`,
`BL` the Bini--Lotti aggregate, `TM` the 3M--Strassen aggregate, and `P8`
`Problem08`.

| Historical path | Direct targets |
| --- | --- |
| `Higham23` | `L + H` |
| `Higham23Recursive` | `L + H + T2 + E3` |
| `Higham23Remaining` | `L + H + T2 + T3 + E11` |
| `Higham23Bini` | `L + H + T2 + T3 + E11 + BL` |
| `Higham23ThreeMStrassen` | `L + H + T2 + T3 + E11 + BL + TM` |
| `Higham23Problem23_8` | `L + H + T2 + E3 + P8` |

These rows become six exact `COMPATIBILITY.md` entries. Target paths in the
table and direct imports in each wrapper must match in sorted order.

## Tests

Add and register 40 isolated import tests:

- one direct-import test for each of the 26 canonical declaration leaves;
- one direct-import test for each of the five canonical aggregates;
- six old-only wrapper tests, each checking its owned terminal plus a terminal
  from every predecessor surface in its compatibility row and a retained
  legacy-root declaration;
- `FastMatMulLegacyBounds`, directly checking all six internal compatibility
  declarations;
- `FastMatMulRecurrences`, checking the three reusable explicit declarations;
  and
- `FastMatMulAggregate`, checking all nine historical root names plus a
  terminal from every former `Higham23*` owner.

Update shared Algorithms, All, endpoint, Higham, Root, Source, canonical-source,
and migration smokes. No broad co-import may substitute for an old-only test.

## Manifest and documentation ratchets

- Classify `FastMatMul` and all five new source umbrellas as `aggregate`, the
  recurrence leaf as `reusable`, the legacy leaf as `internal`, and all six old
  paths as `compatibility`. The canonical leaves inherit the `source` prefix.
- Register all six compatibility rows.
- Add complete-aggregate mappings for FastMatMul and the five Chapter 23
  aggregates.
- Remove FastMatMul from the declaration-bearing, missing-doc, and unclassified
  exceptions; remove all six old source paths from unclassified and
  noncanonical exceptions.
- Refresh direct-import ceilings and every reported statistic from measured
  output only.
- Update the README, architecture guide, library lookup, Chapter 23 coverage
  and formalization reports, and baseline index to the canonical entry point.

The expected structural result, subject to measurement, is 931 production
modules, 294 classified, 637 unclassified, 224 missing module docs, 431 naming
exceptions, zero declaration-bearing umbrellas, zero mixed modules, and zero
unsorted aggregates. The measured declaration inventory is 81,950 compiled
declarations: the unchanged 56,187 public declarations, 4,341 private
declarations, and 21,422 internal declarations. The 17-constant non-public
delta is accounted for by the generated-auxiliary audit above.

## Verification gates

Completion requires:

1. normalized name/type/body/visibility comparison for all 54 root constants
   and all 317 public plus 20 source-written private Chapter 23 declarations,
   plus an exact generated-auxiliary inventory explaining the compiled
   non-public delta;
2. canonical-only and old-only targeted builds for every new leaf, aggregate,
   and wrapper;
3. proof that no production file imports any of the six old source paths;
4. proof that all aggregates are sorted, unique, documented, and
   declaration-free;
5. `lake test` and `lake build NumStability NumStabilityTest`;
6. the library lookup example;
7. layout, compatibility, provenance, strict-source, aggregate-order, JSON,
   placeholder, notice-normalization dry-run, and `git diff --check` gates;
8. a generated Phase 7 baseline and a reproducibility comparison; and
9. a clean-checkout build record before the checkpoint is pushed.
