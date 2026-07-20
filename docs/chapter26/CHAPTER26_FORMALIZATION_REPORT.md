# Higham Chapter 26 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 26, "Automatic Error Analysis", printed pp. 471-487.
- Source file: `References/1.9780898718027.ch26.pdf`.
- Mode / split: core / Split 4.
- Planning documents: full blueprint, Split 4 contract, chapter index.
- Selected-scope gate: **PASS**.

## Completed selected targets

| Source | Lean declarations | Theorem surface |
|---|---|---|
| (26.1)-(26.2) | `IsGlobalMax`, `adConverged` | exact optimization problem and AD stopping predicate; the optional `DirectSearchSpec` global postcondition is not used to specify an algorithm |
| Sec. 26.2 MDS method / (26.3) | `MDSSimplex`, `MDSSimplex.reorderBest`, `reflect`, `expand`, `contract`, `iteration`, `IterationSpec`, `SearchTrace`, `Converged` | actual general simplex transition and finite execution semantics, including contraction retries and the printed stopping test; no optimizer-correctness or termination assumption |
| (26.4) | `inverseResidualStabilityMeasure` | exact maximum-row-sum residual definition |
| (26.5)-(26.6) | `depressedCubic_identity`, `cubicWCubePlus_quadratic`, `cubicWCubeMinus_quadratic`, `stableCubicWCube_quadratic` | end-to-end exact cubic algebra |
| (26.7) | `monicCubic`, `cubicRootResidualMeasure` | exact residual objective only; no empirical accuracy claim |
| Section 26.4 | `RealInterval` operations, `*_contains` theorems, `dependency_sub_example`, `dependency_div_example` | exact endpoint definitions, set-soundness for `+,-,*,/`, and both printed dependency-widening examples |
| Section 26.4 computed endpoints | `outwardRounded`, `outwardAdd/Sub/Mul/Div` and containment theorems | concrete finite-range IEEE directed-rounding enclosure |

## Computed directed-rounding closure

Page 481 also states an implementation-facing theorem: compute left endpoints
with rounding toward `-infinity` and right endpoints toward `+infinity`, so the
result contains the corresponding interval operation. `outwardRounded` now uses
the repository's concrete `FloatingPointFormat.finiteRoundTowardNegative` and
`finiteRoundTowardPositive` selectors. The four computed operation producers
and their containment theorems close this claim for finite real endpoints. The
explicit endpoint-range evidence excludes only IEEE overflow results, whose
infinities live in the repository's separate `IeeeValue` layer rather than in a
finite `RealInterval`.

## Reuse and assumptions

The module reuses `RVec`, `infNorm`, `matMul`, and `idMatrix` from
`FP.Analysis.MatrixAlgebra`, plus Mathlib's real square root, finite sums,
absolute values, and ordered-field lemmas. There are no suspicious assumptions:
the cubic root theorems expose the necessary nonnegative-radicand hypothesis,
and exact-real interval division exposes `0` not belonging to the denominator
interval. The new computed enclosure theorems reuse the repository's proved
directed-rounding inequalities rather than adding rounding assumptions.

The MDS transition uses `Finite.exists_max` only to choose the best of the
current `n+1` vertices. Its reflection, expansion, and contraction candidates
are constructed directly from the printed affine formulas, and its branch
tests compare their actual finite objective maxima. `SearchTrace` records the
repeat-until-(26.3) control flow. No theorem assumes that MDS returns a local or
global maximizer, that a limit point is stationary, or that an iteration or run
terminates.

## Exclusions

Historical MATLAB matrices, decimal outputs, figures, iteration counts, and
machine observations are `SKIP-EMPIRICAL`. The partly specified AD line-search
implementation, the unprinted Nelder--Mead transitions, and estimator
comparisons are benchmark candidates; the printed MDS transition is core and
is encoded. The cited pattern-search convergence sentence and (26.8) are
deferred because the printed statements omit the technical conditions or a
semantics for "to first order". Problems 26.1-26.4, including Appendix solution
26.2, were not selected.

## Verification

- Target build: `lake build NumStability.Algorithms.AutomaticErrorAnalysis.Higham26` - PASS.
- Public import audit: `examples/LibraryLookup.lean` checks `MDSSimplex`, its
  best-vertex ordering theorem, `iteration`, `IterationSpec`, and `SearchTrace`
  and compiles - PASS.
- Hygiene scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` - PASS (no matches).
- `#print axioms MDSSimplex.reorderBest_orderedFor` and the representative
  chapter checks report only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Documentation

- Inventory: `docs/chapter26/CHAPTER26_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter26/CHAPTER26_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter26/CHAPTER26_PROOF_SOURCE_LEDGER.md`
