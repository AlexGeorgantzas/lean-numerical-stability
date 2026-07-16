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
| (26.1)-(26.3) | `IsGlobalMax`, `DirectSearchSpec`, `adConverged`, `mdsRelativeSize`, `mdsConverged` | exact objective and stopping specifications |
| (26.4) | `inverseResidualStabilityMeasure` | exact maximum-row-sum residual definition |
| (26.5)-(26.6) | `depressedCubic_identity`, `cubicWCubePlus_quadratic`, `cubicWCubeMinus_quadratic`, `stableCubicWCube_quadratic` | end-to-end exact cubic algebra |
| (26.7) | `monicCubic`, `cubicRootResidualMeasure` | exact residual objective only; no empirical accuracy claim |
| Section 26.4 | `RealInterval` operations and `*_contains` theorems | exact endpoint definitions and set-soundness for `+,-,*,/` |
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

## Exclusions

Historical MATLAB matrices, decimal outputs, figures, iteration counts, and
machine observations are `SKIP-EMPIRICAL`. AD/MDS/Nelder-Mead implementations
and estimator comparisons are benchmark candidates. The cited pattern-search
convergence sentence and (26.8) are deferred because the printed statements omit
the technical conditions or a semantics for "to first order". Problems
26.1-26.4, including Appendix solution 26.2, were not selected.

## Verification

- Target build: `lake build LeanFpAnalysis.FP.Algorithms.AutomaticErrorAnalysis.Higham26` - PASS.
- Hygiene scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` - PASS (no matches).
- Representative `#print axioms` checks report only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Documentation

- Inventory: `docs/chapter26/CHAPTER26_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter26/CHAPTER26_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter26/CHAPTER26_PROOF_SOURCE_LEDGER.md`
