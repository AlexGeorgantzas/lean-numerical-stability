# Higham Chapter 26 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 26, "Automatic Error Analysis", printed pp. 471–487.
- Source file: `References/1.9780898718027.ch26.pdf`.
- Mode / split: core / Split 4.
- Planning documents: full blueprint, Split 4 contract, chapter index.
- Canonical entry point: `NumStability.Source.Higham.Chapter26`.
- Historical compatibility paths:
  `NumStability.Algorithms.AutomaticErrorAnalysis.Higham26` and
  `NumStability.Algorithms.AutomaticErrorAnalysis.Higham26SourceSearch`.
- Selected-scope gate: **PASS**.

The implementation is organized into 23 declaration-bearing canonical leaves
and six documented declaration-free aggregates. The leaves own exactly 141
public declarations and five private proof helpers. The private crude-fold,
ordered-iteration, two regular-simplex sums, and fixed-multiplication-bound
helpers remain atomic with the declarations that use them.

## Completed selected targets

| Source | Lean declarations | Theorem surface |
|---|---|---|
| (26.1)–(26.2) | `IsGlobalMax`, `DirectSearchSpec`, `adConverged` | exact optimization vocabulary and AD stopping predicate; the optional global postcondition is not used to specify an algorithm |
| Sec. 26.2 alternating directions | `ADExactLineSearch`, `ADSearchTrace`, `adRun`, `higham26ADCrudeSearch` and monotonicity results | exact coordinate execution and the finite crude producer printed on p. 475 |
| Sec. 26.2 MDS method / (26.3) | `MDSSimplex`, `reorderBest`, `reflect`, `expand`, `contract`, `iteration`, `IterationSpec`, `SearchTrace`, `Converged` | general simplex transitions and finite execution semantics, including contraction retries and the printed stopping test; no optimizer-correctness or termination assumption |
| Sec. 26.2 initial simplexes | `higham26RightAngledSimplex`, `higham26RegularSimplex` and their geometry theorems | both page 476 constructors and exact edge geometry |
| (26.4) | `inverseResidualStabilityMeasure` | exact maximum-row-sum residual definition |
| (26.5)–(26.6) | depressed/monic cubic identities, real and complex branches, Cardano endpoints, stable branches, and the zero-branch discrepancy | end-to-end exact cubic algebra with the necessary nonzero and real-radicand qualifications exposed |
| (26.7) | `monicCubic`, `cubicRootResidualMeasure` | exact residual objective only; no empirical accuracy claim |
| (26.8) | `linearizedForwardError26_8`, `linearizedForwardError26_8_eq`, `eq26_8_linearized_forward_error`, `eq26_8_exact_of_affine_increment` | explicit finite-dimensional Fréchet-derivative/little-o interpretation and affine exactness; this adds semantics omitted by the terse printed display and is not claimed to be its unique reading |
| Section 26.4 | `RealInterval` operations, containment theorems, and dependency examples | exact endpoint definitions, set-soundness for `+,-,*,/`, and both printed dependency-widening examples |
| Section 26.4 computed endpoints | `outwardRounded`, `outwardAdd/Sub/Mul/Div` and containment theorems | concrete finite-range IEEE directed-rounding enclosure |

## Computed directed-rounding closure

Page 481 states that left endpoints are computed with rounding toward
`-infinity` and right endpoints toward `+infinity`, so the result contains
the corresponding interval operation. `outwardRounded` uses the repository's
`FloatingPointFormat.finiteRoundTowardNegative` and
`finiteRoundTowardPositive` selectors. The four computed operation producers
and their containment theorems close this claim for finite real endpoints. The
explicit endpoint-range evidence excludes only IEEE overflow results, whose
infinities live in the separate `IeeeValue` layer.

## Reuse and assumptions

The canonical leaves reuse `RVec`, `infNorm`, `matMul`, and `idMatrix`
from `Analysis.MatrixAlgebra`, plus Mathlib's real square root, finite sums,
absolute values, and ordered-field lemmas. There are no suspicious assumptions:
the cubic root theorems expose the necessary nonnegative-radicand or nonzero
branch hypotheses, and exact-real interval division exposes `0` not belonging
to the denominator interval. The computed enclosure theorems reuse proved
directed-rounding inequalities rather than adding rounding assumptions.

The MDS transition uses `Finite.exists_max` only to choose the best of the
current `n+1` vertices. Its reflection, expansion, and contraction candidates
are constructed directly from the printed affine formulas, and its branch
tests compare their actual finite objective maxima. `SearchTrace` records the
repeat-until-(26.3) control flow. No theorem assumes that MDS returns a local or
global maximizer, that a limit point is stationary, or that an iteration or run
terminates.

## Exclusions and interpretive boundary

Historical MATLAB matrices, decimal outputs, figures, iteration counts, and
machine observations are `SKIP-EMPIRICAL`. The printed finite crude AD search,
MDS transition, and both printed initial-simplex constructions are encoded.
The unprinted Nelder–Mead transitions and estimator comparisons remain
benchmark candidates. The cited pattern-search convergence sentence remains
deferred because its technical hypotheses are not printed.

Equation (26.8) is no longer listed as unencoded: the repository records the
explicit Fréchet-derivative interpretation described above while preserving
the caveat that Higham does not state those formal semantics. Problems
26.1–26.4, including Appendix solution 26.2, were not selected.

## Verification

- Canonical target build:
  `lake build NumStability.Source.Higham.Chapter26` — PASS.
- Both historical wrapper builds — PASS.
- Isolated imports: 23 declaration-bearing leaves, six declaration-free
  aggregates, and two old-only compatibility smokes — PASS.
- Public declaration ownership: 141 public declarations occur exactly once in
  canonical declaration-bearing leaves; five private helper clusters remain
  with their dependents.
- Hygiene scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` —
  PASS (no matches).
- Representative axiom checks report only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Documentation

- Inventory: `docs/chapter26/CHAPTER26_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter26/CHAPTER26_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter26/CHAPTER26_PROOF_SOURCE_LEDGER.md`
