# Chapter 20 Not-Proved Ledger

## Gate

The Chapter 20 core selected-scope gate is **FAIL** as of 2026-07-16. The
repository contains substantial exact and implementation-facing Chapter 20
mathematics, but the rows below still lack the literal source conclusion,
constant, construction, remainder, or boundary generality. A conservative
runtime certificate does not close a sharper printed source row.

The authoritative row-by-row accounting is
`docs/chapter20/CHAPTER20_SOURCE_INVENTORY.md`.

## Open selected-scope rows

| Priority | Source row | Current Lean status | Exact missing foundation | Next theorem or construction |
|---|---|---|---|---|
| P0 | Theorem 20.4, pp. 389-390 | `...theorem20_4_source_fullRank_computed_nonbreakdown_total_perturbations` packages the actual totals `DeltaA_i := DeltaA + Q[DeltaR_i;0]`, exact systems, and `|DeltaA_i| <= C (G_i |A|) + |Q[DeltaR_i;0]|`. | The printed theorem absorbs the transported triangular term into a single nonnegative Frobenius-unit witness: `|DeltaA_i| <= C (G_i' |A|)`. | Prove a source-derived lift-domination/absorption lemma using the QR relation and `|DeltaR_i| <= gamma_n |R|`, without increasing the printed dimension-only budget or assuming the target bound. |
| P0 | Equation (20.16) and the preceding p. 390 refinement inequalities | `higham20_eq20_16_actual_householderQR_one_refinement_finite` gives a finite implementation majorant. | The displayed first-order terms and a proved `O(u^2)` remainder tied to the total Theorem 20.4 perturbations are not exposed. | Derive the source residual inequality and its simplifications, then state the displayed linear coefficient plus an explicit quadratic remainder. |
| P0 | Theorem 20.7 and the row-sorting prose, p. 395 | The literal pivoted QR/RHS/back-substitution execution has an exact runtime certificate using accumulated local residual and final top-`R` scales. Conditional producers expose the printed symbols. | No unconditional producer derives the printed `alpha_i`, `beta_i`, and `phi`, the pivot-position `j^2 gamma_tilde_m` bound, and the source-row `n^2` envelope from the rounded algorithm. The current runtime scales are different objects. | Complete the Chapter 19 composite-permutation invariant and the Cox--Higham per-stage component/row-policy bounds, then instantiate `PivotedStoredQRCoxHighamRowPolicy` and `PivotedStoredQRCoxHighamComponentBudgets`. |
| P0 | MGS stability prose, p. 386; Problem/Appendix 20.5 | Literal rounded MGS, accumulated-polar repair, computed-Gram repair, and the Chapter 20 minimizer transfer are formalized. | The printed condition-number-independent columnwise `c3*u` coefficient is not derived; current coefficients depend on runtime Gram/local-error data and positive-pivot conditions. | Prove the Chapter 19.13 global MGS repair with a dimension-only `c3`, then feed it to the existing Appendix 20.5 transfer. |
| P1 | Precise prose around (20.14), (20.16), and p. 396 | Exact algorithms and several finite bounds exist. | Separate source rows for the squared-condition normal-equations forward-error claim, the p. 391 mixed-precision refinement claim, the analogous `Delta r` first-order shape, and the structured componentwise backward-error setup are not closed at their printed strengths. | Add source-facing statements only where the source supplies precise constants/quantifiers; keep `c_mn`, `lesssim`, and qualitative language deferred. |

## Audited source boundaries that do not fail the gate

- Theorems 20.1 and 20.2 print qualitative approximate-attainability remarks
  by citation. Their exact inequalities are selected and proved; the
  qualitative remarks are attribution-only rather than invented theorems.
- Equation (20.14), the rough corrected-seminormal forward bound, and the
  mixed-precision statements with unspecified `c_mn`/`lesssim` are deferred
  under `DEFER-MISSING-PRECISE-STATEMENT`.
- The p. 402 arbitrary-equal-rank Wedin extension is false as printed. A local
  exact rational counterexample records the source discrepancy; it is not an
  impossible proof obligation.
- Historical MATLAB tables, experimental observations, operation counts,
  software catalogues, and qualitative comparisons are excluded or deferred
  with explicit reasons in the source inventory.
- Optional Problems 20.4, 20.6, 20.8, 20.12, and 20.13 remain outside core
  mode. Their Appendix/research status is recorded individually.

## Closed during the 2026-07-16 Split 4 repair

- `GeneralizedQRFactorization.exists_theorem20_9_exact_householder` proves
  unconditional Theorem 20.9 existence for arbitrary source dimensions
  `m + p >= n >= p`; rank assumptions are used only for the theorem's separate
  nonsingularity equivalence.
- `higham20CrossProductExample_symbolic_family` replaces a single fixed
  witness with the printed symbolic `0 < epsilon < sqrt(u)` family and proves
  that the actual modeled rounded Gram matrix is all ones and singular.
- `higham20_fullColumn_range_projector_complement_complexMatrixOp2_eq_min_one_sub`
  proves the exact prose identity
  `||I - A A^+||_2 = min {1, m - n}`, including square and genuinely tall
  cases.
- `Theorem20_10.computedX_emptyConstraints_partA_mixed_stability` and
  `computedX_emptyConstraints_partB_backward_error` prove the genuine rounded
  `p=0,q>0` boundary and derive computed-`R` nonbreakdown from source rank and
  an explicit unit-roundoff threshold.
- `Theorem20_10.computedX_fullConstraints_partA_mixed_stability` and
  `computedX_fullConstraints_partB_backward_error` close the genuine rounded
  `q=0,p>0` constraint-only boundary, deriving computed-`S` nonbreakdown and
  perturbation/rank preservation from the printed rank assumptions and an
  explicit threshold.
- `Higham20EliminationActual.lseEliminationActualReturnedSolution_isLSEMinimizer` closes the p. 399
  elimination algorithm by constructing the reduced exact pivoted QR/top solve
  and the final original-coordinate returned vector; no reduced-minimizer
  premise remains.
- `theorem20_5_wks_finite_formula_and_eigenvalue` and
  `theorem20_5_wks_formula_eigenvalue_and_matrixOnly_limit` remove the
  inappropriate full-row-rank restriction, cover minimizer and nonminimizer
  branches, and compile at the source-general finite/limit API.
- `higham20_problem20_7_scaled_augmented_condition_extremum` closes the full
  positive-`alpha` extremum, balanced minimizer, and maximum-condition witness
  for `n<m`. `higham20_problem20_7_square_scalar_branch_discrepancy` proves
  that the source's unrestricted square-case `sqrt(2)` lower envelope is
  false, so this row is closed as a proved strict-tall result plus a source
  discrepancy rather than by hiding an extra assumption.

## Rejected closure shortcuts

- A hypothesis containing a minimizer, returned vector, final backward error,
  or target-equivalent inequality is not a numerical producer.
- A runtime-derived local-error sum may be useful and exact, but it cannot be
  renamed to the printed `alpha`/`beta`/`phi` compression.
- The Theorem 20.7 `j^2` factor is a pivot-position statement. Original source
  columns use the proved uniform `n^2` envelope unless a permutation theorem
  transports the sharper index.
- A computed-Gram or accumulated-polar MGS coefficient cannot be described as
  the condition-number-independent dimension-only `c3*u` bound.
- `FPModel.exactWithUnitRoundoff` is not evidence about a rounded source
  algorithm.
- A conditional transfer theorem is listed as `PARTIAL` whenever its producer
  assumptions are exactly the source theorem's missing work.
