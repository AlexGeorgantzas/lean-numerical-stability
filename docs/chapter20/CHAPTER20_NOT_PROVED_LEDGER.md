# Chapter 20 Not-Proved Ledger

## Gate

The Chapter 20 core selected-scope gate is **PASS** after the fresh 2026-07-19
actual-trace audit and repair. There are no open selected-scope rows.

The authoritative row-by-row accounting is
`docs/chapter20/CHAPTER20_SOURCE_INVENTORY.md`.

## Open selected-scope rows

None.

## Closed during the 2026-07-19 actual-trace repair

- `higham20_7_sourceConstructed_actual_closed` in
  `Higham20Theorem20_7ActualBackSub.lean` closes Theorem 20.7 for the literal
  rounded pivoted stored-QR, paired RHS transformation, and `fl_backSub`
  execution. It constructs the back-substitution perturbation `dR`, proves the
  actual returned source-coordinate vector is an exact minimizer for the
  perturbed data, and proves both printed uniform source-order `n^2` envelopes.
- The proof derives the completed pivot-row bound, raw-vector and prefix-row
  growth estimates, literal matrix/RHS compact-operation budgets, the direct
  `Q Delta R` multiplier estimate, and the source-coordinate permutation
  transport from the execution. None of these appear as readiness, policy,
  residual, target-bound, or component-budget premises of the final theorem.
- One common explicit nonnegative coefficient,
  `sourceConstructedPivotedStoredQRFinalGammaTilde fp m`, is used for both
  perturbations and depends only on the floating-point model and `m`, as the
  printed hidden dimension-only coefficient requires.
- Nonzero computed diagonal remains a visible algorithm-domain premise. This
  is necessary rather than target-bearing: `breakdownCounter_no_roundedRowPolicy`
  proves that source full rank plus bare `gammaValid` does not imply computed
  nonbreakdown.

## Audited source boundaries that do not fail the gate

- Theorems 20.1 and 20.2 print qualitative approximate-attainability remarks
  by citation. Their exact inequalities are selected and proved; the
  qualitative remarks are attribution-only rather than invented theorems.
- Equation (20.14), the rough corrected-seminormal forward bound, and the
  mixed-precision statements with unspecified `c_mn`/`lesssim` are deferred
  under `DEFER-MISSING-PRECISE-STATEMENT`.
- The p. 396 sentence after Theorem 20.8 describes only which condition numbers
  an analogous residual bound would depend on; it supplies no inequality,
  coefficients, norm choice, or remainder and is therefore deferred under
  `DEFER-MISSING-PRECISE-STATEMENT`.
- The p. 386 MGS paragraph is qualitative attribution-only prose, and optional
  Problem/Appendix 20.5 uses an unspecified `c_{m,n} u` coefficient. They are
  inventoried but do not create a selected core proof obligation.
- The p. 402 arbitrary-equal-rank Wedin extension is false as printed. A local
  exact rational counterexample records the source discrepancy; it is not an
  impossible proof obligation.
- The p. 404 invariance sentence is also false over the chapter's square edge.
  `higham20_p404_square_source_discrepancy` proves this exactly for
  `A = [1]`, `b = [3]`, `y = [1]`, and `theta = 1`: ordinary error is at most
  `1`, whereas strengthened minimum-norm error is at least `sqrt 2`. The cited
  Sun result is strict-tall and matrix-only, so the unqualified square-or-tall
  sentence is closed as a source discrepancy rather than retained as an
  impossible proof obligation.
- Historical MATLAB tables, experimental observations, operation counts,
  software catalogues, and qualitative comparisons are excluded or deferred
  with explicit reasons in the source inventory.
- Optional Problems 20.4, 20.6, 20.8, 20.12, and 20.13 remain outside core
  mode. Their Appendix/research status is recorded individually.

## Closed during the 2026-07-16 Split 4 repair

- `Higham20RowSorting.exactPrinted_iSup_max_alpha_beta_le_cap_of_source_injective` closes the p. 395
  row-sorting cap for the executable decreasing source-row infinity-norm
  permutation and the actual exact active-max signed-Householder matrix/RHS
  trace. Ordinary source full column rank is proved to preserve injectivity
  through row/column permutations and the exact factorization, hence every
  pivot norm is positive; the theorem then returns the literal finite `max_i`.
  `exactPrintedPhi_eq_qrCertificate` identifies the literal stagewise `phi`
  with its completed `Q^T b`/`R` certificate, and
  `exactPrintedPhi_independent_of_row_ordering` proves that simultaneous row
  permutation transports the orthogonal QR certificate and leaves the scalar
  exactly unchanged.

- `LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_theorem20_4_printed_total_perturbations`
  closes Theorem 20.4 by preserving the exact QR relation, transporting both
  triangular-solve perturbations, normalizing their summed nonnegative witness
  once, and proving the printed matrix/RHS envelopes with an explicit
  dimension-only `gammaTilde`.
- `fl_pivotedStoredQR_returnedX_pivotPosition_of_roundedCoxHigham` closes only
  the historical conditional assembly from forward-row/component-budget
  packages. It remains useful infrastructure but is superseded as gate
  evidence by the 2026-07-19 actual producer above.
- The 2026-07-18 bounded repair proved nonnegativity of both literal local
  budget families, a finite a-posteriori direct-multiplier envelope, and the
  exact full-rank rounded-breakdown counterexample. Its then-current conclusion
  that the actual producer was still missing is historical and is superseded
  by `higham20_7_sourceConstructed_actual_closed`.
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
- A computed-Gram or accumulated-polar MGS coefficient is retained under its
  exact local assumptions and is not relabeled as the Appendix's suppressed
  `c_{m,n} u` constant.
- `FPModel.exactWithUnitRoundoff` is not evidence about a rounded source
  algorithm.
- A conditional transfer theorem remains `PARTIAL` whenever its assumptions
  merely restate an accumulated perturbation, minimizer, or target bound. The
  older Theorem 20.7 conditional assembler is therefore not closure evidence;
  the new actual-trace endpoint proves its numerical estimates directly. The
  conditional `PivotedStoredQRCoxHighamRowSortingCaps` is likewise not used as
  evidence for row 27; the independent executable producer and invariance proof
  are in `Higham20RowSorting.lean`.
