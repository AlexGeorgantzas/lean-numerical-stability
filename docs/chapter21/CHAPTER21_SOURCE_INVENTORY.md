# Higham Chapter 21 Source Inventory

## Audit Basis

- Audit date: 2026-07-18
- Source: `References/1.9780898718027.ch21.pdf`
- Book: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002)
- Chapter: 21, “Underdetermined Systems,” printed pp. 407–414
- Mode: core
- Parallel ownership: Split 4, Chapter 21 only
- Planning documents: parallel blueprint, Split 4 primary contract, and chapter index
- Source inspection: all eight chapter pages were rendered and visually checked

## Counts

This audit separates 27 source rows: 21 selected mathematical or algorithmic
rows and six intentional exclusions. All 21 selected rows pass at source
strength. The selected-scope result is maintained in
`CHAPTER21_NOT_PROVED_LEDGER.md`; exclusions below are not proof gaps.

## Inventory

| # | Source row | Location | Decision / reason | Audit status | Primary Lean evidence |
|---:|---|---|---|---|---|
| 1 | Full-row-rank underdetermined minimum-norm problem | p. 407 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `UnderdeterminedSpec.lean`: `RectMinNormSolution` and canonical Gram pseudoinverse results |
| 2 | Equation (21.1), QR block form of `Aᵀ` | p. 407 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21_eq21_1_qr_transpose_block_mulVec`, `higham21_qr_transpose_system_eq` |
| 3 | Equation (21.2), block coordinate equation | p. 407 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21_eq21_2_qr_block_transpose_coordinates` |
| 4 | Equation (21.3), zero free coordinates and Q method | p. 407 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21_eq21_3_q_method_min_norm_of_qr_upper_diag_ne_zero` and companion lemmas |
| 5 | Equation (21.4), minimum-norm pseudoinverse formula | p. 408 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21_eq21_4_*` family in `UnderdeterminedSpec.lean` |
| 6 | Equation (21.5), seminormal equations | p. 408 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21_eq21_5_qr_sne_gram_eq`, `higham21_eq21_5_sne_rect_transpose_solution` |
| 7 | Theorem 21.1 and equation (21.6) | pp. 408–409 | FORMALIZE_CORE / CORE-NAMED-RESULT and CORE-NUMBERED-EQUATION | PASS | `Higham21Perturbation.lean`; end-to-end radius theorem `higham21_theorem21_1_relative_asymptotic_bound_of_direction_envelope` in `Higham21PerturbationRadius.lean` |
| 8 | Equation (21.7), exact first-order perturbation expansion | p. 409 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21Eq21_7_exact_expansion`, fixed-radius remainder and `IsBigO` theorems |
| 9 | `‖I-A⁺A‖₂ = min{1,n-m}` | p. 409 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `higham21_projector_complement_opNorm2_eq_min_one_sub_of_gram_det_ne_zero` in `Higham21ProjectorNorm.lean` |
| 10 | Equation (21.8), componentwise perturbation specialization | p. 409 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Higham21Eq21_8.lean`, explicit fixed-radius quadratic remainder |
| 11 | Equation (21.9), normwise specialization | p. 409 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `Higham21Eq21_9.lean`, explicit fixed-radius quadratic remainder |
| 12 | Row-scaling invariance of `cond₂` | p. 410 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `higham21Cond2With_row_scaling` in `Higham21Condition.lean` |
| 13 | Lemma 21.2, one-perturbation symmetrization | p. 410 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS | `higham21_lemma21_2_source_bundle` and component lemmas in `UnderdeterminedSolve.lean` |
| 14 | Theorem 21.3, Sun–Sun normwise backward-error formula | pp. 410–411 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS WITH DOCUMENTED SOURCE BOUNDARY CORRECTION | `higham21_theorem21_3_normwise_backward_error_formula`; exact/closure attainment in `Higham21Theorem21_3Attainment.lean` |
| 15 | Theorem 21.3 square specialization | p. 411 | FORMALIZE_CORE / CORE-PRECISE-PROSE | PASS | `higham21_theorem21_3_square_nonzero_etaF_eq_phi` |
| 16 | Row-wise backward-error measure `ωᴿ` and `O(u)` criterion | p. 411 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS (quantitative gamma form) | `Higham21RowwiseMeasure.lean`; the Lean index is correctly `i=1:m`, repairing the printed `i=1:n` typo |
| 17 | Equation (21.10), rounded Q-action formation | p. 411 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21_eq21_10_*` family and Householder gamma wrappers |
| 18 | Theorem 21.4, Householder branch | p. 411 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS | `Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness` derives the complete computed-QR domain from full row rank, gamma validity, and the printed-form smallness condition. It proves top-block nonbreakdown by combining the Chapter 19 rowwise QR perturbation with the Chapter 21 right inverse/rank-stability bridge. `higham21_theorem21_4_computed_qhat_rowwise_backward_stable_source` then applies the actual panel, solve, and Q-action endpoint. |
| 19 | Theorem 21.4, Givens branch | p. 411 | FORMALIZE_CORE / CORE-NAMED-RESULT | PASS | `Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid` derives replay smallness from one operational schedule index; `higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness` derives every computed top diagonal entry nonzero from source rank and QR smallness; `higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable_source` supplies both facts to the concrete retained-trace endpoint. |
| 20 | Equation (21.11), Q method | p. 412 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | Uniform dimension-at-least-two theorem plus `higham21_eq21_11_computed_qhat_relative_forward_error_quadratic_scalar` for the remaining square scalar branch |
| 21 | Equation (21.11), SNE method | p. 412 | FORMALIZE_CORE / CORE-NUMBERED-EQUATION | PASS | `higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq`: actual Householder panel, two rounded triangular solves, and rounded `Aᵀŷ` formation; relative `xhat` versus canonical `x`, the original `cond2(A)` first-order term, and an explicit `fp.u²` remainder with a fixed-radius coefficient depending only on `A`, `b`, the dimensions, and `tau` |
| 22 | SNE has no Theorem-21.4 analogue and no general small-residual guarantee | p. 412 | SKIP / SKIP-QUALITATIVE | EXCLUDED | Negative qualitative warning; no stronger backward-stability or residual theorem is claimed |
| 23 | Corrected reverse MGS recurrence | pp. 412–413 | FORMALIZE_DEPENDENCY / DEP-REQUIRED | PASS | `Higham21MGS.lean`, `Higham21MGSRounded.lean` |
| 24 | Corrected MGS has “essentially” Theorem-21.4 stability | p. 413 | SKIP / SKIP-QUALITATIVE | EXCLUDED | No exact coefficient or theorem surface is printed; conditional extension interfaces are not counted as core closure |
| 25 | Vandermonde experiment and Table 21.1 | p. 413 | SKIP / SKIP-EMPIRICAL | EXCLUDED | Historical condition/orthogonality/backward-error outputs lack a uniquely specified machine execution |
| 26 | LAPACK routine descriptions | p. 414 | SKIP / SKIP-EDITORIAL | EXCLUDED | Implementation catalogue and documentation, not theorem statements |
| 27 | Problem 21.1 and equations (21.12)–(21.14), with Appendix A solution row | p. 414 | SKIP / OPTIONAL-PROBLEM-NOT-SELECTED | EXCLUDED | Optional generalized least-squares/constrained-distance characterization, not selected in core mode |

## Algorithm Object Classification

| Method | Computed objects modeled | Analysis-only objects | Empirical-only objects |
|---|---|---|---|
| Q method, Householder | rounded panel `Q̂`, top `R̂`, rounded triangular solve, rounded Q action | row-wise backward perturbations, exact nearby minimum-norm solution | none |
| Q method, Givens | stored rounded rotations, triangular solve, replayed action | exact replay/factor perturbation witnesses | none |
| SNE | actual Householder panel/top `R̂`, two rounded triangular solves, rounded `Aᵀŷ` formation | QR perturbation, exact economy factor, canonical `x`, signed first-order terms, and source-defined fixed-radius uniform remainder coefficients | none |
| Corrected MGS | rounded recurrence state and local operations | row-scaling/transfer certificates | none |
| Section 21.3 experiment | source does not fully specify a reproducible execution | symbolic algorithms above | all printed decimal results in Table 21.1 |

## Source Corrections And Boundaries

1. The row-wise measure’s printed row index runs to `n`; for an `m × n`
   matrix it must run to `m`. Lean uses the dimension-correct row index.
2. Theorem 21.3’s unconditional printed minimum needs a zero-system boundary
   correction. Lean proves the correct infimum formula, exact attainment under
   the sharp nonzero-pairing condition, and unconditional closure attainment.
3. Theorem 21.4’s lower-level operational surfaces expose computed top-factor
   nonbreakdown and, for Givens, replay smallness. The source-facing producers
   in `Higham21Theorem214SourceClosure.lean` now derive those execution facts:
   Householder and Givens top-block nonsingularity follow from the QR rowwise
   perturbation plus full-row-rank stability, while the actual Givens replay
   recurrence is bounded below one from one operational gamma-validity index.
   They are not assumptions of the final source-facing endpoints.
4. The final SNE relative endpoint exposes `hm`, `hn`, `hdet`, and `hb` as
   source/domain assumptions; `hvalidQR` and `hmGamma` as floating-point
   validity; `hdiag` as triangular nonbreakdown; and `hrho_pos` as positivity
   of the Householder perturbation scale. Its fixed-radius premises require
   `gamma_m + rho ≤ tau < 1`, uniform Gram contraction below one, and
   `tau * higham21SNEQUniformSolveMultiplier A tau ≤ 1/2`. The explicit
   `fp.u²` corollary additionally assumes the standard half-radius bounds
   `(m : ℝ) * fp.u ≤ 1/2` and
   `(m * householderConstructApplyGammaIndex (m+k) : ℝ) * fp.u ≤ 1/2`.
   The resulting quadratic coefficient is source-defined and independent of
   the active QR direction, nearby factors, and rounded normal solution.
