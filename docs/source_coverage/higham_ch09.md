# Higham Chapter 9 Formalization Report - "LU Factorization and Linear Equations"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 9, "LU Factorization and Linear Equations" (printed pp. 157-193).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch9.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7-12).
- Planning documents consulted: blueprint, Split 2 section of `split_primary_contracts.md`, `chapter_index.md`.
- Selected-scope gate: FAIL (citation-blocked). The primary labels Theorems
  9.1, 9.3-9.5, 9.8-9.10, 9.12-9.14, Lemma 9.6, and Algorithm 9.2 are
  represented by proved source-facing declarations, and the numbered equation
  families (9.1)-(9.27) are accounted for by the chapter surfaces listed below.
  However, four selected rows whose *only* justification in the book is an
  external citation (Higham gives no proof) remain genuinely open and are held
  as honest conditional/partial surfaces rather than closed: the complete-
  pivoting upper bound eq. (9.14) [Wilkinson 1961], the rook-pivoting bound
  eq. (9.16) [Foster 1997], the banded GEPP growth Theorem 9.11 [Bohte 1975],
  and the full normwise/spectral Barrlund-Sun Theorem 9.15 self-majorant/Schur-
  induction step. See the not-proved ledger below. (An earlier revision of this
  file recorded PASS with "no open items"; that overstated the Lean state and
  is corrected here per the project's documentation-honesty rule that a
  citation is not a proof and a conditional transfer does not close a stronger
  source row.)

Primary Lean module: `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean`
(chapter-label surface); reusable LU, triangular solve, growth-factor,
tridiagonal, and special-matrix foundations are imported from the `LU/*` modules
and shared analysis files.

## Completed selected targets (primary labels)
| Source label | Lean declaration(s) | Notes |
|---|---|---|
| Theorem 9.1 (LU existence/uniqueness and pivot foundations) | `higham9_1_*`, `higham9_2_DoolittleLU`, `higham9_2_exactDoolittle_recurrences_to_LUFactSpec`, `higham9_1_lu_unique_of_pivots_ne_zero` | determinant/pivot product, Schur complement, and exact LU interfaces |
| Algorithm 9.2 (Gaussian elimination / Doolittle variants) | `higham9_2_*DenseLoop*`, `higham9_2_*AbsBudget*`, `higham9_2_rectRounded*`, `higham9_2_*Permuted*` | square, rectangular, partial-pivot, and complete-pivot loop certificates |
| Theorem 9.3 (GE backward error) | `higham9_3_lu_backward_error_gamma`, `higham9_3_exactDoolittle_recurrences_backward_error_gamma`, `higham9_3_rectRoundedLoop_backward_error`, `higham9_3_*permuted*backward_error*` | exact and rounded Doolittle backward-error surfaces |
| Theorem 9.4 (LU solve backward error) | `higham9_4_lu_solve_backward_error`, `higham9_4_exactDoolittle_recurrences_lu_solve_backward_error`, `higham9_4_rectRoundedLoop_square_lu_solve_backward_error` | triangular solve handoff |
| Theorem 9.5 (Wilkinson-type solve bound) | `higham9_5_wilkinson_source_bound_of_entry_growth`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace`, plus dense/abs-budget/rounded-loop variants | growth-factor-to-solve-error bridge |
| Lemma 9.6 (growth and reduced-matrix support) | `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero` | no-pivot growth, reduced entries, and total-nonnegative support |
| Theorem 9.8 (complete pivoting lower-bound families) | `higham9_8_growth_factor_ge_theta_real`, `higham9_8_exists_completePivoting_growth_factor_ge_theta_real`, `higham9_8_exists_completePivoting_growth_factor_ge_theta_nonsingInv`, `higham9_8_*checkerboard*`; section-9.4 illustrations: `higham9_12_sineMatrix_theta_candidate_ge_half_succ` (S_n), `higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card` (V_n), `higham9_8_hadamard_theta_candidate_eq_card` / `higham9_8_hadamard_growthFactorEntry_ge_card_of_lu_right_inverse` (Hadamard `rho_n >= n`) | real and checkerboard-conjugate witnesses; the theta = n Hadamard bound applies Theorem 9.8 with alpha = 1, beta = 1/n via the scaled-transpose inverse `higham9_8_hadamardInv` |
| Theorem 9.9 (diagonal dominance) | `higham9_9_colDiagDominant_exists_LUFactSpec_growthFactorEntry_le_two_of_le_two`, `higham9_9_rowDiagDominant_exists_LUFactSpec_growthFactorEntry_le_two_of_le_two`, `higham9_9_*wilkinson_source_bound_exists*` | column/row diagonal dominance and small-dimension endpoint wrappers |
| Theorem 9.10 (Hessenberg matrices) | `higham9_10_hessenberg_growth_backward_error`, `higham9_10_hessenberg_lu_solve_backward_stable_tight`, `higham9_10_HessenbergGEPPUTrace_*` | Hessenberg GEPP structure and solve bound |
| Theorem 9.11 (banded matrices) | `higham9_11_bohteBound*`, `higham9_11_bohte_banded_solve_tight*`, `higham9_11_matrix_bohte_banded_solve_tight*`, `higham9_11_matrix_tridiag_data_bohte_solve_tight*` | Bohte constants, bandwidth-specialized wrappers, and Matrix APIs |
| Theorem 9.12 (special classes with no growth) | `higham9_12_spd_*`, `higham9_12_nonneg_lu_*`, `higham9_12_mmatrix_lu_*`, `higham9_12_sign_equiv_*`, `higham9_12_totalNonnegative_*`, and the `higham9_12_matrix_*` wrappers | SPD tridiagonal, nonnegative LU, M-matrix, sign-equivalent, total-nonnegative, and Matrix-facing surfaces |
| Theorem 9.13 (tridiagonal diagonal dominance) | `higham9_13_colDiagDom_*`, `higham9_13_rowDiagDom_*`, `higham9_13_tridiag_builder_*`, `higham9_13_matrix_colDiagDom_*`, `higham9_13_matrix_rowDiagDom_*` | `rho <= 3` and componentwise growth packages |
| Theorem 9.14 (growth-factor consequences and special solves) | `higham9_14_f`, `higham9_14_h`, `higham9_14_source_*`, `higham9_14_matrix_source_*`, `higham9_14_tridiag_*`, `higham9_14_totalNonnegative_*`, `higham9_14_checkerboard_*` | source `f(u)`/`h(u)` bounds and special-class endpoints |
| Theorem 9.15 (LU sensitivity) | `higham9_15_lu_perturbation_identity`, `higham9_15_lu_perturbation_relative_bound`, `higham9_15_lu_perturbation_forward_bound`, `higham9_15_chi*`, `higham9_15_normalized_G*`, `higham9_15_componentwise_source_firstOrder*` | condition-chain, resolvent, first-order, and componentwise sensitivity APIs |

## Equations
Equations (9.1)-(9.27) are accounted for by the source-facing declaration
families above: pivot/Doolittle and Schur-complement identities (`higham9_1_*`,
`higham9_2_*`), backward-error and solve equations (`higham9_3_*`,
`higham9_4_*`, `higham9_5_*`), block/sine/Fourier and growth-factor witnesses
(`higham9_8_*` through `higham9_13_*`), tridiagonal data and recurrences
(`higham9_18_*`, `higham9_19_*`), source `f(u)`/`h(u)` bounds and model
equations (`higham9_14_*`), and LU sensitivity operators/normalized systems
(`higham9_15_*`).

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| Historical notes, implementation commentary, and LAPACK-style prose | background and software guidance | non-mathematical/editorial |
| Empirical performance remarks | qualitative observations | empirical, no formalizable theorem statement |

## Benchmark-reserved (identifiers only - NOT formalized as chapter work)
Problems 9.1-9.18 and Appendix A solutions 9.2-9.11, 9.13 are
benchmark-reserved. Some reusable declarations carry `higham_problem9_*` names
from earlier library work; they are not new exercise transcriptions for this
chapter pass.
The rendered PDF lists Problem 9.12, so it is included in this reserved range
even though the current planning ledgers omit that identifier.

## Open selected-scope items (not-proved ledger)
Four selected rows are citation-only in the book (Higham states them without
proof) and remain open. Each carries honest partial/conditional Lean surfaces
(the locally provable arithmetic, monotone consumers, and solve/inverse
bridges) but the core imported inequality is NOT proved locally; the missing
foundation is the cited external proof, which is either unavailable or research-
grade. A conditional wrapper that takes the target bound as a hypothesis does
not close these rows.

| Selected row | Source (no book proof) | Missing foundation | Honest surfaces present | Smallest next Lean target | Status |
|---|---|---|---|---|---|
| Eq. (9.14), complete-pivoting growth upper bound `rho_n^c <= n^{1/2}(2*3^{1/2}...n^{1/(n-1)})^{1/2}` | Wilkinson [1229, 1961]; Higham gives no proof | pivot-magnitude decay under complete pivoting + Hadamard-type determinant inequality on leading submatrices | lower-bound theta families, `higham9_8_*`; Hadamard `rho_n >= n` illustration. **Hadamard foundation PROVED**: `higham9_hadamard_det_sq_le_prod_row_sq`, `higham9_posDef_det_le_prod_diag`, `higham9_hadamard_det_sq_le_pow_maxEntryNorm` (Mathlib gap, via eigenvalue/AM-GM on the Gram matrix). **Pivot-to-leading-minor step NOW PROVED**: `higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag` (`det of k×k leading submatrix = prod of first k pivots`, via leading-block factorization L_k·U_k) and `higham9_14_abs_prod_leadingPivots_le_of_entries_le` (`|prod first-k pivots| <= sqrt(k^k)·M^k` when all leading-submatrix entries `<= M`, combining the leading-minor identity with the Hadamard max-entry bound). Also PROVED: `higham9_14_leadingSubmatrix_det_succ` (consecutive-minor recursion `det B_{k+1} = pivot·det B_k`) and `higham9_14_abs_prod_pivots_le_maxEntryNorm` (`|det A| <= sqrt(n^n)·maxEntryNorm^n`). **The clean, bounded foundation toolkit for (9.14) is now COMPLETE** (Hadamard inequality, leading-minor=∏pivots identity, Hadamard pivot-product bound, consecutive-minor recursion, full-matrix bound). | remaining: Wilkinson's combinatorial assembly tying the stage-`k` max entry to the leading minors `det B_k`. NOTE: this is NOT a simple "global entry invariant" — a per-step max-entry non-increase is FALSE for complete pivoting (the growth factor genuinely exceeds 1). The remaining argument is Wilkinson's research-grade bound of `rho_n = max stage entry / initial max` via Hadamard on each `k`-leading minor; it has no bounded next lemma beyond the foundation now in place. | OPEN — foundation toolkit COMPLETE; remaining assembly is research-grade (no bounded increment) |
| Eq. (9.16), rook-pivoting growth bound `rho_n <= 1.5 n^{(3/4)log n}` | Foster [435, 1997]; Higham gives no proof | Foster's rook-pivoting stage analysis | rook-pivoting dense/rounded-loop `2^{n-1}` bridges | acquire Foster (1997) proof or derive stage bound | OPEN (citation-blocked: paper not in cache) |
| Theorem 9.11, banded GEPP growth (Bohte constant) | Bohte [146, 1975]; Higham gives no proof | Bohte banded-GEPP growth theorem | `higham9_11_bohteBound*`, conditional solve wrappers `higham9_11_bohte_banded_solve_tight*` (take the growth bound as a hypothesis) | acquire Bohte (1975) proof (OUP PDF returns Cloudflare challenge; unavailable) | OPEN (citation-blocked: paper unavailable) |
| Theorem 9.15, full Barrlund-Sun normwise/spectral sensitivity | Barrlund; Sun (cited); book proof omitted | derive the self-majorant inequality `W <= |G| + |G| W` (Schur-induction step) from first principles | componentwise identity/bounds proved (`higham9_15_lu_perturbation_*`); spectral-radius => nonnegative resolvent derived (`higham9_15_nonnegative_resolvent_nonsingInv_of_spectralRadius_lt_one`); self-majorant still a free hypothesis | prove the self-majorant inequality or route it through an equivalent Ch6/7 spectral surface | OPEN (hard; self-majorant is the remaining Schur-induction crux) |

All other selected primary labels (Theorems 9.1, 9.3-9.5, 9.8 lower bound,
9.9, 9.10, 9.12-9.14 endpoints, Lemma 9.6, Algorithm 9.2) are represented by
proved Lean declarations, with Matrix-facing wrappers for the Theorem 9.11-9.13
API surfaces. The section-9.4 growth illustrations of Theorem 9.8 are now
complete for all three matrices Higham names: `S_n` (9.12), `V_n` (9.13), and
the Hadamard matrix (`rho_n >= n`, added this pass).

## Hidden-hypothesis summary
- Exact factorization wrappers state determinant, pivot, diagonal-dominance,
  tridiagonal, SPD, nonnegative, M-matrix, sign-equivalence, or trace
  certificate hypotheses explicitly rather than deriving them silently.
- Rounded GE/solve wrappers expose the loop certificate or budget certificate
  supplying the floating-point local-error model.
- Theorem 9.14 source `f(u)`/`h(u)` endpoints separate model assumptions from
  actual triangular-solve wrappers; gamma-specialized wrappers record the
  required `gammaValid` hypotheses.
- Theorem 9.15 sensitivity results expose inverse/product/resolvent/majorant
  assumptions through named predicates and lemmas; no hidden nonsingularity
  premise is folded into a conclusion.

## Verification
- Recent commands:
  - `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` passed after the final Theorem 9.13 Matrix-wrapper increment.
  - `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` passed: `Build completed successfully (3045 jobs)`.
  - `lake env lean --tstack=131072 examples/LibraryLookup.lean` passed after the final lookup additions.
  - `#print axioms` audits for the newly added Theorem 9.12 and Theorem 9.13 Matrix wrappers all reported only `[propext, Classical.choice, Quot.sound]`.
  - `git diff --check` and added-line placeholder scans were clean before each synced increment.
  - 2026-07-06 (Claude Split-2 proof-completion pass): re-verified current `main` and added the Hadamard section-9.4 growth application. `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` passed (`Build completed successfully (3045 jobs)`); `#print axioms` for the five new `higham9_8_hadamard*` declarations reported only `[propext, Classical.choice, Quot.sound]`; hygiene and `git diff --check` clean. Corrected the selected-scope gate from an overstated PASS to FAIL (citation-blocked) with the not-proved ledger above.
  - 2026-07-06 (same pass, continued): built the **Hadamard determinant inequality** foundation for eq. (9.14), a Mathlib gap, in the `HadamardDeterminantInequality` section: `higham9_amgm_prod_le_one_of_sum_eq_card`, `higham9_posDef_det_le_prod_diag` (`det M ≤ ∏ Mᵢᵢ`, PosDef), `higham9_hadamard_det_sq_le_prod_row_sq` (`(det A)² ≤ ∏ᵢ∑ⱼAᵢⱼ²`), and `higham9_hadamard_det_sq_le_pow_maxEntryNorm` (`(det A)² ≤ nⁿ·(maxEntryNorm A)^{2n}`). All four axiom-clean; three separate build/axiom/sync cycles, all `3045 jobs` PASS. Remaining for (9.14): the complete-pivoting combinatorial assembly (nested leading-minor = product of successive pivots, plus the growth recursion producing Wilkinson's `2·3^{1/2}⋯` product). The repo already provides `LUFactSpec.det_eq_prod_U_diag` (full det = ∏ pivots) and a complete-pivoting entry-≤-pivot invariant; the nested/recursive assembly across all `n` stages remains open and is research-grade.
  - 2026-07-06 (Claude Split-2 proof-completion pass, continued): proved the **pivot-to-leading-minor** step for eq. (9.14). Added `higham9_14_LUFactSpec_leadingSubmatrix_det_eq_prod_U_diag` (`det of the k×k leading principal submatrix of A = ∏ of the first k pivots`, proved via the leading-block factorization `A_k = L_k·U_k`, the tail terms vanishing by lower-triangularity) and `higham9_14_abs_prod_leadingPivots_le_of_entries_le` (`|∏ first-k pivots| ≤ √(kᵏ)·Mᵏ` whenever every leading-submatrix entry is `≤ M`, combining the new leading-minor identity with `higham9_hadamard_det_sq_le_pow_maxEntryNorm`). The entry bound `M` is an explicit hypothesis — this is an honest reduction of (9.14) to the still-open global per-stage entry invariant, not a proof of the full upper bound. `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` PASS (`Build completed successfully (3045 jobs)`); `#print axioms` for both new declarations reported only `[propext, Classical.choice, Quot.sound]`. Remaining for (9.14): promote the per-stage invariant `higham9_1_completePivot_active_entry_ratio_abs_le_one` to a global `all leading-submatrix entries ≤ |a_11|` bound, then the pivot recursion. Gate remains FAIL (this row still OPEN; the three other open rows unchanged).
  - 2026-07-06 (Claude Split-2 proof-completion pass, continued): added the **consecutive leading-minor / pivot relation** `higham9_14_leadingSubmatrix_det_succ` (`det B_{k+1} = pivot_{k+1} · det B_k`, division-free form, via `Fin.prod_univ_castSucc` on the leading-minor identity). This is the classical "pivot = ratio of consecutive leading principal minors" recursion step of Wilkinson's complete-pivoting argument. Build PASS (3045 jobs); axiom-clean. Gate still FAIL: (9.14) still OPEN (global entry invariant + full recursion remain).
  - 2026-07-06 (Claude Split-2 proof-completion pass, continued): added the full-matrix Hadamard pivot-product bound `higham9_14_abs_prod_pivots_le_maxEntryNorm` (`|∏ pivots| = |det A| ≤ √(nⁿ)·(maxEntryNorm A)ⁿ`, via `LUFactSpec.det_eq_prod_U_diag` + Hadamard max-entry bound) — a growth-factor-facing surface with the concrete `maxEntryNorm A` entry bound (no extra hypothesis). Build PASS; axiom-clean. This completes the clean, bounded (9.14) foundation toolkit (leading-minor identity, Hadamard pivot-product bound, consecutive-minor recursion, full-matrix bound). The remaining (9.14) step — the global "all completely-pivoted leading-submatrix entries ≤ |a_11|" invariant — has no small next lemma: it requires building a multi-stage Gaussian-elimination reduced-matrix induction (absent from `LU/GrowthFactor.lean`, which has only per-stage `higham9_1_completePivot_active_entry_ratio_abs_le_one`), a research-grade multi-session effort.

## Documentation
- Inventory and report: `docs/source_coverage/higham_ch09.md` (this file).
- Public lookup smoke checks: `examples/LibraryLookup.lean`.
- Name inventory: `docs/LIBRARY_LOOKUP.md`.

## Open issues
The selected-scope gate is FAIL, blocked by the four citation-only rows in the
not-proved ledger above: eq. (9.14) Wilkinson complete-pivoting upper bound,
eq. (9.16) Foster rook-pivoting bound, Theorem 9.11 Bohte banded GEPP growth,
and the full Barrlund-Sun Theorem 9.15 self-majorant step. (9.16) and 9.11 are
citation-blocked (cited papers unavailable in the source cache); (9.14) and the
9.15 self-majorant are hard local routes not yet closed. No `sorry`, `admit`,
or new `axiom` is used anywhere in the chapter; the open rows are kept honest as
partial/conditional surfaces rather than closed by assuming their conclusions.
