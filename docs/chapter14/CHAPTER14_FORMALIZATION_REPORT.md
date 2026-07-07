# Higham Chapter 14 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002, verified from repository metadata, README, PDF chapter title/numbering, and the DOI-named chapter files.
- Chapter: 14, "Matrix Inversion"
- Printed pages: 259--285
- Source file: `References/1.9780898718027.ch14.pdf`
- Mode: core
- Parallel split: 3A
- Planning documents consulted: blueprint, Split 3A contracts, chapter index
- Inventory path: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter14/CHAPTER14_PROOF_SOURCE_LEDGER.md`
- Selected-scope gate: FAIL, because several selected source-strength bounds are still represented by conditional interfaces or remain unstarted.

## Progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 14 | core | 100 | 97 | 82 | 70 | 85 | 85 | about 16 selected rows/classes | Conditional floating-point interfaces for Method 2/2C, Method D final-bound composition, and GJE second-stage accumulation; Method 2B instability route, Hadamard equality converse, Hyman backward error, and remaining problem rows still partly open | medium |

## Completed selected targets

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| (14.1) | `ideal_right_residual` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact componentwise right-residual bound from an explicit perturbation and right-inverse equation. | Proved. |
| (14.2) | `ideal_left_residual` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact componentwise left-residual bound from an explicit perturbation and left-inverse equation. | Proved. |
| (14.4) | `triInv_method1_right_residual_matrix` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Method 1 right-residual bound via Ch8 triangular solve. | Proved from existing triangular solve theorem. |
| (14.5) | `triInv_method1_forward_error` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Componentwise forward-error bound for Method 1. | Proved. |
| (14.7) | `triInv_method1_normwise_error` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Legacy infinity-norm wrapper. | Proved. |
| (14.14) Method 2B block update | `higham14_method2BBlockUpdateExact`, `higham14_method2BBlockUpdateDelta`, `higham14_eq14_14_method2B_block_update_decomposition`, `higham14_eq14_14_method2B_block_update_delta_bound`, `higham14_eq14_14_method2B_exact_offdiag_block_update` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact off-diagonal block formula `X21 = -X22 L21 X11` from the block equation and `L11 X11 = I`, plus the computed-update delta decomposition and inherited delta bound. | Exact algebra/delta wrapper closed; the source instability analysis remains open. |
| (14.15)--(14.17) | `methodA_column_backward_error*`, `methodA_right_residual*`, `methodA_forward_error*` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Method A column, residual, and forward-error wrappers. | Proved from explicit specs/budgets. |
| (14.18) | `methodB_left_residual` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Method B left-residual bound from supplied triangular-inverse/solve specs. | Conditional but internally proved from stated hypotheses. |
| (14.19) | `methodC_mixed_residual`, `methodC_forward_error` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Mixed-residual interface and forward-error consequence. | Mixed residual is assumed; forward consequence proved. |
| (14.20)--(14.23) Method D exact expansion | `higham14_methodDProductDelta`, `higham14_methodDLUBackwardDelta`, `higham14_methodDXLLeftResidual`, `higham14_methodDXULeftResidual`, `higham14_eq14_20_methodD_product_decomposition`, `higham14_eq14_20_methodD_productDelta_bound`, `higham14_eq14_21_methodD_lu_substitution`, `higham14_eq14_21_methodD_luDelta_bound`, `higham14_eq14_22_methodD_left_residual_expansion`, `higham14_eq14_23_methodD_left_residual_bound` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Product-formation delta, LU backward delta, triangular-inverse residual deltas, exact LU substitution, exact residual expansion, and a source-facing conditional final-bound wrapper. | Equations (14.20)--(14.22) closed as exact algebra; (14.23) still assumes the combined componentwise budget. |
| (14.24) | `left_right_residual_comparison` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact comparison of left and right residuals through a left inverse. | Proved. |
| Problem 14.3 | `higham14_problem14_3_right_over_left_residual_infNorm_le_kappa`, `higham14_problem14_3_left_over_right_residual_infNorm_le_kappa`, `higham14_problem14_3_max_residual_ratio_infNorm_le_kappa` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Infinity-norm residual-ratio bound by `kappaInf`; includes exact identities `AX-I = A(XA-I)A_inv` and `XA-I = A_inv(AX-I)A`. | New after the initial milestone; denominators are explicit positivity hypotheses. |
| Problem 14.4 | `higham14_problem14_4_right_over_left_ratio_arbitrarily_large` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Source two-by-two family with `||AX-I||_inf / ||XA-I||_inf` arbitrarily large as `eps -> 0`; support includes exact `XA`, exact `AX`, left-residual norm, and right-residual lower-bound theorems. | Closed for the infinity norm. |
| Problem 14.5 residual, forward, and first-order comparison bounds | `higham14_problem14_5_right_inverse_solve_residual_bound`, `higham14_problem14_5_left_inverse_solve_residual_bound`, `higham14_problem14_5_forward_error_of_residual_bound`, `higham14_problem14_5_right_inverse_solve_forward_error_bound`, `higham14_problem14_5_left_inverse_solve_forward_error_bound`, `higham14_problem14_5_right_inverse_solve_forward_error_firstorder_replacement`, `higham14_problem14_5_left_inverse_solve_forward_error_firstorder_replacement`, `higham14_problem14_5_left_firstorder_envelope_le_right_exact_rhs_envelope` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Right- and left-approximate-inverse residual bounds, residual-to-forward-error transfer, exact right/left forward envelopes, explicit `|X|`/`|Y|` replacement wrappers, and the exact envelope comparison showing the right first-order exact-RHS envelope is the left envelope after one extra `|A_inv||A|` amplification. | Source comparison layer closed at explicit bounded-replacement strength; full asymptotic `O(u^2)` calculus remains open. |
| Problem 14.7 | `higham14_problem14_7_inverse_entries_sum_eq_one_of_row_ones`, `higham14_problem14_7_inverse_entries_sum_eq_one_of_col_ones` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Sum of all inverse entries is one when A has a row or column of ones. | New in this pass; proved. |
| p.279 `psi(A)` | `higham14_hadamardConditionNumber`, `higham14_hadamardConditionNumberRaw`, `higham14_det_rowNormDiagonal_eq_prod_rowNorm2`, `higham14_hadamardConditionNumber_eq_det_rowNormDiagonal_div_abs_det`, `higham14_hadamardConditionNumberRaw_eq_conditionNumber_of_det_pos`, `higham14_hadamardConditionNumber_nonneg`, `higham14_hadamardConditionNumber_pos_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Row 2-norm diagonal determinant definition of the Hadamard determinant condition number, with a nonnegative `|det(A)|` denominator and a raw signed displayed-ratio bridge. | Definition row closed; Problem 14.11 now closes the inequality/`psi >= 1` consequence and the orthogonal-row equality direction. |
| Problem 14.11 inequality, equality direction, and `psi(A) >= 1` | `higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq`, `higham14_problem14_11_abs_det_le_prod_rowNorm2`, `higham14_problem14_11_hadamardConditionNumber_ge_one_of_det_ne_zero`, `higham14_rowsOrthogonal`, `higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_rowsOrthogonal` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Hadamard determinant inequality in squared row-norm and absolute determinant forms, the nonsingular lower bound `1 <= psi(A)`, and equality under pairwise row orthogonality. | Inequality closed by reusing the Chapter 9 Gram determinant proof; the orthogonal-row equality direction is proved by a local Gram-diagonal determinant argument. The converse/equivalence characterization remains open. |
| Problem 14.12(a) QR formula for `psi(A)` | `higham14_colNorm2`, `higham14_abs_det_eq_one_of_isOrthogonal`, `higham14_colNorm2_matMul_orthogonal_left`, `higham14_rowNorm2_eq_colNorm2_of_transpose_qr`, `higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr_det_product`, `higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | If `A^T = Q R`, `Q` is orthogonal, and `R` has determinant equal to the product of its diagonal entries, then `psi(A) = prod_i ||R(:,i)||_2 / |r_ii|`; upper-triangular `R` is supplied as the source-shaped corollary. | Exact algebra closed under an abstract QR certificate, so Split 3A does not own QR algorithm/stability infrastructure. |
| Problem 14.12(b) `U(1)` evaluation | `higham14_problem14_12_hadamardConditionNumber_stressUpper_one_eq_sqrt_factorial` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | For the Chapter 8 stress matrix `U(1)`, `psi(U(1)) = sqrt(n!)`. | Closed by direct exact determinant and row-norm product algebra. |
| Problem 14.12(b) Pei matrix evaluation | `higham14_peiMatrix`, `higham14_problem14_12_peiMatrix_det`, `higham14_problem14_12_peiMatrix_rowNorm2`, `higham14_problem14_12_peiMatrix_prod_rowNorm2`, `higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs`, `higham14_problem14_12_hadamardConditionNumber_peiMatrix` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | For `A = (alpha - 1)I + ee^T`, `psi(A) = sqrt(alpha^2+n-1)^n / |(n+alpha-1)(alpha-1)^(n-1)|`, with the unsigned Appendix A denominator proved when `0 < n` and `1 < alpha`. | Closed by the matrix determinant lemma for the rank-one update and direct row-norm algebra; the absolute-value denominator matches the repository's nonnegative `psi` convention. |
| Problem 14.13 AM-GM support | `higham14_problem14_13_amgm_prod_le_pow_sum_div_card`, `higham14_problem14_13_gej_squared_bound_from_amgm`, `higham14_problem14_13_gej_bound_from_squared`, `higham14_problem14_13_gej_bound_from_amgm_certificate`, `higham14_problem14_13_frobNorm_eq_sqrt_card_of_rowNorm2_eq_one`, `higham14_problem14_13_hadamardConditionNumber_eq_inv_abs_det_of_rowNorm2_eq_one`, `higham14_problem14_13_two_over_abs_det_eq_two_mul_hadamardConditionNumber`, `higham14_problem14_13_kappa_lt_two_mul_hadamardConditionNumber_of_unit_rows` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Appendix A AM-GM algebra and row-unit reductions for the Guggenheimer-Edelman-Johnson bound. | Dependency layer closed and now instantiated by the source AM-GM family for dimensions `k + 2`. |
| Problem 14.13 norm-side SVD bridge | `higham14_problem14_13_opNorm2_eq_complexMatrixOp2_realRectToCMatrix`, `higham14_problem14_13_opNorm2_eq_complex_top_singularValue`, `higham14_problem14_13_frobNorm_sq_eq_complexMatrixFrobeniusSq`, `higham14_problem14_13_frobNorm_sq_eq_sum_complex_singularValue_sq`, `higham14_problem14_13_lowerNorm_eq_complex_last_singularValue`, `higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue`, `higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Connects the repository's real `opNorm2`, `frobNorm`, lower norm, inverse norm, and `kappa2` to the ordered singular values of the complexified real matrix. | Norm-side SVD bridge closed for supplied right inverses and used by the source GEJ theorem. |
| Problem 14.13 determinant product bridge | `higham14_problem14_13_complexGramLin_det_eq_prod_gramEigenvalues`, `higham14_problem14_13_complex_det_conjTranspose_mul_self_eq_prod_singularValue_sq`, `higham14_problem14_13_real_det_sq_eq_prod_complex_singularValue_sq`, `higham14_problem14_13_abs_det_eq_prod_complex_singularValue`, `higham14_problem14_13_abs_det_pos_of_isRightInverse`, `higham14_problem14_13_gej_bound_from_matrix_amgm_certificate` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Proves the ordered-singular-value determinant product for real square matrices via complexified Gram determinants, derives determinant positivity from a supplied right inverse, and packages the matrix-shaped GEJ AM-GM certificate wrapper. | Determinant side closed and used by the source GEJ theorem. |
| Problem 14.13 source GEJ bound and unit-row corollary | `higham14_problem14_13_gejAmgmFamily`, `higham14_problem14_13_gejAmgmFamily_nonneg`, `higham14_problem14_13_last_singularValue_pos_of_isRightInverse`, `higham14_problem14_13_gejAmgmFamily_prod`, `higham14_problem14_13_gejAmgmFamily_sum_add_last_singularValue_sq`, `higham14_problem14_13_gejAmgmFamily_sum_lt_frobNorm_sq`, `higham14_problem14_13_gej_bound_of_isRightInverse`, `higham14_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Constructs the printed AM-GM family `σ₁²/2, σ₁²/2, σ₂², ..., σₙ₋₁²`, proves its nonnegativity, product, and strict Frobenius-sum certificates, derives the GEJ inequality for dimensions `k + 2`, and closes the unit-row `κ₂(A) < 2ψ(A)` corollary. | Source-strength Problem 14.13 / (14.37) closed for dimensions at least two. |
| (14.34) | `higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec`, `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec`, `higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec`, `higham14_eq14_34_det_eq_perm_sign_mul_prod_U_diag_of_PermutedLUFactSpec`, `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Determinant/product-of-pivots identity for exact no-pivot/unit-lower LU certificates and signed/absolute determinant products for row-permuted LU certificates. | Equation (14.34) closed. |
| (14.35)--(14.36) | `higham14_eq14_35_hyman_block_lu_factorization`, `higham14_eq14_36_hyman_det_cyclic_block`, `higham14_eq14_36_hyman_det_original_of_row_permutation` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact Hyman block LU factorization, determinant of the cyclically permuted block `H₁`, and signed row-permutation wrapper for the original Hessenberg matrix. | Exact determinant algebra closed; Problem 14.14 still owns the floating-point backward-error and scaling analysis. |
| Problem 14.10 | `higham14_problem14_10_det_entry_perturb_eq`, `higham14_problem14_10_det_entry_independent_iff_adjugate_eq_zero` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact determinant entry-perturbation formula and iff condition for determinant independence from `a_ij`. | New after Problem 14.3; cofactor/adjugate condition is explicit. |
| Theorem 14.5 composition | `gje_overall_residual`, `gje_overall_forward_error` | `LeanFpAnalysis/FP/Algorithms/GaussJordan.lean` | Composition from explicit GE and GJE second-stage hypotheses. | Partial source closure; printed constants still open. |

## Reused from repository or Mathlib

| Source concept/result | Existing declaration | File/module |
|---|---|---|
| Legacy inverse predicates | `IsLeftInverse`, `IsRightInverse`, `IsInverse` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Matrix multiplication and identity | `matMul`, `idMatrix` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Triangular solve backward-error infrastructure | `forwardSub_backward_error`, related triangular solve APIs | `LeanFpAnalysis.FP.Algorithms.ForwardSub`, `TriangularSolve` |
| Chapter 8 stress matrix family | `higham8_3_stressUpper` | `LeanFpAnalysis.FP.Algorithms.HighamChapter8` |
| LU backward-error interface | `LUBackwardError` | `LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination` |
| Floating-point gamma model | `gamma`, `gammaValid` | `LeanFpAnalysis.FP.Model` |
| Hadamard determinant inequality | `higham9_hadamard_det_sq_le_prod_row_sq` | `LeanFpAnalysis.FP.Algorithms.HighamChapter9` |

## New dependencies

| Declaration | Why needed | Used by | Feasibility status |
|---|---|---|---|
| `inverseRightResidual`, `inverseLeftResidual` | Stable source-facing names for `AX-I` and `XA-I`. | Problem 14.3; later Problems 14.4--14.5. | implemented |
| `higham14_problem14_3_right_residual_eq_mul_left_residual` | Exact identity `AX-I = A(XA-I)A_inv`. | Problem 14.3 right-over-left ratio. | implemented |
| `higham14_problem14_3_left_residual_eq_mul_right_residual` | Exact identity `XA-I = A_inv(AX-I)A`. | Problem 14.3 left-over-right ratio. | implemented |
| `higham14_problem14_3_max_residual_ratio_infNorm_le_kappa` | Closes the printed max residual-ratio inequality for `infNorm` under nonzero residual denominators. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_4_A`, `higham14_problem14_4_X` | Source two-by-two family from Appendix A Problem 14.4. | Problem 14.4 residual-ratio counterexample. | implemented |
| `higham14_problem14_4_XA_eq`, `higham14_problem14_4_AX_eq` | Exact products for the displayed family. | Problem 14.4 residual norm bounds. | implemented |
| `higham14_problem14_4_right_over_left_ratio_arbitrarily_large` | Closes the arbitrarily-large right-over-left residual ratio. | Chapter 14 inventory/report. | implemented |
| `higham14_unit_roundoff_add_gamma_le_gamma_succ` | Scalar gamma collapse `u + gamma_n <= gamma_(n+1)`. | Problem 14.5 residual bound. | implemented |
| `higham14_problem14_5_right_inverse_solve_residual_bound` | Closes the right-approximate-inverse residual half of Problem 14.5. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_inverse_solve_residual_bound` | Closes the left-approximate-inverse residual half of Problem 14.5 with `b = Ax`. | Chapter 14 inventory/report. | implemented |
| `higham14_inverseLeftResidual_mulVec_add_self` | Expands `Y(Ax)` as `(YA-I)x + x` for the left forward-error proof. | Problem 14.5 left forward-error bound. | implemented |
| `higham14_problem14_5_forward_error_of_residual_bound` | Transfers a componentwise residual envelope to a forward-error envelope via a supplied left inverse. | Problem 14.5 right forward-error bound. | implemented |
| `higham14_problem14_5_right_inverse_solve_forward_error_bound` | Closes the right-approximate-inverse forward-error consequence through `|A_inv|`. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_inverse_solve_forward_error_bound` | Closes the exact `|Y||A||x|` left forward-error bound from Appendix A Problem 14.5. | Chapter 14 inventory/report. | implemented |
| `higham14_absMatrix_matMulVec_mono`, `higham14_absMatrix_matMulVec_nonneg` | Componentwise monotonicity and nonnegativity for absolute-matrix products. | Problem 14.5 first-order replacement wrappers. | implemented |
| `higham14_problem14_5_right_inverse_solve_forward_error_bound_of_abs_X_le` | Replaces `|X|` in the right forward envelope by any caller-supplied componentwise upper bound. | Problem 14.5 first-order replacement. | implemented |
| `higham14_problem14_5_right_inverse_solve_forward_error_firstorder_replacement` | Specializes the right forward envelope to `|A_inv||A||A_inv||b|` under `|X| <= |A_inv|`. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_inverse_solve_forward_error_bound_of_abs_Y_le` | Replaces `|Y|` in the left forward envelope by any caller-supplied componentwise upper bound. | Problem 14.5 first-order replacement. | implemented |
| `higham14_problem14_5_left_inverse_solve_forward_error_firstorder_replacement` | Specializes the left forward envelope to `|A_inv||A||x|` under `|Y| <= |A_inv|`. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_firstorder_envelope_le_right_exact_rhs_envelope` | Formalizes the comparison: with `b = Ax`, the right first-order exact-RHS envelope applies an extra `|A_inv||A|` amplification to the left envelope. | Problem 14.5 interpretation. | implemented |
| `higham14_method2BBlockUpdateExact`, `higham14_method2BBlockUpdateDelta` | Source-facing exact off-diagonal Method 2B block update and computed-update delta. | Equation (14.14). | implemented |
| `higham14_eq14_14_method2B_block_update_decomposition`, `higham14_eq14_14_method2B_block_update_delta_bound` | Computed block-update decomposition and inherited componentwise delta bound. | Equation (14.14). | implemented |
| `higham14_eq14_14_method2B_exact_offdiag_block_update` | Exact block formula from `X21 L11 + X22 L21 = 0` and `L11 X11 = I`. | Equation (14.14) exact algebra. | implemented |
| `higham14_methodDProductDelta`, `higham14_methodDLUBackwardDelta` | Source-facing perturbation matrices for Method D product formation and LU backward error. | Equations (14.20)--(14.21). | implemented |
| `higham14_methodDXLLeftResidual`, `higham14_methodDXULeftResidual` | Source-facing residual deltas for the lower and upper triangular inverse factors in Method D. | Equation (14.22). | implemented |
| `higham14_eq14_20_methodD_product_decomposition`, `higham14_eq14_20_methodD_productDelta_bound` | Exact product decomposition and inherited componentwise product-error bound. | Equation (14.20). | implemented |
| `higham14_eq14_21_methodD_lu_substitution`, `higham14_eq14_21_methodD_luDelta_bound` | Exact `X_hat A` expansion through `A = L_hat U_hat - Delta_A` and inherited LU backward-error bound. | Equation (14.21). | implemented |
| `higham14_eq14_22_methodD_left_residual_expansion` | Exact split of `X_hat A - I` into upper residual, propagated lower residual, product perturbation, and LU perturbation terms. | Equation (14.22). | implemented |
| `higham14_eq14_23_methodD_left_residual_bound` | Source-facing final Method D left-residual bound interface. | Equation (14.23). | implemented as conditional interface |
| `matrixEntryPerturb` | Source-facing additive perturbation of one matrix entry. | Problem 14.10. | implemented |
| `higham14_problem14_10_det_entry_perturb_eq` | Exact determinant change formula `det(A+tE_ij)=det(A)+t*adj(A)_{ji}`. | Problem 14.10 independence iff. | implemented |
| `higham14_problem14_10_det_entry_independent_iff_adjugate_eq_zero` | Closes the determinant-independence condition in cofactor/adjugate form. | Chapter 14 inventory/report. | implemented |
| `higham14_rowNorm2` | Source-facing `||A(i,:)||_2` row norm used in the p.279 `psi(A)` definition. | Hadamard determinant condition number. | implemented |
| `higham14_rowNormDiagonal` | Diagonal matrix `D = diag(||A(i,:)||_2)`. | Hadamard determinant condition number. | implemented |
| `higham14_hadamardConditionNumber` | Nonnegative Hadamard determinant condition number `prod_i ||A(i,:)||_2 / |det(A)|`. | p.279 `psi(A)` definition and Problem 14.11 route. | implemented |
| `higham14_hadamardConditionNumberRaw` | Signed raw displayed ratio `prod_i ||A(i,:)||_2 / det(A)`. | p.279 printed display audit. | implemented |
| `higham14_det_rowNormDiagonal_eq_prod_rowNorm2` | Shows `det(D)` is the product of the row 2-norms. | p.279 `det(D)/det(A)` bridge. | implemented |
| `higham14_hadamardConditionNumber_eq_det_rowNormDiagonal_div_abs_det` | Rewrites the condition number as `det(D)/|det(A)|`. | p.279 `psi(A)` source form. | implemented |
| `higham14_hadamardConditionNumberRaw_eq_conditionNumber_of_det_pos` | Shows the raw displayed ratio agrees with the positive condition-number form when `det(A)>0`. | Hidden absolute-value audit. | implemented |
| `higham14_hadamardConditionNumber_nonneg` | Nonnegativity of the positive `psi(A)` surface. | Problem 14.11 route. | implemented |
| `higham14_hadamardConditionNumber_pos_of_det_ne_zero` | Positivity of `psi(A)` for nonsingular matrices. | Problem 14.11 route. | implemented |
| `higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq` | Chapter 14 squared row-norm Hadamard inequality wrapper. | Problem 14.11. | implemented |
| `higham14_problem14_11_abs_det_le_prod_rowNorm2` | Absolute determinant form `|det(A)| <= prod_i ||A(i,:)||_2`. | Problem 14.11 and `psi(A) >= 1`. | implemented |
| `higham14_problem14_11_hadamardConditionNumber_ge_one_of_det_ne_zero` | Lower bound `1 <= psi(A)` for nonsingular matrices under the nonnegative denominator convention. | Problem 14.11. | implemented |
| `higham14_rowsOrthogonal` | Source-facing predicate for pairwise Euclidean orthogonality of rows. | Problem 14.11 equality direction. | implemented |
| `higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_rowsOrthogonal` | Equality in Hadamard's determinant inequality when the rows are pairwise orthogonal. | Problem 14.11 equality direction. | implemented |
| `higham14_colNorm2` | Source-facing `rho_i = ||R(:,i)||_2` column norm used by Problem 14.12(a). | Problem 14.12(a). | implemented |
| `higham14_abs_det_eq_one_of_isOrthogonal` | Determinant absolute value of a real orthogonal matrix is one. | Problem 14.12(a) QR denominator. | implemented |
| `higham14_colNorm2_matMul_orthogonal_left` | Orthogonal left multiplication preserves column 2-norms. | Problem 14.12(a) numerator. | implemented |
| `higham14_rowNorm2_eq_colNorm2_of_transpose_qr` | Row norms of `A` become column norms of `R` under `A^T = Q R`. | Problem 14.12(a). | implemented |
| `higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr_det_product` | QR formula for `psi(A)` with a supplied determinant product for `R`. | Problem 14.12(a). | implemented |
| `higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr` | Source-shaped QR formula for `psi(A)` under upper-triangular `R`. | Problem 14.12(a). | implemented |
| `higham14_problem14_12_hadamardConditionNumber_stressUpper_one_eq_sqrt_factorial` | Appendix A closed form `psi(U(1)) = sqrt(n!)` for the Chapter 8 stress matrix. | Problem 14.12(b). | implemented |
| `higham14_peiMatrix` | Source-facing Pei matrix `A = (alpha - 1)I + ee^T`, with diagonal entries `alpha` and off-diagonal entries `1`. | Problem 14.12(b). | implemented |
| `higham14_problem14_12_peiMatrix_det` | Determinant of the Pei matrix as `(n+alpha-1)(alpha-1)^(n-1)` under `0 < n` and `alpha != 1`. | Problem 14.12(b). | implemented |
| `higham14_problem14_12_peiMatrix_rowNorm2` | Common row 2-norm `sqrt(alpha^2+n-1)` for the Pei matrix. | Problem 14.12(b). | implemented |
| `higham14_problem14_12_peiMatrix_prod_rowNorm2` | Numerator product `sqrt(alpha^2+n-1)^n` for the Pei matrix. | Problem 14.12(b). | implemented |
| `higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs` | Pei `psi` formula with the repository's nonnegative absolute-value denominator. | Problem 14.12(b). | implemented |
| `higham14_problem14_12_hadamardConditionNumber_peiMatrix` | Appendix A unsigned Pei denominator formula under `0 < n` and `1 < alpha`. | Problem 14.12(b). | implemented |
| `higham14_problem14_13_amgm_prod_le_pow_sum_div_card` | Finite AM-GM product inequality `prod z <= ((sum z)/n)^n` for nonnegative families. | Problem 14.13 Appendix A algebra. | implemented |
| `higham14_problem14_13_gej_squared_bound_from_amgm` | Squared GEJ AM-GM consequence from a supplied product/sum certificate. | Problem 14.13 Appendix A algebra. | implemented |
| `higham14_problem14_13_gej_bound_from_squared` | Converts the squared conclusion to the printed `kappa < 2/detAbs * (frob/sqrt n)^n` shape. | Problem 14.13 Appendix A algebra. | implemented |
| `higham14_problem14_13_gej_bound_from_amgm_certificate` | Source-shaped AM-GM certificate theorem for the GEJ determinant/condition bound. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_opNorm2_eq_complexMatrixOp2_realRectToCMatrix` | Real exact `opNorm2` equals the operator norm of the complexified real matrix. | Problem 14.13 SVD bridge. | implemented |
| `higham14_problem14_13_opNorm2_eq_complex_top_singularValue` | Real exact `opNorm2` equals the largest ordered singular value after complexification. | Problem 14.13 SVD bridge. | implemented |
| `higham14_problem14_13_frobNorm_sq_eq_complexMatrixFrobeniusSq` | Real Frobenius square equals the complexified Frobenius square. | Problem 14.13 SVD bridge. | implemented |
| `higham14_problem14_13_frobNorm_sq_eq_sum_complex_singularValue_sq` | Real Frobenius square equals the sum of squared ordered singular values. | Problem 14.13 SVD bridge. | implemented |
| `higham14_problem14_13_lowerNorm_eq_complex_last_singularValue` | Euclidean lower norm equals the last ordered singular value for `(k+1) x (k+1)` real matrices. | Problem 14.13 SVD bridge. | implemented |
| `higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue` | A supplied right inverse has operator norm equal to the reciprocal of the last ordered singular value. | Problem 14.13 SVD bridge. | implemented |
| `higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse` | For a supplied right inverse, `kappa2 = sigma_1 / sigma_n`. | Problem 14.13 SVD bridge. | implemented |
| `higham14_problem14_13_complexGramLin_det_eq_prod_gramEigenvalues` | Identifies the complex Gram linear-map determinant with the product of its ordered Gram eigenvalues. | Problem 14.13 determinant product. | implemented |
| `higham14_problem14_13_complex_det_conjTranspose_mul_self_eq_prod_singularValue_sq` | Shows `det(AᴴA)` is the product of squared ordered singular values for complex square matrices. | Problem 14.13 determinant product. | implemented |
| `higham14_problem14_13_real_det_sq_eq_prod_complex_singularValue_sq` | Transfers the complex Gram determinant identity to `(det A)^2` for real square matrices. | Problem 14.13 determinant product. | implemented |
| `higham14_problem14_13_abs_det_eq_prod_complex_singularValue` | Proves `|det A| = prod_i sigma_i` for the complexified real matrix. | Problem 14.13 determinant product. | implemented |
| `higham14_problem14_13_abs_det_pos_of_isRightInverse` | Derives `0 < |det A|` from a supplied right-inverse certificate. | Problem 14.13 matrix AM-GM wrapper. | implemented |
| `higham14_problem14_13_gej_bound_from_matrix_amgm_certificate` | Applies the GEJ AM-GM certificate theorem directly to a real matrix and supplied right inverse. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_gejAmgmFamily` | Defines the source AM-GM family `σ₁²/2, σ₁²/2, σ₂², ..., σₙ₋₁²` for dimensions `k + 2`. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_gejAmgmFamily_nonneg` | Nonnegativity of the source AM-GM family. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_last_singularValue_pos_of_isRightInverse` | A supplied right inverse makes the last ordered singular value positive. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_gejAmgmFamily_prod` | Product certificate for the source AM-GM family. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_gejAmgmFamily_sum_add_last_singularValue_sq` | Sum of the source AM-GM family plus `σₙ²` equals `frobNorm A ^ 2`. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_gejAmgmFamily_sum_lt_frobNorm_sq` | Strict Frobenius-sum certificate for the source AM-GM family. | Problem 14.13 source closure. | implemented |
| `higham14_problem14_13_gej_bound_of_isRightInverse` | Source GEJ determinant/condition inequality for dimensions `k + 2`. | Problem 14.13 / (14.37). | implemented |
| `higham14_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows` | Unit-row corollary `kappa2 A Ainv < 2 * psi(A)` for dimensions `k + 2`. | Problem 14.13(b). | implemented |
| `higham14_problem14_13_frobNorm_eq_sqrt_card_of_rowNorm2_eq_one` | Unit row norms imply `frobNorm A = sqrt n`. | Problem 14.13(b). | implemented |
| `higham14_problem14_13_hadamardConditionNumber_eq_inv_abs_det_of_rowNorm2_eq_one` | Unit row norms imply `psi(A) = 1/|det(A)|`. | Problem 14.13(b). | implemented |
| `higham14_problem14_13_two_over_abs_det_eq_two_mul_hadamardConditionNumber` | Identifies `2/|det(A)|` with `2*psi(A)` under unit row norms. | Problem 14.13(b). | implemented |
| `higham14_problem14_13_kappa_lt_two_mul_hadamardConditionNumber_of_unit_rows` | Transfers a supplied `kappa < 2/|det(A)|` bound to `kappa < 2*psi(A)` for unit-row matrices. | Problem 14.13(b). | implemented support |
| `higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec` | Source-facing Chapter 14 wrapper around the existing unit-lower LU determinant product identity. | Equation (14.34) no-pivot core. | implemented |
| `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec` | Absolute-value form of the exact no-pivot LU determinant product. | Equation (14.34) no-pivot core. | implemented |
| `higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec` | Direct row-permuted determinant relation `sign(σ) det(A) = ∏ᵢ uᵢᵢ` for `PA = LU`. | Equation (14.34) GEPP signed product. | implemented |
| `higham14_eq14_34_det_eq_perm_sign_mul_prod_U_diag_of_PermutedLUFactSpec` | Source-oriented signed product `det(A) = sign(σ) ∏ᵢ uᵢᵢ`, using that permutation signs square to one. | Equation (14.34) GEPP signed product. | implemented |
| `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec` | Absolute-value determinant product for row-permuted LU certificates. | Equation (14.34) GEPP absolute-value product. | implemented |
| `higham14_hymanRowTimesInv`, `higham14_hymanSchur`, `higham14_hymanBlockMatrix` | Source-facing Hyman row product, Schur scalar, and cyclically permuted block matrix `H₁`. | Equations (14.35)--(14.36). | implemented |
| `higham14_hymanLowerFactor`, `higham14_hymanUpperFactor` | Source-facing Hyman lower and upper block factors. | Equation (14.35). | implemented |
| `higham14_hymanRowTimesInv_mul_T` | Proves `(hᵀT⁻¹)T = hᵀ` from the explicit inverse certificate `T⁻¹T = I`. | Hyman block LU factorization. | implemented |
| `higham14_eq14_35_hyman_block_lu_factorization` | Exact block LU factorization `H₁ = LU` for Hyman's cyclic block matrix. | Equation (14.35). | implemented |
| `higham14_eq14_36_hyman_det_cyclic_block` | Determinant formula `det(H₁)=det(T)(η-hᵀT⁻¹y)`. | Equation (14.36) cyclic block step. | implemented |
| `higham14_eq14_36_hyman_det_original_of_row_permutation` | Signed determinant wrapper for an original matrix whose row permutation is `H₁`. | Equation (14.36) source sign step. | implemented |
| `higham14_problem14_7_inverse_entries_sum_eq_one_of_row_ones` | Closes the row-ones half of Problem 14.7. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_7_inverse_entries_sum_eq_one_of_col_ones` | Closes the column-ones half of Problem 14.7. | Chapter 14 inventory/report. | implemented |

## External proof sources

| Selected claim | Source and exact location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| Lemmas 14.1--14.3 and Method A--D bounds | Du Croz and Higham [357, 1992], exact locations not yet acquired | Detailed inverse-method error analyses | Partial interfaces only | open |
| Theorem 14.5 second-stage GJE | Peters-Wilkinson [938, 1975] and Dekker-Hoffmann [303, 1989], exact locations not yet acquired | GJE second-stage proof route | Composition wrappers only | open |
| Hyman method / Problem 14.14 | Wilkinson references cited in Notes 14.7; Appendix A solution 14.14 | Hyman determinant error route | Exact determinant identities (14.35)--(14.36) closed; floating-point error route open | partial foundation |
| Problem 14.15 | Godunov et al. [493, 1993] and singular-value inequalities cited in Appendix A | Determinant perturbation theorem | none | open |

## GPT-5.5 Pro browser consultations

No consultation was used in this milestone. The current blockers are inventoried and still at the repository/Mathlib search and theorem-design stage.

## Skipped items

| Source location | Summary | Reason code |
|---|---|---|
| Figure 14.1 | MATLAB residual plot for a specific family and implementation. | SKIP-EMPIRICAL |
| Tables 14.1--14.5 | Backward-error samples, performance rates, and historical timings. | SKIP-EMPIRICAL |
| Notes 14.7 and LAPACK prose | Literature and software notes. | SKIP-LITERATURE-REVIEW |
| Problem 14.1 | Historical cautionary tale. | SKIP-EDITORIAL |
| Problem 14.6 | Fixed external cover-matrix exercise. | SKIP-FIXED-NUMERICAL |

## Deferred items

| Source location | Summary | Destination/dependency | Reason |
|---|---|---|---|
| Problem 14.9 | Computational investigation of a generalized Sylvester-equation approach. | Chapter 16 / benchmark mode | The source asks for a computational investigation and references Sylvester machinery. |
| Section 14.5 Schulz/Csanky overview | Parallel inverse methods and convergence commentary. | Future benchmark/algorithm work if requested | Mostly literature review and broad algorithm survey; precise Schulz identities are not needed for current core closures. |

## Benchmark candidates

| Source location | Methods compared | Required dependencies |
|---|---|---|
| Section 14.5 | Csanky, Schulz iteration, and parallel/divide-and-conquer inverse methods | Complexity model, matrix iteration convergence, floating-point stability model |
| Tables 14.2--14.5 | Triangular/full inverse implementations on specific machines | Machine and implementation model, benchmark mode |

## Open selected-scope items

See `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`. The highest-leverage next rows are:

| Source location | Exact claim | Current Lean status | Missing foundation | Next theorem |
|---|---|---|---|---|
| Lemma 14.1 / (14.8) | Method 2 left residual | conditional transfer | Method 2 stage induction | Source-faithful Method 2 loop residual theorem |
| (14.25)--(14.30) | GJE second-stage accumulation | conditional transfer | cumulative product induction | Exact (14.27)--(14.28) wrappers, then (14.29)--(14.30) |
| Theorem 14.5 | Printed GJE constants | partial foundation | second-stage closure and first-order scalar simplification | Instantiate composition theorem to `8 n u`/`2 n u` source surfaces |
| Problem 14.11 | Hadamard determinant inequality and equality case for `psi(A)` | partial foundation | Equality converse | Prove the converse/equivalence side of the equality characterization, likely via equality conditions in the Gram determinant/AM-GM route |
| Problem 14.14 | Hyman backward-error bound and diagonal scaling effect | unstarted | triangular solve and inner-product error composition | Compose the exact (14.36) determinant identity with back-substitution and inner-product perturbation bounds |

## Hidden-hypothesis summary

- The new Problem 14.3 max-ratio theorem assumes both residual denominators are positive. The two one-sided ratio lemmas require only the denominator used by that ratio. This makes the source's implicit nonzero-ratio side condition explicit.
- The new Problem 14.4 theorem closes the Appendix A two-by-two family in infinity norm. It proves exact `XA`, exact `AX`, `||XA-I||_inf = 2 eps`, a right-residual lower bound, and an arbitrary-large right-over-left ratio for `0 < eps <= 1`.
- The new Problem 14.5 theorems close both source residual bounds, the exact right/left forward-error consequences, explicit first-order replacement wrappers, and the exact envelope-comparison interpretation. The right residual theorem assumes `|AX-I| <= u|A||X|`; the right forward theorem additionally assumes a supplied left inverse `A_inv` and `Ax = b`. The first-order wrappers make the `|X| <= |A_inv|` and `|Y| <= |A_inv|` replacement assumptions explicit; the comparison theorem shows the exact-RHS right envelope is the left first-order envelope after one extra nonnegative `|A_inv||A|` amplification. Full asymptotic `O(u^2)` replacement calculus remains open.
- The new Method 2B theorem for (14.14) assumes the off-diagonal block equation `X21 L11 + X22 L21 = 0` and the right-inverse certificate `L11 X11 = I`; it closes the exact formula and computed-delta wrapper, not the source instability analysis.
- The new Problem 14.10 theorem states the determinant-independence condition as `adj(A)_{ji}=0`. For a nonsingular matrix this is equivalent to the corresponding inverse-entry condition after multiplying by the nonzero determinant factor.
- The new p.279 `psi(A)` definitions expose both the nonnegative condition-number surface with denominator `|det(A)|` and the signed raw displayed ratio. The report treats the missing absolute value in the printed display as an implicit convention/typo audit, not as license to state a signed quantity as a condition number.
- The new Problem 14.11 theorems close Hadamard's determinant inequality and the lower bound `1 <= psi(A)` for nonsingular matrices by reusing the Chapter 9 Gram determinant theorem. They also prove equality when rows are pairwise orthogonal; the converse/equivalence side of the equality characterization remains open.
- The new Problem 14.12(a) theorem assumes an exact `A^T = QR` certificate, orthogonality of `Q`, and upper triangularity of `R`. These are source QR/domain assumptions; the theorem does not assert existence or algorithmic computation of QR factors. The new `U(1)` theorem uses exact row-norm and determinant algebra for the already defined Chapter 8 stress matrix. The Pei matrix theorem first proves the repository-convention formula with `|det(A)|` in the denominator under `0 < n` and `alpha != 1`, then proves the Appendix A unsigned denominator under `1 < alpha`; the sign/domain assumptions are explicit and no QR existence or stability theorem is used.
- The new Problem 14.13 source theorem constructs the printed nonnegative AM-GM family for dimensions `k + 2`, proves its product certificate `(kappa*|det(A)|/2)^2`, and proves its strict Frobenius-sum certificate by showing the omitted last singular-value square is positive. This removes the previous proof-artifact `z` hypothesis at the source-facing GEJ surface. The one-dimensional endpoint is not separately wrapped because the source AM-GM family is the `n >= 2` construction.
- The new Method D theorems close the exact algebra for (14.20)--(14.22) by exposing explicit product, LU, and triangular-inverse residual deltas. They do not yet derive the printed (14.23) coefficient from those componentwise budgets; `higham14_eq14_23_methodD_left_residual_bound` remains a conditional final-bound wrapper.
- The new (14.34) determinant theorems include the no-pivot/unit-lower LU core, the direct and source-oriented signed row-permuted products, and the row-permuted absolute-value product.
- The new Hyman theorems close exact algebra only: the block LU factorization assumes the source inverse certificate `T⁻¹T = I`; the original determinant formula is stated through an explicit row-permutation sign. They do not close Problem 14.14's floating-point backward-error or diagonal-scaling claims.
- The new Problem 14.7 theorems assume the appropriate inverse side explicitly (`IsRightInverse` for a row of ones, `IsLeftInverse` for a column of ones); these are source/domain assumptions, not proof artifacts.
- Existing Method 2, Method 2C, Method D final-bound, and GJE theorem surfaces still include hypotheses that are essentially the missing algorithmic analyses. They are recorded as conditional interfaces and do not close the source rows.
- Existing `O(u^2)` source statements are not fully modeled unless a theorem explicitly exposes a first-order wrapper; the report does not count asymptotic endpoints as closed.

## Weak-component and bottleneck summary

- Weak components: all floating-point residual/stability interfaces, GJE composition wrappers, and documentation completion claims.
- Active bottleneck: no red bottleneck yet for Chapter 14. The current main blocker is initial missing foundation work rather than repeated failed proof attempts.

## Verification

- Commands run so far:
  - `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean`
  - `lake env lean LeanFpAnalysis/FP/Algorithms/GaussJordan.lean`
  - `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion`
  - `lake build LeanFpAnalysis.FP.Algorithms.GaussJordan`
  - `git diff --check`
  - stale source-label scan for `Chapter 13`, `§13`, and equation/theorem label variants in the touched Lean files
  - marker scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` over the touched Chapter 14 Lean files
  - focused `#check` file for the two new Problem 14.7 theorems
  - focused `#print axioms` file for the two new Problem 14.7 theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.3 residual-ratio theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.4 residual-ratio family theorem
  - focused `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion` after adding the signed (14.34) parity wrappers
  - stdin focused `#check`/`#print axioms` run for the new signed (14.34) parity wrappers
  - focused `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion` after adding the p.279 `psi(A)` definitions
  - stdin focused `#check`/`#print axioms` run for the new p.279 `psi(A)` definitions and wrappers
  - `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` before reusing the Hadamard determinant theorem
  - focused `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion` after adding the Problem 14.11 Hadamard wrappers and equality direction
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.11 Hadamard wrappers and equality direction
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 right-residual theorem
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 left-residual theorem
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 right and left forward-error theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 first-order replacement and envelope-comparison theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.10 determinant-independence theorems
  - focused module build after adding the Method 2B exact (14.14) block-update wrappers
  - stdin focused `#check`/`#print axioms` run for the new Method 2B (14.14) declarations
  - focused module build after the new (14.34) determinant wrappers
  - focused `#check`/`#print axioms` run for the new pivoted absolute-value (14.34) wrapper
  - focused module build after adding the Hyman exact block LU and determinant wrappers
  - stdin focused `#check`/`#print axioms` run for the new Hyman exact block LU and determinant wrappers
  - focused module build after adding the Method D exact (14.20)--(14.22) wrappers
  - stdin focused `#check`/`#print axioms` run for the new Method D (14.20)--(14.23) declarations
  - focused module build after adding the Problem 14.12 QR formula wrappers
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.12 QR formula wrappers
  - focused module build after adding the Problem 14.12(b) `U(1)` closed form
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.12(b) `U(1)` theorem
  - focused module build after adding the Problem 14.12(b) Pei matrix closed form
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.12(b) Pei matrix declarations
  - `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` after adding the Problem 14.13 AM-GM support layer
  - `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion` after adding the Problem 14.13 AM-GM support layer
  - focused `#check`/`#print axioms` run for the new Problem 14.13 AM-GM and unit-row support declarations
  - `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` after adding the Problem 14.13 norm-side SVD bridge
  - `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion` after adding the Problem 14.13 norm-side SVD bridge
  - focused `#check`/`#print axioms` run for the new Problem 14.13 norm-side SVD bridge declarations
  - `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` after adding the Problem 14.13 determinant-product bridge
  - `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion` after adding the Problem 14.13 determinant-product bridge
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.13 determinant-product bridge declarations
  - stdin focused lookup `#check` run for the six new Problem 14.13 determinant-product declarations under `open LeanFpAnalysis.FP`
  - `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` after adding the Problem 14.13 source AM-GM family and GEJ theorem
  - `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion` after adding the Problem 14.13 source AM-GM family and GEJ theorem
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.13 source AM-GM family and GEJ theorem declarations
  - `git diff --check`
  - anchored conflict-marker scan over the touched Lean, report, inventory, ledger, lookup, and example files
  - unfinished-proof/placeholder scan over `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean`
  - `lake env lean examples/LibraryLookup.lean`
- Result: `LeanFpAnalysis.FP.Algorithms.MatrixInversion` builds after the Problem 14.13 AM-GM, norm-side SVD, determinant-product, and source-family GEJ additions; focused module builds pass before and after upstream integration and after the Problem 14.3, Problem 14.4, Problem 14.5 residual/forward/first-order, Problem 14.10, p.279 `psi(A)`, Problem 14.11 inequality/equality-direction, Problem 14.12(a), Problem 14.12(b) `U(1)`, Problem 14.12(b) Pei, Problem 14.13 AM-GM/norm-side SVD/determinant-product/source-family GEJ support, Method 2B (14.14), Method D (14.20)--(14.23), (14.34), and Hyman (14.35)--(14.36) additions; `git diff --check` passes; anchored conflict-marker and unfinished-proof scans over the touched files are clean; focused `#check` and axiom checks pass.
- New theorem axiom surface: the new Problem 14.3, Problem 14.4, Problem 14.5 residual/forward/first-order, Problem 14.7, Problem 14.10, p.279 `psi(A)`, Problem 14.11 inequality/equality-direction, Problem 14.12(a) QR formula, Problem 14.12(b) `U(1)` formula, Problem 14.12(b) Pei formula, Problem 14.13 AM-GM/unit-row/norm-side SVD/determinant-product/source-family GEJ support, Method 2B (14.14), Method D (14.20)--(14.23), (14.34), and Hyman (14.35)--(14.36) theorems use only the standard Mathlib axioms reported by Lean (`propext`, `Classical.choice`, `Quot.sound`) when checked; the determinant/LU wrappers inherit existing determinant/permutation/LU determinant facts.
- Known verification issue: the full `examples/LibraryLookup.lean` run aborts with a stack overflow / exit 134 after producing large lookup output. Focused lookups for the new declarations pass, so this is recorded as a full-example scale issue rather than a failed declaration lookup.
- New versus pre-existing warnings: a new unused-simp warning appeared during initial Problem 14.7 proof and was removed; the focused HighamChapter9 replay emits pre-existing `Fin.coe_castLE` deprecation / unused-simp warnings and a `ring_nf` tactic suggestion, unrelated to the Chapter 14 wrappers.

## GitHub synchronization

- Local branch: main
- Latest remote base integrated: `origin/main` fast-forwarded from `0af482e1` to `8411b4d2` before theorem design, then merged `57d02bfd`, `5e10aea0`, `e6c81dbe`, and `c03d362f` after local Chapter 14 milestones; upstream `45c2e8b3` was present before the determinant-product milestone; upstream `3cf69465` was merged cleanly before the Problem 14.5 forward-use push; upstream `ecb2d4e2` was present before the Problem 14.5 first-order comparison push; Problem 14.4 residual-ratio family was pushed as `bed137a7`; upstream `38e9a09f` was merged cleanly before the signed determinant parity push; upstream `4c5a45c3` and `7d4cc0e1` were merged cleanly before the p.279 `psi(A)` push; upstream `d5f5c94b` was merged cleanly before the Hyman/Problem 14.11 push; upstream `93a33335` was merged cleanly in `6f12b5df` before the equality-direction push; no additional upstream changes were present before the Method D exact-algebra push; upstream `20999150`/`57a1679d` was merged cleanly in `78ff0bda` before the Method 2B block-update push; upstream `276d1501` was merged cleanly in `83b3cf51` before the Problem 14.12(a) QR-formula push; upstream `f260f88c` was fast-forwarded before the Problem 14.12(b) `U(1)` theorem design; upstream `214d626f`/`44debfcf` were merged cleanly in `401b5468` before the Problem 14.12(b) `U(1)` push; upstream `b9217bc4` was merged cleanly in `b6147ac6` before the Problem 14.12(b) Pei push; no additional upstream changes were present before the Problem 14.13 AM-GM support push; no additional upstream changes were present before the Problem 14.13 norm-side SVD bridge push; upstream `0b7b3812` was merged cleanly in `b93edc09` before the Problem 14.13 determinant-product bridge push.
- Milestone commits and split prefixes: `6939f36a` (`Split 3A: start Ch14 matrix inversion inventory`), `63347956` (`Split 3A: formalize Ch14 residual ratio`), `90a50b13` (`Split 3A: formalize Ch14 inverse exercises`), `3d01123b` (`Split 3A: clean Ch14 inverse exercise report`), `a2234884` (`Split 3A: formalize Ch14 determinant product`), `1ce54698` (`Split 3A: formalize Ch14 inverse residual completion`), `6e01df40` (`Split 3A: formalize Ch14 inverse forward use`), `24c19e41` (`Split 3A: formalize Ch14 inverse first-order comparison`), `bed137a7` (`Split 3A: formalize Ch14 residual ratio family`), `303b5db6` (`Split 3A: formalize Ch14 signed determinant parity`), `1dc0cb20` (`Split 3A: formalize Ch14 Hadamard psi`), `faa13041` (`Split 3A: formalize Ch14 Hyman determinant identities`, including the Problem 14.11 Hadamard inequality wrappers), `b98441be` (`Split 3A: formalize Ch14 Hadamard equality direction`), `7dd91e49` (`Split 3A: formalize Ch14 Method D exact algebra`), `023c565e` (`Split 3A: formalize Ch14 Method 2B block update`), `86823623` (`Split 3A: formalize Ch14 Hadamard QR formula`), `a64d3a52` (`Split 3A: formalize Ch14 U one Hadamard psi`), `6ab6b506` (`Split 3A: formalize Ch14 Pei Hadamard psi`), `95089b89` (`Split 3A: formalize Ch14 GEJ AM-GM support`), `e24d7d05` (`Split 3A: formalize Ch14 GEJ SVD norm bridge`), `3852711b` (`Split 3A: formalize Ch14 GEJ determinant bridge`)
- Local merge commits before report-sync updates: `24f75fa4`, `30c972c4`, `3fd44412`, `ff90ea53`, `dc77d6aa`, `61d87f6a`, `4f4c45d8`, `4078c720`, `0a5a75fc`, `6f12b5df`, `78ff0bda`, `83b3cf51`, `401b5468`, `b6147ac6`, `b93edc09`
- Pushed to origin/main: yes, through `b93edc09` before this push-record update
- Merge/conflict resolution: clean `ort` merges; latest upstream changed `LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16Spectrum.lean` and `docs/source_coverage/higham_ch16.md` before the Problem 14.13 determinant-product bridge push
- New upstream imports or exported contracts: Chapter 14 imports `LeanFpAnalysis.FP.Algorithms.HighamChapter8` for the `U(1)` stress-matrix family and `LeanFpAnalysis.FP.Algorithms.HighamChapter9` for the Hadamard determinant inequality reuse; exported wrappers cover Problem 14.11 Hadamard inequality/`psi(A) >= 1`, Problem 14.12(a) QR formula, Problem 14.12(b) `U(1)` closed form, Problem 14.12(b) Pei matrix closed form, Problem 14.13 AM-GM/unit-row/norm-side SVD/determinant-product/source-family GEJ support, Method 2B exact (14.14) block-update algebra, Method D exact (14.20)--(14.22) algebra plus conditional (14.23), and exact Hyman (14.35)--(14.36) determinant algebra.

## Documentation

- Inventory path: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`
- Not-proved ledger path: `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`
- Proof-source ledger path: `docs/chapter14/CHAPTER14_PROOF_SOURCE_LEDGER.md`
- Theorem note or PDF: not generated

## Open issues

- Source-visible Problem 14.14 is omitted from the shared chapter problem ledger but appears in the PDF and Appendix A Split 3A ownership list. The inventory includes it.
- Existing `CondEstimation.lean` and `LU/TridiagonalCond.lean` carry older `§14` labels for material now assigned to Chapter 15 by the split plan. They were not changed in this milestone.
- Full source-strength completion of Chapter 14 requires proving several currently conditional floating-point interfaces, the Hadamard equality converse, the singular-value perturbation problem row, and Hyman's backward-error exercise.
