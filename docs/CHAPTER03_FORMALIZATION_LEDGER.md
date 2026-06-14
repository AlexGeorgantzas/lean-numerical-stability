# Chapter 3 Formalization Ledger

Source: `References/Chapter03.pdf` (Higham, Chapter 3 excerpt, 17 PDF pages,
printed pages 68--84).

Status: **PASS for theorem-bearing Chapter 3 rows** as of this audit.  The
repository now contains matching Lean theorem surfaces for the excerpt's
printed lemmas, algorithms, stability/error bounds, normwise corollaries, and
exercise-level product refinements that carry mathematical obligations.
Rows marked `PROSE` below are expository or bibliographic text rather than
local theorem targets.

This ledger is the authoritative gate for the local `Chapter03.pdf` excerpt.
A row is closed only when a matching local Lean theorem proves the mathematical
claim, not merely when later code uses an analogous idea.

## Coverage Summary

| Source location | Claim/result | Lean status | Current Lean surface | Gap / next action |
|---|---|---:|---|---|
| p. 68, eqs. (3.1)--(3.2) | Left-to-right dot-product expansion with local rounding factors and accumulated `(1 +/- delta)` powers. | CLOSED | `fl_dotProduct`, `sumSuffixErrorProduct`, `foldl_add_mul_one_add_suffix_expansion`, `fl_sum_error_init_suffix_expansion`, `dotProduct_factor_expansion_succ` | Closed for positive-length left-to-right dot products. Lean exposes one local multiplication factor per product term and one local addition factor per accumulation step; the first term carries all addition factors, and each later term carries the suffix of addition factors from the step where it enters the accumulator. |
| p. 69, Lemma 3.1 | Signed product lemma: if `|delta_i| <= u`, `p_i = +/-1`, and `n*u < 1`, then `prod_i (1+delta_i)^{p_i} = 1 + theta_n`, `|theta_n| <= gamma_n`. | CLOSED | `gamma`, `gammaValid`, `prod_error_bound`, `prod_signed_error_bound` | Closed with a Boolean selector `neg i` for the source exponent `p_i = -1`; false means `p_i = +1`. This avoids a separate integer-power encoding while proving the signed-factor content under the source `gammaValid fp n` guard. |
| p. 69, eq. (3.3) | Dot product as exact sum with componentwise perturbed multiplicative factors. | CLOSED | `dotProduct_backward_error` | Source-faithful consequence is proved for the implemented left-to-right dot product. Comments should cite Higham section 3.1, not 3.5. |
| p. 69, eq. (3.4) | Dot-product backward stability by perturbing either `x` or `y`. | CLOSED | `dotProduct_backward_stable_x`, `dotProduct_backward_stable_y`, `dotProduct_isRelBackwardStable` | Closed for the modeled left-to-right dot product. General "any order of evaluation" is not a separate permutation theorem. |
| p. 69, eq. (3.5) | Dot-product forward error `|x^T y - fl(x^T y)| <= gamma_n |x|^T |y|`. | CLOSED | `dotProduct_error_bound` | Closed for the modeled left-to-right dot product. |
| pp. 69--70 | No-guard-digit model also gives (3.3)--(3.5). | CLOSED | `dotProduct_backward_error`, `dotProduct_backward_stable_x`, `dotProduct_backward_stable_y`, `dotProduct_error_bound` | Closed at the Chapter 3 abstraction level: these dot-product theorems assume only the repository's standard operation model fields in `FPModel` and do not use a guard-digit hypothesis. Any concrete no-guard arithmetic that satisfies the same `model_add`/`model_mul` fields instantiates the proofs. Deriving those fields from a concrete no-guard hardware model remains a Chapter 2 finite-format/model obligation, not a separate Chapter 3 dot-product proof. |
| p. 70 | Two-piece dot product bound `gamma_{n/2+1} |x|^T |y|`, k-piece bound `gamma_{n/k+k-1}`, and optimal `k ~= sqrt(n)`. | CLOSED | `fl_blockDotProduct`, `blockDotProduct_backward_error`, `blockDotProduct_error_bound`, `twoPieceDotProduct_error_bound`, `blockDotProduct_real_index_decomposition`, `blockDotProduct_real_index_ge_optimum`, `blockDotProduct_real_index_at_sqrt` | Closed for equal block sizes: with `q+1` pieces of length `b`, Lean proves the componentwise backward and forward bounds with radius `gamma fp (b+q)`, i.e. `gamma_{n/k+k-1}` for `n=b*k`, `k=q+1`. The two-piece corollary gives `gamma fp (b+1)`, matching `gamma_{n/2+1}`. The balancing rule is formalized as the continuous relaxation identity `n/k+k-1 = 2*sqrt(n)-1 + (k-sqrt(n))^2/k` and its optimum at `sqrt(n)`. Unequal/remainder block partitions are not separately claimed. |
| p. 70 | Pairwise summation dot-product bound `gamma_{ceil(log2 n)+1} |x|^T |y|`. | CLOSED | `fl_sumTreeDotProduct`, `sumTreeDotProduct_error_bound`, `balancedTreeDotProduct_error_bound`, `fl_clog2PairwiseDotProduct`, `clog2PairwiseDotProduct_error_bound` | Closed for product-first pairwise dot products. Any supplied binary summation tree of depth `d` gives radius `gamma_{d+1}`; the balanced `2^r` corollary gives `gamma_{r+1}`; and the arbitrary-length theorem pads to `2^(Nat.clog 2 n)` and proves the source `gamma_{ceil(log2 n)+1}` forward bound. |
| pp. 70--71 | Extended-precision inner product bound with inner unit roundoff `u_e` and final unit roundoff `u`. | CLOSED | `FinalRoundingModel`, `fl_extendedDotProduct`, `extendedDotProduct_error_from_rounded_exact`, `extendedDotProduct_error_bound`, `fl_exactMulDotProduct`, `exactMulDotProduct_backward_error`, `exactMulDotProduct_error_bound`, `fl_extendedExactMulDotProduct`, `extendedExactMulDotProduct_error_from_rounded_exact`, `extendedExactMulDotProduct_error_bound` | Closed with an explicit unary final-rounding model: the inner product is computed by an inner `FPModel`, then a supplied `FinalRoundingModel u finalRound` rounds the accumulated value to working precision. Lean proves both the rounded-exact comparison `|fl(final) - (x^T y)(1+delta)| <= (1+u)*gamma_e*|x|^T|y|` and the displayed absolute bound `u*|x^T y| + (1+u)*gamma_e*|x|^T|y|`. The exact-product variant charges only `gamma_e(n-1)`, formalizing the source parenthetical that exact extended products reduce the theta subscripts by one. The assumption `u_e < u` is a usage/domain condition and is not needed for the inequality itself. |
| p. 71, eq. (3.6) | Outer product entrywise forward error: `Ahat = x y^T + Delta`, `|Delta| <= u |x y^T|`. | CLOSED | `fl_outerProduct`, `outerProduct_error_bound`, `outerProduct_error_decomposition` | The source-style explicit perturbation matrix and componentwise bound are closed. |
| p. 71 | Outer product is not backward stable in general. | CLOSED | `rankOne_outerProduct2x2_det_zero`, `outerProductCounterexampleMatrix_not_rank_one`, `fl_outerProduct_counterexample_eq`, `fl_outerProduct_counterexample_not_global_backward` | Closed by an explicit 2-by-2 counterexample: a valid `FPModel` rounds only `2*2` upward, so `fl_outerProduct [1,2] [1,2]^T` has nonzero determinant and cannot equal `(x+Delta x)(x+Delta y)^T` for any perturbations at all. The existing `outerProduct_backward_error` remains only rowwise/column-indexed. |
| pp. 71--72, section 3.2 | Purpose of rounding error analysis, role of constants, a posteriori bounds. | PROSE | N/A | Expository guidance; no theorem obligation unless the project adds a formal taxonomy of error-analysis goals. |
| pp. 72--73, Algorithm 3.2 | Running error analysis for dot products: computed `s` and `mu` satisfy `|s - x^T y| <= mu`. | CLOSED | `runningErrorMu`, `fl_runningDotProductProduct`, `exactDotProductPrefixNat`, `fl_runningDotProductPrefixNat`, `exactDotProductPrefixState`, `fl_runningDotProductState`, `fl_runningDotProduct`, `runningError_bound_from_local_errors`, `fl_runningDotProduct_error_bound_from_inverse_models` | Closed for the concrete Algorithm 3.2 loop `z = fl_mul x_i y_i; s = fl_add s z; mu += |s|+|z|`, under the operation-level inverse-model hypotheses used by the source's modified model (2.5). Lean constructs the stored product and partial-sum trace, proves the source recurrence, identifies the final exact prefix with `sum_i x_i*y_i`, and derives `|fl_runningDotProduct - x^T y| <= u*runningErrorMu`. This is not a pure consequence of the repository's primitive standard `FPModel`; the p.73 model row records the remaining derivation/supply obligation for inverse-model witnesses. |
| p. 73, running-operation model | Modified model form `|x op y - fl(x op y)| <= u |fl(x op y)|`. | CLOSED | `inverseRelErrorModel`, `inverseRelErrorModel_abs_exact_sub_computed_le`, `FloatingPointFormat.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange`, `FloatingPointFormat.finiteNormalFl_inverseRelErrorModel` | Closed at both layers needed by the source: the algebraic inverse model (2.5) implies the computed-denominator absolute-error form, and finite-normal-range nearest rounding supplies the inverse model with `fmt.unitRoundoff`. The generic abstract `FPModel` still exposes only the standard `(exact)*(1+delta)` fields, so concrete Algorithm 3.2 instantiations must either pass operation-level inverse-model witnesses or use a finite-normal rounding implementation such as `finiteNormalFl`. |
| p. 73, eq. (3.7) | First-order big-O rewrite of (3.5). | CLOSED | `dotProduct_error_bound`, `gamma_eq_linear_plus_quadratic_remainder` | Closed as an exact bound plus explicit first-order/remainder split: `dotProduct_error_bound` gives the source `gamma_n |x|^T|y|` inequality, and `gamma_eq_linear_plus_quadratic_remainder` rewrites `gamma_n` as `n*u + (n*u)^2/(1-n*u)`. Literal asymptotic notation is not needed for the theorem-bearing content. |
| p. 74, Lemma 3.3 | Gamma/theta algebra rules. | CLOSED | `gamma_mul`, `gamma_div_le_branch`, `gamma_div_gt_branch`, `gamma_div`, `gamma_prod_le`, `gamma_nsmul_le`, `gamma_add_u_le`, `gamma_sum_le` | Closed for the source displayed rules under the repository's non-strict `|theta_k| <= gamma_k` convention. `gamma_div_le_branch` proves the sharp quotient branch `(1+theta_k)/(1+theta_j) = 1+theta_{k+j}` for `j <= k`; `gamma_div_gt_branch` packages the `j > k` branch with radius `gamma_{k+2j}`. |
| pp. 74--75, Lemma 3.4 | Product bound under `n*u < 0.01`: `prod_i (1+delta_i) = 1 + eta_n`, `|eta_n| < 1.01 n u`. | CLOSED | `prod_one_add_delta_eq_one_add_eta_bound_101`, `prod_one_add_delta_eq_one_add_eta_bound_101_le` | Closed as the source scalar product lemma for positive `n`, strict local bounds `|delta_i| < u`, and `(n : Real)*u < 0.01`; the `_le` variant supplies the repository `FPModel`-compatible non-strict local bound `|delta_i| <= u` under the explicit radius assumption `0 < u`. Supporting lemmas prove the `(1-u)^n`/`(1+u)^n` product squeeze, the exponential envelope, and the numerical cap `exp(x)-1 < 1.01*x` for `0 < x < 0.01`. |
| p. 75, eq. (3.8) | Dot-product forward bound with `1.01 n u`. | CLOSED | `dotProductLocalFactor`, `dotProduct_factor_expansion_sum_succ`, `dotProductLocalFactor_abs_sub_one_le_101`, `dotProduct_error_bound_101_succ` | Closed for positive-length left-to-right dot products under the repository's non-strict `FPModel` local-error surface. If `0 < fp.u` and `(n+1)*fp.u < 0.01`, Lean proves `|fl_dotProduct - x^T y| <= 1.01*(n+1)*fp.u*sum_i |x_i||y_i|`. The theorem uses a non-strict `<=` conclusion because zero-weight terms make a globally strict `<` bound impossible without extra nondegeneracy assumptions. |
| p. 75, eq. (3.9) | Stewart relative-error counter `<k>` and rules `<j><k> = <j+k>`, `<j>/<k> = <j+k>`. | CLOSED | `relErrorCounter`, `relErrorCounter_abs_sub_one_le_gamma`, `relErrorCounter_mul`, `relErrorCounter_inv`, `relErrorCounter_div` | Closed as a product-level predicate using the same positive/reciprocal Boolean selector as Lemma 3.1. The division rule carries the necessary `fp.u < 1` guard so reciprocal factors are nonzero. |
| p. 76 | Olver relative precision notation and symmetry/additivity. | CLOSED | `relPrecision`, `relPrecision_refl`, `relPrecision_symm`, `relPrecision_trans`, `pryceOne`, `pryceOne_iff`, `relPrecision_same_sign_of_nonzero` | Closed for the scalar relation `y = exp(delta) x`, `|delta| < a`, including reflexivity for positive radius, symmetry, additive chaining, Pryce's `1(a)` notation, and the same-sign consequence for nonzero scalars. Vector/matrix relative precision extensions mentioned bibliographically remain outside this scalar paragraph. |
| p. 76, eq. (3.10) | Matrix-vector backward error `yhat = (A+Delta A)x`, `|Delta A| <= gamma_n |A|`. | CLOSED | `fl_matVec`, `matVec_backward_error` | Closed for rowwise dot-product implementation. |
| p. 76, eq. (3.11) | Matrix-vector forward error `|y-yhat| <= gamma_n |A||x|`. | CLOSED | `matVec_error_bound` | Closed componentwise. |
| p. 77 | Matrix-vector normwise bounds for `p = 1, infinity`. | CLOSED | `matVec_error_bound_infNorm`, `matVec_error_bound_oneNorm`, `matVec_error_bound_infNormRect`, `matVec_error_bound_oneNormRect` | The square-matrix and rectangular infinity-norm and 1-norm corollaries are proved from (3.11). The rectangular theorems use `infNormRect` for maximum absolute row sum and `oneNormRect` for maximum absolute column sum; vector 1-norms are written explicitly as finite sums. |
| p. 77 | Sdot and saxpy loop-order equivalence. | CLOSED | `fl_matVecSaxpyInit`, `fl_matVecSaxpy`, `fl_matVecSaxpyInit_apply`, `fl_matVecSaxpy_eq_sdot` | Closed by defining the column-oriented saxpy vector fold and proving it is extensionally equal to the existing rowwise `fl_matVec`/sdot implementation. The first saxpy update from zero is exact by `FPModel.fl_add_zero`, matching the repository's tight dot-product convention. |
| pp. 77--78, eq. (3.12) | Matrix-matrix componentwise forward error `|C-Chat| <= gamma_n |A||B|`. | CLOSED | `fl_matMul`, `matMul_error_bound` | Closed for columnwise product via `fl_matVec`. |
| p. 78 | Matrix-matrix columnwise backward error. | CLOSED | `matMul_backward_error_col` | Closed as a columnwise theorem with per-column `Delta A_j`. |
| p. 78 | No single backward error for `Chat` as a whole; Problem 3.5 reference. | CLOSED | `matMulCounterexampleFP_gammaValid_one`, `fl_matMul_counterexample_eq`, `fl_matMul_counterexample_not_global_backward_A`, `fl_matMul_counterexample_not_global_backward_A_gamma` | Closed by a concrete `1 x 1` times `1 x 2` matrix product. The valid model has `u = 1/10`, rounds only `1*2` upward, and computes `[1, 11/5]` from `[1] * [1, 2]`; the first column forces a common perturbation of `A` to be zero while the second forces it to be `1/10`, so no common `Delta A` exists, let alone one satisfying the source-style `gamma_1` radius. |
| p. 78 | Matrix-matrix normwise bounds for `p = 1,2,F`. | CLOSED | `matMul_error_bound_frobNorm_majorant`, `matMul_error_bound_rectOpNorm2Le_majorant`, `matMul_error_bound_oneNorm`, `matMul_error_bound_oneNormRect`, `matMul_error_bound_infNormRect`, `matMul_error_bound_frobNormRect`, `matMul_error_bound_frobNorm`, `matMul_error_bound_opNorm2Le_frob` | The Frobenius norm of the forward error is bounded by `gamma_n || |A||B| ||_F` for rectangular shapes. The square and rectangular product-norm corollaries are closed for `p = 1` and `p = F`; a rectangular maximum-row-sum product bound is also proved. The `p = 2`/vector-action majorant is closed in the repository's predicate form: if the nonnegative factors `|A|` and `|B|` have `rectOpNorm2Le` certificates `alpha` and `beta`, then the error matrix has certificate `gamma_n*alpha*beta`. The Frobenius fallback remains as a coarser convenience. No supremum-valued spectral norm function is introduced for legacy function-shaped matrices. |
| p. 78 | Sensitivity/sharpness of (3.12): perturbation can attain `u(|A||B|)_{ij}`. | CLOSED | `signedMagnitudeForPivot`, `matMulSharpDeltaA`, `matMulSharpDeltaB`, `matMul_forward_bound_sharp_A`, `matMul_forward_bound_sharp_B` | Closed constructively under the repository's non-strict componentwise perturbation convention: for any entry `(i,j)` and `0 <= u`, Lean builds a row perturbation of `A` or a column perturbation of `B` with `|Delta A| <= u|A|` or `|Delta B| <= u|B|` and proves the selected entry error is exactly `u * sum_k |A_ik||B_kj|`. |
| pp. 78--80, eqs. (3.13a)--(3.13c), Lemma 3.5 | Complex add/sub, multiply, and divide error model from real arithmetic; constants `u`, `sqrt(2) gamma_2`, `sqrt(2) gamma_4`; overflow-avoiding division variant with `sqrt(2) gamma_7`. | CLOSED | `complexRelErrorModel`, `fl_complexAdd_rel_error_model`, `fl_complexSub_rel_error_model`, `fl_complexMul_rel_error_model`, `fl_complexDiv_rel_error_model`, `smithComplexDivBranchCExact_eq_div`, `smithComplexDivBranchDExact_eq_div`, `fl_smithComplexDivBranchC_rel_error_model`, `fl_smithComplexDivBranchD_rel_error_model`, `fl_smithComplexDiv_rel_error_model` | Addition and subtraction are closed for equation (3.13a): two rounded real component operations satisfy the source complex relative-error model with radius `fp.u`. Multiplication is closed for equation (3.13b): four rounded real products plus the final rounded add/sub satisfy the source relative-error model with radius `sqrt(2)*gamma fp 2` under `gammaValid fp 2`. Division is closed for the displayed proof model of equation (3.13c): rounded real numerator and denominator subexpressions, followed by the displayed real quotients, satisfy the source relative-error model with radius `sqrt(2)*gamma fp 4` under `gammaValid fp 4` and nonzero denominator. The exact Smith branch formulas from Chapter 25 equation (25.1), using `r = d/c` or `r = c/d`, are proved equal to ordinary complex division under the selected nonzero scale. For the rounded Smith branches, Lean proves the scalar `gamma_3` subexpression bounds for both denominators and all four numerators, the absolute-denominator scalar bridge from these bounds to one rounded quotient with `gamma_7`, all four branch componentwise `gamma_7` quotient bounds, branch normwise bounds, branch relative-error models, and the combined selector theorem `fl_smithComplexDiv_rel_error_model` with radius `sqrt(2)*gamma fp 7` under `gammaValid fp 7` and `y != 0`. The selector follows the Smith branch convention by using the `c`-scale branch when `|y.im| <= |y.re|` and the `d`-scale branch otherwise. Existing C-star matrix files remain unrelated to this scalar rounded-arithmetic model. |
| pp. 80--81, Lemma 3.6 | Normwise perturbation bound for products of perturbed matrices. | CLOSED | `matSeqProd_norm_perturbed_le_scalar`, `matSeqProd_normwise_perturbation_bound` | Closed for finite left-to-right products of square real matrices under an abstract consistent-norm interface: nonnegativity, `N(I) <= 1`, `N(0) <= 0`, subadditivity, and submultiplicativity. If `N(Delta X_j) <= delta_j N(X_j)` and `0 <= delta_j`, Lean proves `N(prod_j (X_j+Delta X_j)-prod_j X_j) <= (prod_j(1+delta_j)-1) prod_j N(X_j)`. |
| p. 81, Lemma 3.7 | Componentwise perturbation bound for products of perturbed matrices. | CLOSED | `matSeqProd`, `scalarSeqProd`, `matSeqProd_abs_perturbed_le_scalar_abs`, `matSeqProd_componentwise_perturbation_bound` | Closed for finite left-to-right products of square real matrices: if `|Delta X_j| <= delta_j |X_j|` and `0 <= delta_j`, Lean proves the componentwise product error is bounded by `(prod_j (1+delta_j)-1) * prod_j |X_j|`. |
| p. 81, Lemma 3.8 | Rank-1 update `yhat = fl(x - a(b^T x))` error bound and 2-norm corollary. | CLOSED | `rankOneUpdateExact`, `fl_rankOneUpdate`, `rankOneUpdateAbsBudget`, `fl_rankOneUpdate_componentwise_error_bound`, `rankOneUpdateAbsBudget_norm2_le`, `fl_rankOneUpdate_error_bound_vecNorm2` | Closed for the concrete routine `t = fl_dotProduct b x; w_i = fl_mul a_i t; y_i = fl_sub x_i w_i`. Lean proves the source componentwise bound `|Delta y| <= gamma_{n+3}(I+|a||b^T|)|x|`, via `rankOneUpdateAbsBudget`, and the displayed Euclidean-norm corollary `||Delta y||_2 <= gamma_{n+3}(1+||a||_2||b||_2)||x||_2`. |
| pp. 82--83, section 3.8 | First-order Jacobian framework for forward/backward error analysis. | CLOSED | `firstOrderStageError`, `firstOrderForwardError`, `firstOrderForwardBudget`, `firstOrderForwardError_vecNorm2_le_budget`, `firstOrderSelectedOutputError`, `firstOrderSelectedOutputError_vecNorm2_le`, `firstOrderBackwardEquation`, `IsMinimumNormFirstOrderBackwardSolution`, `ComponentwiseFirstOrderBackwardFeasible`, `IsMinimumComponentwiseFirstOrderBackwardScale`, `firstOrderBackward_minimumNorm_solution`, `firstOrderBackward_minimumComponentwise_solution` | Closed at the section's intended first-order algebra layer. Lean formalizes the staged recurrence `e_{k+1}=J_k e_k+local_k`, proves a Euclidean normwise forward-error bound from per-stage Jacobian and local-error budgets, applies a final selection/projection matrix, and exposes the backward-analysis equation `J_f Delta a = e` together with norm-minimal and componentwise-minimal solution predicates. The differentiability/Taylor hypotheses that justify a particular algorithm's Jacobians remain visible to the caller, as in the source prose. |
| pp. 83--84, section 3.9 | Other approaches to error analysis. | PROSE | N/A | Bibliographic/expository. |
| p. 84, section 3.10 | Notes, references, Ziv relative error measure, Problems 3.1--3.2 excerpt. | CLOSED/PROSE | `prod_error_bound`, `prod_signed_error_bound`, `real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two`, `prod_one_add_delta_eq_one_add_phi_bound_problem32` | The notes and references are bibliographic prose. Problem 3.1's signed-product form is closed by `prod_signed_error_bound`. Problem 3.2's all-positive-factor bound is closed for the repository's non-strict local-error convention: under `0 < n`, `0 < u`, `|delta_i| <= u`, and `(n : Real)*u < 2`, Lean proves `prod_i (1+delta_i) = 1+phi` with `|phi| < n*u/(1-n*u/2)`. |

## Current Closed Chapter 3 Lean Names

- `gamma`, `gammaValid`, `gamma_eq_linear_plus_quadratic_remainder`,
  `prod_error_bound`, `prod_signed_error_bound`
- `relErrorCounter`, `relErrorCounter_abs_sub_one_le_gamma`,
  `relErrorCounter_mul`, `relErrorCounter_inv`, `relErrorCounter_div`
- `relPrecision`, `relPrecision_refl`, `relPrecision_symm`,
  `relPrecision_trans`, `pryceOne`, `pryceOne_iff`,
  `relPrecision_same_sign_of_nonzero`
- `complexRelErrorModel`, `complexRelErrorModel_of_norm_error_le`,
  `fl_complexAdd`, `fl_complexSub`, `fl_complexMul`,
  `fl_complexAdd_normSq_error_le`,
  `fl_complexAdd_error_bound`, `fl_complexAdd_rel_error_model`,
  `fl_complexSub_normSq_error_le`, `fl_complexSub_error_bound`,
  `fl_complexSub_rel_error_model`, `fl_mul_sub_error_le_gamma2`,
  `fl_mul_add_error_le_gamma2`, `complex_mul_component_abs_terms_sq_le`,
  `fl_complexMul_normSq_error_le`, `fl_complexMul_error_bound`,
  `fl_complexMul_rel_error_model`, `fl_complexDivDen`, `fl_complexDivNumRe`,
  `fl_complexDivNumIm`, `fl_complexDiv`,
  `quotient_abs_error_le_gamma4_of_gamma2`,
  `fl_complexDivDen_error_le_gamma2`,
  `fl_complexDivNumRe_error_le_gamma2`,
  `fl_complexDivNumIm_error_le_gamma2`,
  `fl_complexDiv_re_error_le_gamma4`,
  `fl_complexDiv_im_error_le_gamma4`,
  `complex_div_component_abs_terms_sq_le`,
  `fl_complexDiv_re_exact_error_le_gamma4`,
  `fl_complexDiv_im_exact_error_le_gamma4`,
  `fl_complexDiv_normSq_error_le`, `fl_complexDiv_error_bound`,
  `fl_complexDiv_rel_error_model`, `quotient_abs_error_le_gamma6_of_gamma3`,
  `fl_quotient_abs_error_le_gamma7_of_gamma3`,
  `quotient_abs_error_le_gamma6_of_gamma3_absDen`,
  `fl_quotient_abs_error_le_gamma7_of_gamma3_absDen`,
  `fl_add_mul_div_error_le_gamma3`, `fl_sub_mul_div_error_le_gamma3`,
  `fl_mul_div_sub_error_le_gamma3`,
  `smithComplexDivBranchCExact`, `smithComplexDivBranchDExact`,
  `fl_smithComplexDivBranchCRatio`, `fl_smithComplexDivBranchCDen`,
  `fl_smithComplexDivBranchCNumRe`, `fl_smithComplexDivBranchCNumIm`,
  `fl_smithComplexDivBranchC`, `fl_smithComplexDivBranchDRatio`,
  `fl_smithComplexDivBranchDDen`, `fl_smithComplexDivBranchDNumRe`,
  `fl_smithComplexDivBranchDNumIm`, `fl_smithComplexDivBranchD`,
  `fl_smithComplexDivBranchCDen_error_le_gamma3`,
  `fl_smithComplexDivBranchCNumRe_error_le_gamma3`,
  `fl_smithComplexDivBranchCNumIm_error_le_gamma3`,
  `fl_smithComplexDivBranchDDen_error_le_gamma3`,
  `fl_smithComplexDivBranchDNumRe_error_le_gamma3`,
  `fl_smithComplexDivBranchDNumIm_error_le_gamma3`,
  `smithComplexDivBranchCDen_ne_zero`, `smithComplexDivBranchCDen_abs_eq`,
  `smithComplexDivBranchDDen_ne_zero`, `smithComplexDivBranchDDen_abs_eq`,
  `fl_smithComplexDivBranchC_re_error_le_gamma7`,
  `fl_smithComplexDivBranchC_im_error_le_gamma7`,
  `fl_smithComplexDivBranchD_re_error_le_gamma7`,
  `fl_smithComplexDivBranchD_im_error_le_gamma7`,
  `smithComplexDivBranchC_re_majorant_eq`,
  `smithComplexDivBranchC_im_majorant_eq`,
  `smithComplexDivBranchD_re_majorant_eq`,
  `smithComplexDivBranchD_im_majorant_eq`,
  `smithComplexDivBranchCExact_eq_div`, `smithComplexDivBranchDExact_eq_div`,
  `fl_smithComplexDivBranchC_normSq_error_le`,
  `fl_smithComplexDivBranchC_error_bound`,
  `fl_smithComplexDivBranchC_rel_error_model`,
  `fl_smithComplexDivBranchD_normSq_error_le`,
  `fl_smithComplexDivBranchD_error_bound`,
  `fl_smithComplexDivBranchD_rel_error_model`,
  `fl_smithComplexDiv`, `fl_smithComplexDiv_error_bound`,
  `fl_smithComplexDiv_rel_error_model`
- `gamma_mul`, `gamma_inv`, `gamma_div_le_branch`, `gamma_div_gt_branch`,
  `gamma_div`, `gamma_add_div_one_sub_gamma_le_of_le`, `gamma_prod_le`,
  `gamma_nsmul_le`, `gamma_add_u_le`, `gamma_sum_le`
- `prod_one_add_delta_bounds`,
  `prod_one_add_delta_abs_sub_one_le_exp_sub_one`,
  `real_exp_sub_one_lt_101_mul_of_pos_of_lt_cent`,
  `real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two`,
  `prod_one_add_delta_eq_one_add_eta_bound_101`,
  `prod_one_add_delta_eq_one_add_eta_bound_101_le`,
  `prod_one_add_delta_eq_one_add_phi_bound_problem32`
- `sumSuffixErrorProduct`, `sumSuffixErrorProduct_eq_prod_if`,
  `foldl_add_mul_one_add_suffix_expansion`,
  `fl_sum_error_init_suffix_expansion`, `fl_sum_error`,
  `fl_sum_error_init`, `fl_sum_error_tight`
- `fl_dotProduct`, `dotProductLocalFactor`,
  `dotProduct_factor_expansion_succ`, `dotProduct_factor_expansion_sum_succ`,
  `dotProductLocalFactor_abs_sub_one_le_101`,
  `dotProduct_error_bound_101_succ`, `dotProduct_backward_error`,
  `dotProduct_backward_stable_x`, `dotProduct_backward_stable_y`,
  `dotProduct_error_bound`, `dotProduct_isRelBackwardStable`
- `fl_blockDotProduct`, `blockDotProduct_backward_error`,
  `blockDotProduct_error_bound`, `twoPieceDotProduct_error_bound`,
  `blockDotProduct_real_index_decomposition`,
  `blockDotProduct_real_index_ge_optimum`,
  `blockDotProduct_real_index_at_sqrt`
- `FinalRoundingModel`, `finalRound_error_from_rounded_exact`,
  `finalRound_error_bound`, `fl_extendedDotProduct`,
  `extendedDotProduct_error_from_rounded_exact`,
  `extendedDotProduct_error_bound`, `fl_exactMulDotProduct`,
  `exactMulDotProduct_backward_error`, `exactMulDotProduct_error_bound`,
  `fl_extendedExactMulDotProduct`,
  `extendedExactMulDotProduct_error_from_rounded_exact`,
  `extendedExactMulDotProduct_error_bound`
- `fl_sumTreeDotProduct`, `sumTreeDotProduct_backward_error`,
  `sumTreeDotProduct_error_bound`, `balancedTreeDotProduct_backward_error`,
  `balancedTreeDotProduct_error_bound`, `finZeroPad`,
  `fl_clog2PairwiseDotProduct`, `clog2PairwiseDotProduct_error_bound`
- `runningErrorMu`, `fl_runningDotProductProduct`,
  `exactDotProductPrefixNat`, `fl_runningDotProductPrefixNat`,
  `exactDotProductPrefixState`, `fl_runningDotProductState`,
  `fl_runningDotProduct`, `exactDotProductPrefixState_succ`,
  `fl_runningDotProductState_succ`, `exactDotProductPrefixNat_eq_sum_prefix`,
  `exactDotProductPrefixState_last_eq_sum`,
  `runningError_bound_from_local_errors`,
  `fl_runningDotProduct_error_bound_from_inverse_models`,
  `inverseRelErrorModel`, `inverseRelErrorModel_abs_exact_sub_computed_le`,
  `FloatingPointFormat.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange`,
  `FloatingPointFormat.finiteNormalFl_inverseRelErrorModel`
- `fl_outerProduct`, `outerProduct_error_bound`,
  `outerProduct_error_decomposition`,
  `rankOne_outerProduct2x2_det_zero`,
  `outerProductCounterexampleMatrix_not_rank_one`,
  `fl_outerProduct_counterexample_eq`,
  `fl_outerProduct_counterexample_not_global_backward`
- `fl_matVec`, `fl_matVecSaxpyInit`, `fl_matVecSaxpy`,
  `fl_matVecSaxpyInit_apply`, `fl_matVecSaxpy_eq_sdot`,
  `matVec_backward_error`, `matVec_error_bound`,
  `matVec_error_bound_infNorm`, `matVec_error_bound_oneNorm`,
  `matVec_error_bound_infNormRect`, `matVec_error_bound_oneNormRect`,
  `matVec_row_isRelBackwardStable`
- `fl_matMul`, `matMul_error_bound`, `matMul_error_bound_frobNorm_majorant`,
  `matMul_error_bound_rectOpNorm2Le_majorant`, `matMul_error_bound_oneNorm`,
  `matMul_error_bound_oneNormRect`, `matMul_error_bound_infNormRect`,
  `matMul_error_bound_frobNormRect`, `matMul_error_bound_frobNorm`,
  `matMul_error_bound_opNorm2Le_frob`,
  `matMul_backward_error_col`, `matMulCounterexampleFP_gammaValid_one`,
  `fl_matMul_counterexample_eq`,
  `fl_matMul_counterexample_not_global_backward_A`,
  `fl_matMul_counterexample_not_global_backward_A_gamma`,
  `signedMagnitudeForPivot`, `matMulSharpDeltaA`, `matMulSharpDeltaB`,
  `matMul_forward_bound_sharp_A`, `matMul_forward_bound_sharp_B`
- `rankOneUpdateExact`, `fl_rankOneUpdate`, `rankOneUpdateAbsBudget`,
  `rankOneUpdate_scalar_coeff_le_gamma`, `rankOneUpdate_u_le_gamma`,
  `fl_rankOneUpdate_componentwise_error_bound`,
  `rankOneUpdateAbsBudget_norm2_le`,
  `fl_rankOneUpdate_error_bound_vecNorm2`
- `matSeqProd`, `scalarSeqProd`, `scalarSeqProd_nonneg`,
  `one_le_scalarSeqProd`, `matSeqProd_nonneg`,
  `matSeqProd_abs_perturbed_le_scalar_abs`,
  `matSeqProd_norm_perturbed_le_scalar`,
  `matSeqProd_normwise_perturbation_bound`,
  `matSeqProd_componentwise_perturbation_bound`
- `firstOrderStageError`, `firstOrderForwardError`,
  `firstOrderForwardBudget`, `firstOrderForwardError_vecNorm2_le_budget`,
  `firstOrderSelectedOutputError`, `firstOrderSelectedOutputError_vecNorm2_le`,
  `firstOrderBackwardEquation`, `IsMinimumNormFirstOrderBackwardSolution`,
  `ComponentwiseFirstOrderBackwardFeasible`,
  `IsMinimumComponentwiseFirstOrderBackwardScale`,
  `firstOrderBackward_minimumNorm_solution`,
  `firstOrderBackward_minimumComponentwise_solution`

## Highest-Priority Open Proof Targets

No theorem-bearing Chapter 3 rows remain open in this ledger.  Remaining
`PROSE` rows are expository or bibliographic text rather than local theorem
obligations.

## Hidden-Hypothesis Audit

- Existing Chapter 3 real-operation theorems use the repository's non-strict
  `|delta| <= u` variant of Higham's source `|delta| < u`. This is stronger as
  a theorem surface and acceptable if documented.
- The no-guard-digit sentence on pp. 69--70 is counted as closed only at the
  `FPModel` abstraction layer: the Chapter 3 dot-product proofs require no
  guard-digit field. A concrete derivation of `FPModel` from no-guard hardware
  remains outside this chapter row.
- `fl_runningDotProduct_error_bound_from_inverse_models` is source-faithful for
  Algorithm 3.2 because the PDF derives the running bound from the modified
  inverse model (2.5). It should not be presented as derived from the primitive
  `FPModel.model_add`/`model_mul` fields alone; those are the standard
  `(exact)*(1+delta)` model. Finite-normal-range nearest rounding supplies
  the needed inverse model through
  `FloatingPointFormat.finiteNormalFl_inverseRelErrorModel`.
- `prod_signed_error_bound` encodes the source powers `p_i = +/-1` by choosing
  between `(1 + delta_i)` and `1 / (1 + delta_i)` with a Boolean selector; it
  does not introduce literal integer powers.
- Sampling/probability conventions are irrelevant to this chapter.
- Existing `outerProduct_backward_error` is rowwise and must not be counted as
  a global backward-stability theorem for the outer product. The global
  non-backward-stability source claim is instead closed by
  `fl_outerProduct_counterexample_not_global_backward`.
- Existing `matMul_backward_error_col` is columnwise and must not be counted as
  a single-matrix backward-stability theorem for the whole computed product.
  The global obstruction is closed by
  `fl_matMul_counterexample_not_global_backward_A_gamma`.
- `gamma_div_le_branch` and `gamma_div_gt_branch` close the two source
  quotient branches printed in Lemma 3.3. The older `gamma_div` remains as a
  standalone bounded-theta quotient rule with the independent denominator cost.
- `matMul_error_bound_rectOpNorm2Le_majorant` closes the `p = 2`/vector-action
  majorant in predicate form using explicit `rectOpNorm2Le` certificates for
  the nonnegative factors `|A|` and `|B|`. `matMul_error_bound_opNorm2Le_frob`
  remains a coarser Frobenius fallback. The repository still does not introduce
  a supremum-valued spectral norm function for legacy function-shaped matrices.
- `relErrorCounter_div` closes Stewart's product-counter division rule
  `<j>/<k> = <j+k>` under the explicit `fp.u < 1` nonzero-factor guard; this
  is distinct from the standalone bounded-theta quotient bound `gamma_div`.
- `prod_one_add_delta_eq_one_add_eta_bound_101` closes Lemma 3.4's
  strict `1.01*n*u` product constant directly. The `_le` variant is the
  non-strict adapter for the repository's primitive `FPModel`, with an explicit
  `0 < u` hypothesis; `dotProduct_error_bound_101_succ` instantiates this
  sharper product route for positive-length left-to-right dot products.
- `prod_one_add_delta_eq_one_add_phi_bound_problem32` closes Problem 3.2's
  all-positive-factor product refinement with the larger guard `n*u < 2`.
  The proof uses the local Padé cap
  `real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two`; for `n = 1` it
  handles the endpoint separately because the abstract `FPModel` does not
  globally assume `u <= 1`.
- Existing complex matrix/C-star infrastructure does not instantiate Higham's
  scalar rounded complex arithmetic model. The new `ComplexArithmetic.lean`
  file closes add/sub/mul and the displayed ordinary division proof model; the
  exact Smith branch formulas from section 25.8 are now proved algebraically.
  Both rounded Smith branches have the needed `gamma_3` real subexpression
  bounds, denominator sign/absolute-value lemmas, absolute-denominator scalar
  rounded-quotient `gamma_7` bridges, componentwise `gamma_7` quotient bounds,
  branch normwise bounds, and branch relative-error models. The combined
  selector `fl_smithComplexDiv_rel_error_model` closes the page-80
  `sqrt(2)*gamma_7` overflow-avoiding division note for nonzero divisors.

## Validation

This ledger is an audit artifact. It does not itself add Lean theorem coverage.
After any Chapter 3 proof pass, run:

```bash
lake env lean LeanFpAnalysis/FP/Analysis/Rounding.lean
lake env lean LeanFpAnalysis/FP/Analysis/RoundingProductBounds.lean
lake env lean LeanFpAnalysis/FP/Analysis/ComplexArithmetic.lean
lake env lean LeanFpAnalysis/FP/Algorithms/DotProduct.lean
lake env lean LeanFpAnalysis/FP/Algorithms/BlockDotProduct.lean
lake env lean LeanFpAnalysis/FP/Algorithms/ExtendedPrecisionDotProduct.lean
lake env lean LeanFpAnalysis/FP/Algorithms/TreeDotProduct.lean
lake env lean LeanFpAnalysis/FP/Algorithms/OuterProduct.lean
lake env lean LeanFpAnalysis/FP/Algorithms/MatVec.lean
lake env lean LeanFpAnalysis/FP/Algorithms/MatMul.lean
lake env lean LeanFpAnalysis/FP/Algorithms/RankOneUpdate.lean
lake env lean LeanFpAnalysis/FP/Analysis/FirstOrderFramework.lean
lake build LeanFpAnalysis.FP.Algorithms.RankOneUpdate
lake build LeanFpAnalysis.FP.Analysis.ComplexArithmetic
lake build LeanFpAnalysis.FP
lake env lean examples/LibraryLookup.lean
git diff --check
```
