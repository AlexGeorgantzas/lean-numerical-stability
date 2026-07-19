# Higham, *Accuracy and Stability of Numerical Algorithms* (2nd ed.) — Chapter 3 "Basics"

> **Fresh strict audit (2026-07-18): gate PASS.** The concrete Lemma 3.7
> Frobenius/spectral instantiation, fully permuted arbitrary-tree form of (3.4),
> arbitrary-length pairwise dot-product bound, and printed rectangular 2-norm
> matrix-vector corollary are all proved at source strength. No selected-scope
> bridge remains open.

- **Edition/pages:** 2nd ed., pp. 61–78 (Chapter 3, including Problems 3.1–3.12).
- **Audit mode:** core (primary labels + numbered equations + central definitions + precise body prose claims; problems recorded but optional for the gate).
- **Ownership:** Chapter 3 is the shared error-analysis foundation layer (theta_n/gamma_n calculus). Its modules are consumed by every later chapter in all splits; no single-split lane owns it.
- **Source audited:** `References/1.9780898718027.ch3.pdf`, checked directly against pp. 61–78.
- **Audit date:** 2026-07-18 (fresh main-branch closure audit).
- **Axiom spot-check:** `lemma3_7_frobenius_spectral_perturbation_bound`, `sumTreeDotProduct_backward_stable_any_permuted_order`, `clog2PairwiseDotProduct_error_bound`, `frobNormRect_le_sqrt_min_mul_rectOpNorm2`, and `matVec_error_bound_twoNormRect` all depend only on `[propext, Classical.choice, Quot.sound]`; the earlier core surfaces have the same axiom set.

All Lean names below are in namespace `LeanFpAnalysis.FP`. Module paths are relative to `LeanFpAnalysis/FP/`.

## Primary labels

| Label | Printed statement (summary) | Status | Lean decls | Scope notes |
|---|---|---|---|---|
| Lemma 3.1 | If \|δᵢ\| ≤ u, ρᵢ = ±1, nu < 1, then ∏(1+δᵢ)^ρᵢ = 1+θₙ with \|θₙ\| ≤ γₙ = nu/(1−nu) | **VERIFIED** | `gamma`, `gammaValid`, `prod_error_bound` (ρᵢ≡1), `prod_signed_error_bound` (ρᵢ=±1 via Boolean selector for reciprocal factors) in `Analysis/Rounding.lean`; standalone real-`u` form `prod_one_add_delta_abs_sub_one_le_gamma_radius` in `Analysis/RoundingProductBounds.lean` | Signed exponents encoded as `if neg i then 1/(1+δᵢ) else 1+δᵢ`, faithful to ρᵢ = ±1. Constants derived, not assumed. |
| Algorithm 3.2 | Running error: computes s = fl(xᵀy) and μ with \|s − xᵀy\| ≤ μ (μ = u·Σ(\|ŝᵢ\|+\|ẑᵢ\|)) | **VERIFIED** (conditional on model (2.5), as printed) | `runningErrorMu`, `fl_runningDotProduct`, `runningError_bound_from_local_errors` (checked induction), `fl_runningDotProduct_error_bound_from_inverse_models` (executable loop endpoint) in `Algorithms/DotProduct.lean` | The endpoint theorem takes per-operation `inverseRelErrorModel` (Higham (2.5)) witnesses as hypotheses — exactly the model the printed derivation uses; the repo's primitive `FPModel` surface is the (2.4) standard model, and (2.5) is not derivable from (2.4), so this conditioning is honest, not hidden strength. μ is the exact real accumulator, matching the printed derivation (the source itself treats rounding of μ as negligible prose). |
| Lemma 3.3 | θ/γ algebra: 6 rules (product, quotient two branches, γₖγⱼ ≤ γ_min, iγₖ ≤ γᵢₖ, γₖ+u ≤ γₖ₊₁, γₖ+γⱼ+γₖγⱼ ≤ γₖ₊ⱼ) | **VERIFIED** | `gamma_mul` (rule 1), `gamma_div_le_branch` (rule 2, j ≤ k ⇒ θ_{k+j}), `gamma_div_gt_branch`/`gamma_div` (rule 2, j > k ⇒ θ_{k+2j}), `gamma_prod_le` (rule 3, under `gammaValid fp (2k)` ⇔ max(j,k)u < 1/2), `gamma_nsmul_le` (rule 4), `gamma_add_u_le` (rule 5), `gamma_sum_le` (rule 6); helpers `gamma_inv`, `gamma_mono`, `u_le_gamma`, `gamma_lt_one`, `gamma_add_div_one_sub_gamma_le_of_le` — all in `Analysis/Rounding.lean` | All six printed rules present at printed strength with derived constants. Rule 3's side condition max(j,k)u ≤ 1/2 appears as the `2k`-validity guard. |
| Lemma 3.4 | If \|δᵢ\| ≤ u, nu ≤ 0.01, then ∏(1+δᵢ) = 1+ηₙ, \|ηₙ\| ≤ 1.01nu | **VERIFIED** | `prod_one_add_delta_eq_one_add_eta_bound_101` (strict local errors), `prod_one_add_delta_eq_one_add_eta_bound_101_le` (repo's non-strict \|δᵢ\| ≤ u with 0 < u); envelope lemmas `prod_one_add_delta_bounds`, `prod_one_add_delta_abs_sub_one_le_exp_sub_one`, `real_exp_sub_one_lt_101_mul_of_pos_of_lt_cent` in `Analysis/RoundingProductBounds.lean` | Constant 101/100 exact; guard nu < 1/100 exact. Proof follows the printed exp-envelope argument. |
| Lemma 3.5 | Complex arithmetic under (3.14): fl(x±y) = (x±y)(1+δ), \|δ\| ≤ u; fl(xy) = xy(1+δ), \|δ\| ≤ √2·γ₂; fl(x/y) = (x/y)(1+δ), \|δ\| ≤ √2·γ₄ | **VERIFIED** | `complexRelErrorModel`, `fl_complexAdd_rel_error_model`, `fl_complexSub_rel_error_model`, `fl_complexMul_rel_error_model` (√2·γ₂), `fl_complexDiv_rel_error_model` (√2·γ₄, hypothesis y ≠ 0) in `Analysis/ComplexArithmetic.lean` | δ is a complex number bounded in modulus, matching the printed caveat that real/imaginary parts are not individually accurate. Page-73 remark on the overflow-avoiding formula (27.1): `fl_smithComplexDiv_rel_error_model` gives the printed √2·γ₇ radius (both Smith branches proved). |
| Lemma 3.6 | ‖∏(Xⱼ+ΔXⱼ) − ∏Xⱼ‖ ≤ (∏(1+δⱼ)−1)∏‖Xⱼ‖ for a consistent norm, ‖ΔXⱼ‖ ≤ δⱼ‖Xⱼ‖ | **VERIFIED** | `matSeqProd_normwise_perturbation_bound` (+ size lemma `matSeqProd_norm_perturbed_le_scalar`) in `Analysis/MatrixAlgebra.lean` | Stated for an abstract norm functional with exactly the consistent-norm axioms the printed induction uses (nonneg, N(0) ≤ 0, N(I) ≤ 1, subadditive, submultiplicative); concrete `oneNorm`/`infNorm`/`frobNorm` instances satisfy these. Finite-sequence indexing `Fin m` vs. printed j = 0..m is pure reindexing. |
| Lemma 3.7 | Same with ‖ΔXⱼ‖_F ≤ δⱼ‖Xⱼ‖₂, error in ‖·‖_F, factor sizes in ‖·‖₂ | **VERIFIED** | `lemma3_7_frobenius_spectral_perturbation_bound` in `Analysis/MatrixAlgebra.lean`; induction core `matSeqProd_mixed_normwise_perturbation_bound` | The public theorem assumes only the printed Frobenius perturbation hypothesis. It derives `‖ΔXⱼ‖₂ ≤ ‖ΔXⱼ‖_F` internally, then applies the proved mixed inequalities `frobNorm_matMul_le_opNorm2_mul` and `frobNorm_matMul_le_mul_opNorm2`; no target-equivalent spectral perturbation premise is exposed. |
| Lemma 3.8 | Componentwise: \|∏(Xⱼ+ΔXⱼ) − ∏Xⱼ\| ≤ (∏(1+δⱼ)−1)∏\|Xⱼ\| when \|ΔXⱼ\| ≤ δⱼ\|Xⱼ\| | **VERIFIED** | `matSeqProd_componentwise_perturbation_bound` (+ `matSeqProd_abs_perturbed_le_scalar_abs`) in `Analysis/MatrixAlgebra.lean` | Exact printed shape, componentwise, entrywise absolute-value matrices. |
| Lemma 3.9 | ŷ = fl(x − a(bᵀx)) satisfies ŷ = y + Δy, \|Δy\| ≤ γₙ₊₃(I + \|a\|\|bᵀ\|)\|x\|, hence ‖Δy‖₂ ≤ γₙ₊₃(1+‖a‖₂‖b‖₂)‖x‖₂ | **VERIFIED** | `fl_rankOneUpdate` (concrete routine: rounded dot product, rounded scalar multiply, rounded subtraction), `fl_rankOneUpdate_componentwise_error_bound`, `fl_rankOneUpdate_error_bound_vecNorm2`, coefficient lemma `rankOneUpdate_scalar_coeff_le_gamma` in `Algorithms/RankOneUpdate.lean` | Both printed displays at printed strength; the γₙ + u(1+γₙ) + … ≤ γₙ₊₃ coefficient chase is derived, not assumed. |

## Numbered equations

| Eq(s) | Content | Status | Lean decls / notes |
|---|---|---|---|
| (3.1)–(3.2) | Local-factor expansion of the sequential inner product | **VERIFIED** | `dotProduct_factor_expansion_succ`, `dotProduct_factor_expansion_sum_succ` (`Algorithms/DotProduct.lean`): exact expansion with per-term multiplication factor and suffix addition-factor products, before any gamma compression. |
| (3.3) | ŝₙ = Σ xᵢyᵢ(1+ηᵢ), backward form with graded θ's | **VERIFIED** | `dotProduct_backward_error`: each \|ηᵢ\| ≤ γₙ (the uniform bound the printed interpretation uses). The graded subscripts (θₙ, θₙ₊₁₋ᵢ, …) are recoverable from the (3.1)–(3.2) suffix expansion but not restated with graded gamma indices. |
| (3.4) | fl(xᵀy) = (x+Δx)ᵀy = xᵀ(y+Δy), \|Δx\| ≤ γₙ\|x\|, \|Δy\| ≤ γₙ\|y\| | **VERIFIED** | Sequential forms `dotProduct_backward_stable_x`, `dotProduct_backward_stable_y`; arbitrary association `sumTreeDotProduct_backward_stable_any_order`; fully permuted arbitrary-tree form `sumTreeDotProduct_backward_stable_any_permuted_order` (`Algorithms/TreeDotProduct.lean`). The latter transports perturbations back to the original coordinates, proving the printed “for any order of evaluation” statement. |
| (3.5) | \|xᵀy − fl(xᵀy)\| ≤ γₙ Σ\|xᵢyᵢ\| = γₙ\|x\|ᵀ\|y\| | **VERIFIED** | `dotProduct_error_bound` (`Algorithms/DotProduct.lean`). |
| (3.6) | Outer product: Â = xyᵀ + Δ, \|Δ\| ≤ u\|xyᵀ\| | **VERIFIED** | `outerProduct_error_bound`, `outerProduct_error_decomposition` (`Algorithms/OuterProduct.lean`). Prose "not backward stable / Â not rank-1": `fl_outerProduct_counterexample_not_global_backward` with an explicit valid `FPModel` and non-rank-1 computed matrix. |
| (3.7) | First-order form nu\|x\|ᵀ\|y\| + O(u²) | **VERIFIED** (concrete-remainder form) | O(u²) is not a formal object; the honest counterpart is `gamma_eq_linear_plus_quadratic_remainder` (`Analysis/Rounding.lean`): γₙ = nu + (nu)²/(1−nu) exactly, composable with (3.5). Also `n_mul_u_le_gamma`, `gamma_le_two_mul_n_u_of_nu_le_half` for the standard regime conversions. |
| (3.8) | γ̃ₖ = cku/(1−cku) notation | **SKIP-OK** (notational device) | No central `gammaTilde` definition; the repository's discipline is explicit constants `gamma fp (c*k)`, whose algebra is Lemma 3.3 rule 4 (`gamma_nsmul_le`) and `gamma_mul_index_le_two_mul_nat_mul_gamma`. Chapter-local γ̃ instances appear downstream (ch19–21 modules) where the source uses them. |
| (3.9) | \|xᵀy − fl(xᵀy)\| ≤ 1.01nu\|x\|ᵀ\|y\| | **VERIFIED** | `dotProduct_error_bound_101_succ` (`Algorithms/DotProduct.lean`), via `dotProductLocalFactor_abs_sub_one_le_101`. Non-strict ≤ on the repo's non-strict primitive model; strictness noted in docstring. |
| (3.10) | Stewart relative-error counter <k> and rules <j><k> = <j+k>, <j>/<k> = <j+k> | **VERIFIED** | `relErrorCounter`, `relErrorCounter_mul`, `relErrorCounter_inv`, `relErrorCounter_div`, bound `relErrorCounter_abs_sub_one_le_gamma` (`Analysis/Rounding.lean`). |
| (3.11) | ŷ = (A+ΔA)x, \|ΔA\| ≤ γₙ\|A\| | **VERIFIED** | `matVec_backward_error` (`Algorithms/MatVec.lean`). (Docstring cites "equation 3.10" — a label slip in the comment only; the statement is (3.11).) |
| (3.12) | \|y − ŷ\| ≤ γₙ\|A\|\|x\| | **VERIFIED** | `matVec_error_bound`. Normwise corollaries p = 1, ∞ (square and rectangular): `matVec_error_bound_oneNorm(Rect)`, `matVec_error_bound_infNorm(Rect)`. The printed unnumbered 2-norm display is `matVec_error_bound_twoNormRect`, using the exact rectangular norm `rectOpNorm2` and proved Lemma 6.6(a) bridge `frobNormRect_le_sqrt_min_mul_rectOpNorm2`. |
| (3.13) | \|C − Ĉ\| ≤ γₙ\|A\|\|B\| | **VERIFIED** | `matMul_error_bound` (`Algorithms/MatMul.lean`); per-column backward error (body display ĉⱼ = (A+ΔAⱼ)bⱼ): `matMul_backward_error_col`; normwise p = 1, ∞, F: `matMul_error_bound_oneNorm(Rect)`, `_infNormRect`, `_frobNorm(Rect)`, `_frobNorm_majorant`. Prose "whole Ĉ has no small backward error": counterexample `fl_matMul_counterexample_not_global_backward_A(_gamma)`. Prose sharpness "\|(A+ΔA)B − AB\|ᵢⱼ = u(\|A\|\|B\|)ᵢⱼ attainable": `matMul_forward_bound_sharp_A`, `matMul_forward_bound_sharp_B`. |
| (3.14a–c) | Complex add/mul/div implementation formulas | **VERIFIED** | `fl_complexAdd`, `fl_complexSub`, `fl_complexMul`, `fl_complexDiv` in `Analysis/ComplexArithmetic.lean` implement exactly (3.14a–c) from rounded real ops (some docstrings cite "(3.13x)" — 1st-ed label slip in comments only). |

## Body prose / unnumbered displays

| Item | Status | Notes |
|---|---|---|
| Blocked inner product: \|sₙ−ŝₙ\| ≤ γ_{n/2+1}\|x\|ᵀ\|y\| (two pieces), γ_{n/k+k−1} (k pieces), minimum 2√n−1 at k = √n | **VERIFIED** | `Algorithms/BlockDotProduct.lean`: `blockDotProduct_error_bound` (radius `gamma (b+q)`; with k = q+1 blocks of length b and n = bk this is γ_{n/k+k−1}), `twoPieceDotProduct_error_bound`, `blockDotProduct_real_index_ge_optimum`, `blockDotProduct_real_index_at_sqrt`. |
| Pairwise-summation dot product bound γ_{⌈log₂n⌉+1}\|x\|ᵀ\|y\| | **VERIFIED** | `clog2PairwiseDotProduct_error_bound` (`Algorithms/TreeDotProduct.lean`) zero-pads an arbitrary length to `2^(Nat.clog 2 n)`, evaluates a perfect balanced tree, and proves exactly `gamma fp (Nat.clog 2 n + 1)`; `Nat.clog 2 n` is the natural ceiling of log₂ n. |
| Extended precision: \|xᵀy − fl(flₑ(xᵀy))\| ≤ u\|xᵀy\| + (nuₑ/(1−nuₑ))(1+u)\|x\|ᵀ\|y\| | **VERIFIED** | `Algorithms/ExtendedPrecisionDotProduct.lean`: `extendedDotProduct_error_bound` (abstract `FinalRoundingModel` for the working-precision final round, inner `FPModel` at uₑ); parenthetical "subscripts reduced by 1 if multiplications exact": `exactMulDotProduct_backward_error` (γ_{n−1}). |
| sdot/saxpy rounding-error equivalence (§3.5) | **VERIFIED** | `fl_matVecSaxpy_eq_sdot` (`Algorithms/MatVec.lean`): exact equality of the computed vectors, the strongest possible form of "exactly the same rounding errors". |
| §3.2 purpose of rounding error analysis | **SKIP-OK** (editorial) | The formal backward-stability predicate connection is `dotProduct_isRelBackwardStable` (`Analysis/Stability.lean` predicate). |
| §3.4 Olver rp notation, Kahan bracket notation, Wilkinson ψ_r | **SKIP-OK** | Notation survey, editorial. |
| §3.8 error analysis demystified (Jacobian framework) | **SKIP-OK** (first-order outline) | Presented "to first order" as a conceptual framework, not a theorem; no formalization, none claimed. |
| §3.9 other approaches, §3.10 notes and references, epigraphs | **SKIP-OK** | Editorial/bibliographic. |

## Problems (optional in core mode)

| Problem | Status | Lean decls / notes |
|---|---|---|
| 3.1 (prove Lemma 3.1) | **VERIFIED** | Proofs of `prod_error_bound` / `prod_signed_error_bound` are checked inductions, not citations. |
| 3.2 (Kielbasiński–Schwetlick: ρᵢ≡1 ⇒ \|θₙ\| ≤ nu/(1−nu/2) for nu < 2) | **VERIFIED** | `prod_one_add_delta_eq_one_add_phi_bound_problem32` (+ Padé cap `real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two`) in `Analysis/RoundingProductBounds.lean`. |
| 3.3 (running error for continued fraction) | **PARTIAL** | `Algorithms/ContinuedFraction.lean`: one-step inheritance lemma and end-to-end certificate `continuedFraction_running_error_bound`, conditional on local residual bounds τₖ and a budget recurrence; the concrete `fl_add`/`fl_div` instantiation of τₖ is not discharged. |
| 3.4 (prove Lemma 3.3) | **VERIFIED** | All six rules proved in `Analysis/Rounding.lean` (see Lemma 3.3 row). |
| 3.5 (fl(AB) = (A+ΔA)B, \|ΔA\| ≤ γₙ\|A\|\|B\|\|B⁻¹\|, and the B-perturbed analogue) | **VERIFIED** | `matMul_backward_error_common_A_of_inverse`, `matMul_backward_error_common_B_of_inverse` (`Algorithms/MatMul.lean`), componentwise triple-product bounds written as explicit sums, with two-sided inverse hypothesis. |
| 3.6 (backward error definition ω; ω ≥ maxᵢⱼ(√(1+\|rᵢⱼ\|/gᵢⱼ)−1)) | **VERIFIED** (feasibility form) | `Algorithms/MatMulBackwardError.lean`: residual majorants and `matMulRelativeBackwardFeasible_sqrt_lower_bound_entry` / weighted variant — every feasible ε dominates the entrywise sqrt expression, which is exactly the printed lower bound on the minimal radius ω. ω-as-minimum is not reified; the open-ended prose parts (full-rank discussion, mixed backward/forward definition) are unformalized. |
| 3.7 (complex analogues of (3.4), (3.11)) | **PARTIAL** | `Algorithms/ComplexBackwardError.lean`: `complexDotProduct_backward_stable_x/_y`, `complexMatVec_backward_error` — reductions from a hypothesized complex componentwise expansion (`complexDotProductRelErrorExpansion`); the expansion is not derived from a concrete complex fl dot product built on `fl_complexAdd`/`fl_complexMul`. |
| 3.8 (x² − y² direct vs. factored) | **VERIFIED** | `Algorithms/SquareDifference.lean`: `fl_squareDiff_direct_error_bound` (γ₂(\|x·x\|+\|y·y\|) cancellation-sensitive majorant), `fl_squareDiff_factored_rel_error` ((x²−y²)(1+θ₃)) and absolute form. |
| 3.9 (prove Lemma 3.6) | **VERIFIED** | Proof of `matSeqProd_normwise_perturbation_bound` is a checked induction. |
| 3.10 (‖A₁…A_k − fl(A₁…A_k)‖_F ≤ (kn²u + O(u²))∏‖Aᵢ‖₂) | **PARTIAL** | `Algorithms/MatSeqProduct.lean`: `matPrefixProd_error_bound_from_local_errors` and `matPrefixProd_error_bound_uniform` — exact finite-budget accumulation (Σεⱼ · ∏αⱼ) replacing the asymptotic display; the local εⱼ = n²u + O(u²) budget is not discharged against `fl_matMul`. |
| 3.11 (Kahan `absolute(x,m)` explanation) | **PARTIAL** | `Algorithms/KahanAbsolute.lean`: exact baselines, IEEE-double encodings of all six displayed inputs, displayed machine outputs recorded, and exactness of the initial squaring proved (`kahanAbsoluteProblem311IeeeDouble_initialSquare_exact`); the full error analysis of the repeated sqrt/square phases is open (stated in the module docstring). |
| 3.12 (quadrature rule bound) | **VERIFIED** | `Algorithms/Quadrature.lean`: `fl_quadrature_error_bound_of_function_value_rel_error` — \|I − Ĵ\| ≤ \|I − J\| + (η + γₙ(1+η))Σ\|wᵢ\|\|fᵢ\|, with the three error sources separated as the problem asks. |

## Honest-strength notes

1. **Non-strict primitive model.** The repository `FPModel` uses \|δ\| ≤ u (non-strict). Where Higham's displays are strict (Lemma 3.4, Problem 3.2), the Lean theorems either assume strict local errors or add `0 < u` and recover the strict product radius; both variants exist and are labeled.
2. **Algorithm 3.2 / model (2.5).** The executable running-error theorem is conditional on per-operation inverse-model witnesses (Higham (2.5)). This mirrors the printed derivation, which is itself conducted in model (2.5); (2.5) is an independent model assumption not derivable from the (2.4)-only `FPModel`.
3. **Lemmas 3.6–3.8 and concrete Lemma 3.7.** The reusable induction cores retain their honest abstract-norm hypotheses. `lemma3_7_frobenius_spectral_perturbation_bound` now packages the printed concrete norms and derives the spectral perturbation estimate from the source's Frobenius hypothesis rather than assuming it.
4. **Uniform vs. graded gamma subscripts in (3.3).** The formal backward error bounds every perturbation by γₙ (the bound the source itself extracts); the finer graded structure is available from the factor-expansion theorems.
5. **Comment-label slips.** A few docstrings cite 1st-edition/off-by-one equation numbers ((3.10) for (3.11), (3.13a) for (3.14a)); the attached statements match the 2nd-edition content audited here.

## Selected-scope gate: **PASS**

All nine primary labels, all numbered equations (3.1)–(3.14), and the selected
central body displays are verified at printed strength. The four bridges found
missing by the fresh audit—concrete Lemma 3.7, any-order (3.4), the
`γ_{⌈log₂n⌉+1}` pairwise display, and the rectangular 2-norm matvec display—are
closed. No selected-scope residual remains.

Problems 3.3, 3.7, 3.10, and 3.11 remain honestly PARTIAL as recorded above;
problems are optional in this ledger's core audit mode and are not bridge
dependencies for Chapters 1–28.

## Cross-chapter role

Chapter 3 is the foundation layer consumed by essentially every later chapter:

- `gamma`/`gammaValid` and the Lemma 3.1/3.3 calculus (`prod_error_bound`, `gamma_mul`, `gamma_div*`, `gamma_sum_le`, `gamma_nsmul_le`, …) are the constant-accounting engine for chs. 4–28 (e.g., `three_gamma_plus_sq_le_gamma` exists specifically for Theorem 9.4's 3γₙ+γₙ² coefficient; `gamma_inv_mul_roundoff` for Lemma 18.1).
- `dotProduct_*` (3.3)–(3.5) feed summation (ch4), Horner (ch5), triangular solves (ch8), LU/GE (ch9), Cholesky (ch10), and the ch14 inversion clusters.
- `matVec_*`/`matMul_*` ((3.11)–(3.13) + norm corollaries) feed chs. 9–14, 18–22.
- Lemmas 3.6–3.8 (`matSeqProd_*`) are the perturbed-product engine for Householder/Givens QR (ch19), underdetermined systems (ch21), and matrix powers (ch18).
- Lemma 3.9 (`fl_rankOneUpdate*`) underlies Gram–Schmidt and Householder QR error analyses (ch19).
- Lemma 3.5 (`complexRelErrorModel`, `fl_complex*`) is the bridge that transfers real-arithmetic results to complex arithmetic "with constants increased appropriately" (used by the ch18 complex matrix-powers modules and ch25/27-adjacent material).
