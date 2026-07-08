# Higham Chapter 11 Formalization Report — "Symmetric Indefinite and Skew-Symmetric Systems"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 11, "Symmetric Indefinite and Skew-Symmetric Systems" (printed pp. 213–229).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch11.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Planning documents consulted: blueprint, Split 2 section of `split_primary_contracts.md`, `chapter_index.md`.
- **Selected-scope gate: FAIL.** The chapter's four primary *theorems* (11.3, 11.4, 11.7,
  11.8) are backward-error / stability results whose Lean surfaces are currently
  **conditional-transfer interfaces**: they take the analytic backward-error bound as a
  hypothesis and restate it (`h : P ⊢ P`). Per the project honesty policy a conditional
  transfer does not close the stronger source row, so these rows remain **open**. The five
  *algorithms* (11.1, 11.2, 11.5, 11.6, 11.9) are modeled as honest decision predicates plus
  the genuinely-proved pivot-parameter and per-step growth lemmas listed below.

Primary Lean module: `LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean`
(chapter-label surface); reusable definitions and proofs in
`LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean`.

## Proved selected targets and dependencies
Rows in this table are compiled Lean results. Rows labelled with Theorem 11.8
after the exact recurrence entries are dependency or wrapper results only; they
do **not** close the selected Theorem 11.8 row while the budget-comparison
assumptions remain open in the not-proved ledger below.

| Source item | Lean declaration(s) | File | Notes |
|---|---|---|---|
| Alg 11.1 α = (1+√17)/8 root of 4α²−α−1 | `bunch_parlett_alpha_root`, `higham11_1_bunch_parlett_alpha_root` | CholeskyIndefinite / Ch11 | exact algebraic identity |
| Alg 11.6 α = (√5−1)/2 root of α²+α−1 | `bunch_tridiagonal_alpha_root`, `bunch_tridiagonal_alpha_pos`, `bunch_tridiagonal_alpha_lt_one`, `bunch_tridiagonal_alpha_sq`, `higham11_6_bunch_tridiagonal_alpha_root`, `higham11_6_bunch_tridiagonal_alpha_pos`, `higham11_6_bunch_tridiagonal_alpha_lt_one`, `higham11_6_bunch_tridiagonal_alpha_sq` | " | exact algebraic identity plus `0<α<1` and `α²=1−α`, used by tridiagonal pivot-case inequalities |
| Alg 11.6 tridiagonal pivot branch tests | `bunch_tridiagonal_pivot_choice_one_threshold`, `bunch_tridiagonal_pivot_choice_two_threshold`, `bunch_tridiagonal_pivot_choice_one_of_threshold`, `bunch_tridiagonal_pivot_choice_two_of_threshold`, `bunch_tridiagonal_pivot_choice_one_a11_ne_zero_of_a21_ne_zero`, `bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg`, `bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg`, and the corresponding `higham11_6_tridiagonal_pivot_choice_*` wrappers | " | **new this session**; extracts the printed one-/two-pivot threshold inequalities, constructs the branch predicates from those tests, and proves the local nonzero pivot facts needed for the Theorem 11.7 branch split |
| Thm 11.7 2×2 tridiagonal pivot determinant lower bound | `bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound`, `bunch_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound`, `higham11_7_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound`, `higham11_7_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound` | " | **new this session**; Algorithm 11.6's two-pivot branch plus `|a22| ≤ σ` gives `|a11*a22-a21^2| ≥ (1-α)a21^2` and hence nonsingularity of the accepted `2×2` tridiagonal pivot block |
| Thm 11.7 2×2 tridiagonal pivot inverse-entry bounds | `bunch_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound`, `higham11_7_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound` | " | **new this session**; with `|a11|,|a22| ≤ σ`, bounds the inverse entries `a22/det`, `-a21/det`, and `a11/det` using the determinant lower bound, preparing the one-step fl backward-error estimate |
| Thm 11.7 atomic fl update for a 2×2 tridiagonal pivot | `fl_tridiagonal_twoByTwo_schur_step_error`, `higham11_7_fl_tridiagonal_twoByTwo_schur_step_error`, `fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound`, `higham11_7_fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound`, `fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound`, `higham11_7_fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound`, `fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound`, `higham11_7_fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound`, `fl_tridiagonal_twoByTwo_trailing_one_stage_bound`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_bound`, `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound`, `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three`, `tridiagonalTwoByTwoFirstTrailingIndex`, `higham11_7_tridiagonalTwoByTwoFirstTrailingIndex`, `tridiagonalTwoByTwoTrailingSubproblemIndex`, `higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex`, `tridiagonalTwoByTwoTrailingSubproblemIndex_zero`, `higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex_zero`, `tridiagonalTwoByTwoTrailingSubproblemIndex_injective`, `higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex_injective`, `TridiagonalTwoByTwoTrailingBlockSupport`, `higham11_7_TridiagonalTwoByTwoTrailingBlockSupport`, `TridiagonalLeadingBlockSupport`, `higham11_7_TridiagonalLeadingBlockSupport`, `tridiagonalLeadingBlockSupport_of_le_offset`, `higham11_7_tridiagonalLeadingBlockSupport_of_le_offset`, `tridiagonalLeadingBlockSupport_zero_bound`, `higham11_7_tridiagonalLeadingBlockSupport_zero_bound`, `tridiagonalLeadingBlockSupport_zero_printed_bound`, `higham11_7_tridiagonalLeadingBlockSupport_zero_printed_bound`, `tridiagonalLeadingBlockSupport_add_bound`, `higham11_7_tridiagonalLeadingBlockSupport_add_bound`, `tridiagonalLeadingBlockSupport_add_bound_of_le_offset`, `higham11_7_tridiagonalLeadingBlockSupport_add_bound_of_le_offset`, `tridiagonalLeadingBlockSupport_add_bound_printed`, `higham11_7_tridiagonalLeadingBlockSupport_add_bound_printed`, `tridiagonalLeadingBlockSupport_add_bound_printed_of_le_offset`, `higham11_7_tridiagonalLeadingBlockSupport_add_bound_printed_of_le_offset`, `tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport`, `higham11_7_tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport`, `tridiagonalTwoByTwoTrailingBlockSupport_add_bound`, `higham11_7_tridiagonalTwoByTwoTrailingBlockSupport_add_bound`, `tridiagonalTwoByTwoLiftTrailingPerturbation`, `higham11_7_tridiagonalTwoByTwoLiftTrailingPerturbation`, `tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support`, `higham11_7_tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support`, `tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport`, `higham11_7_tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport`, `tridiagonalTwoByTwoLiftTrailingPerturbation_bound_leadingBlockSupport`, `higham11_7_tridiagonalTwoByTwoLiftTrailingPerturbation_bound_leadingBlockSupport`, `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed`, `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support`, `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate`, `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed`, `fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate`, `fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate_leadingBlockSupport`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate_leadingBlockSupport`, `fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate`, `fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport` | " | **new this session**; proves `fl(b - fl(fl(c*f)*c)) = (b-c*f*c)+Δ` with `|Δ| ≤ γ₃(|b|+|c*f*c|)` from the standard model and `prod_error_bound`, specializes `f = a11/(a11*a22-a21^2)` using Algorithm 11.6 inverse-entry bounds, repackages the result as an exact Schur update of a perturbed trailing scalar `b+Δb`, converts it to a uniform `γ₃(Amax+Amax·κ·Amax)` budget when `|b|,|c|≤Amax` and the inverse-entry scalar is bounded by `κ`, lifts the scalar residual to the `Fin 1 × Fin 1` trailing Schur block touched by a tridiagonal `2×2` pivot, hands it to the printed componentwise budget `c·u·Amax` when the local scalar comparison is supplied, embeds that perturbation into the ambient `Fin 3 × Fin 3` first-stage tridiagonal block-LDLᵀ shell with zeros outside the trailing entry, generalizes the same zero-outside embedding to an arbitrary local block `Fin (n+3)` at the first trailing index of the shrinking recursion, adds the offset/injectivity bookkeeping for embedding the recursive trailing subproblem `Fin (n+1)` into that ambient block, packages the local perturbation as supported in the trailing block after the leading two rows/columns, proves the zero-base package, printed zero-base package, zero-prefix depth monotonicity, offset-generic and mixed-depth add/bound combiners, printed coefficient add/bound combiners, and offset-two bridge for zero-prefix supported perturbations, proves the trailing-block support-preserving add/bound combiner for accumulating local and recursive perturbations, applies that combiner to accumulate the local printed-budget residual with an already-supported recursive trailing perturbation, exposes the printed coefficient update `(c_bound+c_rec)·u·Amax` when the recursive side has coefficient `c_rec`, lifts a recursive `Fin (n+1)` trailing-subproblem perturbation into the ambient block with bounds/support and embedded-entry identity, shifts zero-prefix support by two when such a recursive perturbation is lifted into the ambient block and packages that shifted support together with the componentwise bound and embedded-entry identity, feeds that lifted residual into the local accumulator so the recursive residual appears as `ΔRtail 0 0`, composes a recursive scalar certificate `tail_fl = tail_exact + ΔRtail 0 0` with the local rounded Schur update as `outer_fl + tail_fl = outer_exact + tail_exact + ΔA`, and exposes both the subproblem and recursive-residual accumulated perturbations through the generic offset-two zero-prefix support predicate |
| Thm 11.7 solve-side interface bridge | `higham11_7_tridiagonal_backward_error_interface_of_solve_delta`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_nonneg`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm` | Ch11 | **new this session**; if the recursive tridiagonal analysis constructs the solve-side perturbation `ΔA₂` with the printed componentwise budget, the factorization-side perturbation `ΔA₁` can be filled by zero to produce the source-facing Theorem 11.7 interface shape; the `_nonneg` form derives `0 ≤ c*u*Amax` from separate nonnegativity of `c`, `u`, and `Amax`, and the `_infNorm` form specializes the budget to `c*u*‖A‖∞` |
| Thm 11.7 entrywise infinity-norm bridge | `higham11_7_abs_entry_le_infNorm` | Ch11 | **new this session**; row-sum bridge showing every entry satisfies `|Aᵢⱼ| ≤ ‖A‖∞`, used to discharge local scalar `Amax` hypotheses from a norm budget |
| Thm 11.7 componentwise-to-infinity-norm bridge | `higham11_7_infNorm_le_card_mul_of_uniform_componentwise_bound`, `higham11_7_infNorm_le_card_mul_of_printed_componentwise_bound` | Ch11 | **new this session**; aggregates a uniform componentwise perturbation budget to an infinity-norm bound by row sums, with the printed `c*u*Amax` form exposed for the final normwise theorem |
| Thm 11.7 solve-side norm-bound packaging | `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_with_norm_bounds`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm_with_norm_bounds` | Ch11 | **new this session**; carries the recursive solve perturbation through the source-facing interface while also recording `‖ΔA₁‖∞` and `‖ΔA₂‖∞` bounds obtained from the componentwise budget, including the direct `Amax = ‖A‖∞` specialization |
| §11.1.1 1×1 multiplier bound `|c/e| ≤ 1/α` | `oneByOne_multiplier_bound`, `higham11_1_oneByOne_multiplier_bound` | " | **new this session**; derived from pivot test `α·ω ≤ |e|`; the honest content behind the `bunch_parlett_L_bound`/`bunch_kaufman` `‖L‖`-interfaces |
| §11.1.1 / §11.1.2 1×1 Schur step growth `|b−c₁c₂/e| ≤ (1+1/α)μ₀` | `oneByOne_schur_growth`, `higham11_1_oneByOne_schur_growth` | " | **new this session**; printed bound `|ã_ij| ≤ μ₀+μ₀²/μ₁ ≤ (1+1/α)μ₀`; mechanism behind ρₙ ≤ (1+α⁻¹)^{n−1} |
| §11.1.1 2×2 pivot det bound `det E ≤ (α²−1)μ₀²` | `twoByTwo_completePivot_det_bound`, `higham11_4_twoByTwo_det_bound` | " | **new this session**; printed `det(E) ≤ μ₁²−μ₀² ≤ (α²−1)μ₀²` |
| §11.1.1 2×2 pivot nonsingularity `|det E| ≥ (1−α²)μ₀²` | `twoByTwo_completePivot_absdet_lower`, `higham11_4_twoByTwo_absdet_lower` | " | **new this session**; α∈[0,1); printed `|det E| ≥ (1−α²)μ₀²` |
| §11.1.1 2×2 Schur step growth `|ã| ≤ (1+2/(1−α))μ₀` (eq 11.4) | `twoByTwo_schur_growth`, `higham11_4_twoByTwo_schur_growth` (+ helper `abs_triple_mul_le`) | " | **new this session**; inverse-block entries `≤ αK,K`, `K = 1/((1−α²)μ₀)`; with the 1×1 bound this gives both single-step growth bounds of §11.1.1 |
| §11.1.1 α-derivation: growth balance `(1+1/α)² = 1+2/(1−α)` ⟺ `4α²−α−1=0`; `0<α<1` | `growth_balance_of_root`, `bunch_parlett_growth_balance`, `bunch_parlett_alpha_pos`, `bunch_parlett_alpha_lt_one`, `higham11_1_growth_balance` | " | **new this session**; the printed derivation fixing `α = (1+√17)/8`; ties the two single-step growth bounds together |
| §11.1.1 growth-factor recursion `r n ≤ (1+1/α)ⁿ·ρ₀` from per-stage ratio `r(k+1) ≤ (1+1/α)·r k` | `geom_growth_iterate`, `higham11_1_growth_factor_recursion` | " | **new this session**; derives the printed `ρₙ ≤ (1+α⁻¹)^{n−1}` from the single-step bounds (induction, not assumed) |
| §11.1.1 printed inverse bound `|E⁻¹| ≤ K·[[α,1],[1,α]]`, `K=1/((1−α²)μ₀)` | `twoByTwo_inverse_entry_bounds`, `higham11_4_twoByTwo_inverse_entry_bounds` | " | **new this session**; entrywise bounds on `E⁻¹=d⁻¹[[e₂₂,−e₂₁],[−e₂₁,e₁₁]]`, derived from the determinant magnitude bound |
| §11.1.1 self-contained 2×2 growth (eq 11.4 with actual `E⁻¹`) | `twoByTwo_schur_growth_of_block`, `higham11_4_twoByTwo_schur_growth_of_block` | " | **new this session**; `\|ã\| ≤ (1+2/(1−α))μ₀` from pivot-block data alone — **no inverse-entry bounds assumed** |
| §11.1 fl backward error of one 1×1 Schur step (toward Thm 11.3) | `fl_oneByOne_schur_step_error`, `higham11_3_fl_oneByOne_schur_step_error` | " | **new this session**; computed `fl(a−fl(fl(c₁/e)·c₂)) = (a−c₁c₂/e)+Δ`, `\|Δ\| ≤ γ₃(\|a\|+\|c₁c₂/e\|)` **derived** via `prod_error_bound` (standard model), not assumed — the atomic per-step ingredient of Thm 11.3 |
| §11.1 fl backward error of 1×1 pivot solve (Thm 11.3 / eq 11.5, s=1) | `fl_oneByOne_solve_backward_error`, `higham11_3_fl_oneByOne_solve_backward_error` | " | **new this session**; `x̂ = fl(b/e)` satisfies `(e+Δe)x̂ = b`, `\|Δe\| ≤ γ₁\|e\|` — **derived** 1×1 instance of the (11.5) block-solve perturbation hypothesis |
| §4.2 per-stage trailing fl backward error (Higham [608,1997]) | `fl_oneByOne_stage_trailing_error`, `higham11_3_fl_stage_trailing_error` | " | **new this session**; `l̂_i·e·l̂_j + fl(b−fl(l̂_i·c_j)) = b + Δ`, `\|Δ\| ≤ 2γ₃(\|b\|+\|c_i c_j/e\|)`, via `prod_error_bound` — the atomic (i,j) step of Thm 11.3's componentwise fl induction |
| §4.2 fl **trailing-block backward error** (inductive step of Thm 11.3) | `fl_blockLDLT_trailing_bound`, `higham11_3_fl_blockLDLT_trailing_bound` | " | **new this session**; recursive `L_S,D_S` within `Bs` of the computed Schur ⇒ `\|(L̂D̂L̂ᵀ)_{i+1,j+1} − A_{i+1,j+1}\| ≤ 2γ₃(\|A_{i+1,j+1}\| + \|A_{i+1,0}A_{0,j+1}/A00\|) + Bs i j`; combines the per-stage error with the recursion IH |
| §4.2 fl **pivot-row/col backward error** (other half of the stage) | `fl_blockLDLT_pivot_row_bound`, `fl_blockLDLT_pivot_col_bound` (+ `higham11_3_` wrappers) | " | **new this session**; `(L̂D̂L̂ᵀ)_{0,0} = A00` exactly, `\|(L̂D̂L̂ᵀ)_{0,j+1} − A_{0,j+1}\|`, `\|(L̂D̂L̂ᵀ)_{i+1,0} − A_{i+1,0}\| ≤ u·\|·\|` — **all four index cases** of the single 1×1-pivot fl assemble step now proved |
| §4.2 fl **one-stage all-index backward-error envelope** | `flBlockLDLTOneByOneStageBound`, `fl_blockLDLT_oneByOne_stage_bound`, `higham11_3_fl_oneByOneStageBound`, `higham11_3_fl_oneByOneStageBound_nonneg`, `higham11_3_fl_blockLDLT_oneByOne_stage_bound` | " | **new this session**; packages pivot entry, pivot row, pivot column, and trailing-block estimates into one `∀ I J` bound for a rounded 1×1-pivot assemble step, leaving only the recursive trailing envelope `Bs` explicit; the wrapper now also proves the envelope is nonnegative when `Bs` is |
| §4.2 fl **recursive all-1×1 backward-error envelope** | `flSchurCompl`, `FlAllOneSymmetricPivots`, `flBlockLDLTAllOneByOneBound`, `fl_blockLDLT_all_oneByOne_bound`, `higham11_3_fl_schurCompl`, `higham11_3_FlAllOneSymmetricPivots`, `higham11_3_fl_allOneByOneBound`, `higham11_3_fl_allOneByOneBound_nonneg`, `higham11_3_fl_blockLDLT_all_oneByOne_bound`, `higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne` | " | **new this session**; iterates the one-stage envelope by induction and constructs computed-style `L̂,D̂` factors under an explicit rounded nonzero-pivot + first-row/first-column symmetry side condition at every Schur stage. The recursive envelope is proved nonnegative, so the all-1×1 path is now packaged with explicit `ΔA₁, ΔA₂` witnesses in the source-facing interface shape. This proves the all-1×1 recursive path, but does **not** close printed Thm 11.3's mixed 1×1/2×2 pivot algorithm. |
| §4.2 stored-symmetric rounded Schur bridge | `flStoredSymSchurCompl`, `flStoredSymSchurCompl_symm`, `flStoredSymSchurCompl_first_row_col`, `higham11_3_fl_storedSymSchurCompl`, `higham11_3_fl_storedSymSchurCompl_symm`, `higham11_3_fl_storedSymSchurCompl_first_row_col` | " | **new this session**; formalizes "compute one triangle, copy across the diagonal" for the rounded Schur complement and proves the symmetry/first-row-column fact needed by recursive stage hypotheses. This is a bridge toward replacing explicit stage-symmetry assumptions by a stored-symmetric algorithm path. |
| §4.2 stored-Schur one-stage error bridge | `flStoredSymSchurDefect`, `fl_blockLDLT_oneByOne_stage_bound_of_stored_schur`, `higham11_3_fl_storedSymSchurDefect`, `higham11_3_fl_storedSymSchurDefect_nonneg`, `higham11_3_fl_blockLDLT_oneByOne_stage_bound_of_stored_schur` | " | **new this session**; if recursive factors approximate the stored-symmetric Schur complement within `B`, the one-stage bound holds with trailing envelope `B + |S_stored − S_raw|`. The storage defect is exposed as nonnegative, which is needed to package zero perturbations. This is the precise storage-defect bridge needed to connect symmetric storage to the existing raw-Schur analysis. |
| §4.2 fl **stored-symmetric recursive all-1×1 envelope** | `FlStoredAllOnePivots`, `flBlockLDLTStoredAllOneByOneBound`, `fl_blockLDLT_stored_all_oneByOne_bound`, `higham11_3_FlStoredAllOnePivots`, `higham11_3_fl_storedAllOneByOneBound`, `higham11_3_fl_storedAllOneByOneBound_nonneg`, `higham11_3_fl_blockLDLT_stored_all_oneByOne_bound`, `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne` | " | **new this session**; symmetric input + nonzero pivots along the stored-symmetric rounded Schur path ⇒ computed-style `L̂,D̂` factors with an accumulated componentwise envelope that includes the stored-vs-raw Schur defect at each level. The envelope is proved nonnegative and the all-1×1 stored path is packaged with explicit `ΔA₁, ΔA₂` witnesses in the source-facing interface shape. This removes the explicit per-stage symmetry hypothesis for the all-1×1 path. |
| §11.1 exact block-LDLᵀ step, eq (11.3) `s=1`: `∑ L·D·Lᵀ = A` | `oneByOne_step_factorization`, `higham11_3_oneByOne_step_factorization` | " | **new this session**; exact 1×1-pivot factorization identity (unit-lower-tri `L`, block-diag `D` with Schur complement) — the **exact base of Theorem 11.3's diagonal-pivoting recursion** (fl version adds `fl_oneByOne_schur_step_error`) |
| §11.1 exact block-LDLᵀ **inductive step**, eq (11.1)/(11.3) | `blockLDLT_assemble_step`, `higham11_3_blockLDLT_assemble_step` | " | **new this session**; trailing block factorized recursively (`L_S·D_S·L_Sᵀ = S`, IH) + 1×1 multipliers ⇒ assembled `∑ L·D·Lᵀ = A`; iterating gives the exact `PAPᵀ = LDLᵀ` recursion |
| §11.1 exact **full recursion**, eq (11.1)/(11.2): `∃ L D, ∑ L·D·Lᵀ = A` | `exact_blockLDLT_all_oneByOne`, `higham11_1_exact_blockLDLT_all_oneByOne` (+ `schurCompl`, `schurCompl_symm`, `AllOnePivots`) | " | **new this session**; symmetric `A` with all Schur-complement pivots nonzero ⇒ exact `LDLᵀ` (no-2×2-pivot case), by induction on `n` via `blockLDLT_assemble_step` — the exact factorization scaffold for Theorem 11.3 |
| Thm 11.4 constant, Higham [608,1997] eq (4.13): `(3+α²)(3+α)/(1−α²)² ≤ 36` | `bunch_kaufman_bound_const_le_36`, `higham11_4_bound_const_le_36` | " | **new this session**; the `36` in `‖\|L̂\|\|D̂\|\|L̂ᵀ\|‖_M ≤ 36nρₙ‖A‖_M` (α=(1+√17)/8) |
| Thm 11.4 constant, Higham [608,1997] (A.3): `(3+α²)/(1−α²) ≤ 6` (`\|E\|\|E⁻¹\|\|E\| ≤ 6\|E\|`) | `bunch_kaufman_pivot_norm_const_le_six`, `higham11_4_pivot_norm_const_le_six` | " | **new this session** |
| §11.1.2 1×1-pivot growth constant `1/α < 2` (Higham [608,1997]) | `bunch_kaufman_recip_alpha_lt_two`, `higham11_4_recip_alpha_lt_two` | " | **new this session**; `g_ij ≤ α⁻¹·max < 2·max` |
| α bounds `1/2 < α ≤ 5/7`, `α² = (α+1)/4` | `bunch_parlett_alpha_gt_half`, `bunch_parlett_alpha_le_5_7`, `bunch_parlett_alpha_sq` | " | **new this session**; supporting the Thm 11.4 constants |
| Eq (11.6) example factorization A = LDLᵀ (partial pivoting) | `higham11_6_partialPivotExample_factorization` | Ch11 | exact `fin_cases` algebra, ε≠0 |
| §11.3 skew-symmetric diag zero | `skewSymmetric_diag_zero`, `higham11_16_skew_diag_zero` | " | Aᵀ=−A ⇒ Aᵢᵢ=0 |
| §11.3 / Alg 11.9 skew 2×2 multiplier bound `|c/a₂₁| ≤ 1` | `skew_twoByTwo_multiplier_bound`, `higham11_9_skew_multiplier_bound` | " | **new this session**; from `|c| ≤ |a₂₁|` (pivot is max) — honest content behind `higham11_9_skew_L_entry_bound_interface` |
| §11.3 / Alg 11.9 skew Schur entry bound `|s| ≤ 3M` | `skew_twoByTwo_schur_entry_bound`, `higham11_9_skew_schur_entry_bound` | " | **new this session**; `s = a_ij − (a_{i2}/a₂₁)a_{j1} + (a_{i1}/a₂₁)a_{j2}` (printed formula); establishes `higham11_9_skewSchurEntryBound` |
| §11.2 Aasen recurrence eq (11.12) from `A=LH` | `higham11_12_aasen_diagonal_equation_of_product` | Ch11 | **new this session**; exact-arithmetic: unit-lower-tri `L` ⇒ `A i i = ∑_{j<i} L i j·H j i + H i i` |
| §11.2 Aasen recurrence eq (11.13) from `A=LH` | `higham11_13_aasen_subdiagonal_equation_of_product` | Ch11 | **new this session**; `k=i+1` ⇒ `A k i = ∑_{j≤i} L k j·H j i + H k i` — the Aasen recurrence structure (exact), toward Thm 11.8 |
| §11.2 Aasen band structure `H j i = 0` (`j>i+1`), from `H=TLᵀ` | `higham11_10_aasenH_band` | Ch11 | **new this session**; `T` tridiagonal + `L` lower-tri ⇒ `H` banded |
| §11.2 Aasen recurrence eq (11.14) next-column update from `A=LH` | `higham11_14_aasen_next_column_of_product` | Ch11 | **new this session**; `L k next = (A k i − ∑_{j≤i} L k j·H j i)/H next i` (`next=i+1`, `k≥i+2`, `H next i≠0`) — completes the exact Aasen recurrence trio (11.12)–(11.14) |
| §11.2 Aasen recurrence eq (11.14) scalar fl update | `higham11_14_fl_aasen_next_column_update_rel_error`, `higham11_14_fl_aasen_next_column_update_abs_error`, `higham11_14_fl_aasen_next_column_update_sum_abs_error`, `higham11_14_fl_aasen_next_column_update_abs_error_of_exact_recurrence` | Ch11 | **new this session**; proves `fl(fl(a-s)/h) = ((a-s)/h)(1+θ)`, `|θ| ≤ γ₂`, additive form `exact + Δ`, finite-sum specialization for `Aki − ∑_{j≤i}LkjHji`, and the exact-recurrence bridge `fl update = L k next + Δ`, `|Δ| ≤ γ₂|L k next|`; first local fl ingredient for the Aasen next-column update |
| §11.2 Aasen recurrence eq (11.14) rounded prefix-sum formation | `higham11_14_fl_aasenPrefixDot`, `higham11_14_fl_aasen_prefix_dot_abs_error`, `higham11_14_fl_aasenSourcePrefixDot`, `higham11_14_fl_aasen_source_prefix_dot_abs_error`, `higham11_14_fl_aasen_next_column_update_formed_sum_abs_error_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_formed_sum_single_abs_error_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_formed_sum_abs_sub_bound_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_source_prefix_abs_sub_bound_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_source_prefix_column_component_bound_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_source_prefix_Lhat_column_relative_bound_of_exact_recurrence`, `higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence` | Ch11 | **new this session**; masks the prefix `j≤i` into a fixed-length rounded dot product and proves its `γ_n` additive residual, also proves the tighter source-length prefix-dot residual with `γ_{i+1}` (`next.val = i.val+1`), combines source-prefix formation with the exact-recurrence update bridge, packages the formed-sum update as `L k next + Δ`, exposes direct componentwise inequalities, lifts the source-prefix scalar budget over the updated entries of the next column, packages one updated column as a relative `L_hat` factor bound, and dispatches those per-successor-column bounds to a global relative-factor hypothesis consumed by the Aasen factorization-product theorem |
| §11.2 Aasen solve chain eq (11.15), outer triangular solves | `higham11_15_fl_aasen_outer_triangular_solves_backward_error` | Ch11 | **new this session**; packages existing Chapter 8 forward/back substitution backward-error theorems for the two outer solves `Lz=Pb` and `Lᵀw=y` |
| §11.2 Aasen solve chain eq (11.15), middle tridiagonal solve | `higham11_15_fl_aasen_middle_tridiagonal_solve_backward_error` | Ch11 | **new this session**; consumes the Chapter 9 equation-(9.20) tridiagonal LU perturbation model for `T`, uses the actual rounded triangular solves, and returns `(T+ΔT)ŷ=z` with the equation-(9.22) `f(γ_n)|L̂||Û|` componentwise bound |
| §11.2 Aasen solve chain eq (11.15), rounded component package | `higham11_15_fl_aasen_solve_chain_backward_error_components` | Ch11 | **new this session**; composes the outer triangular-solve and middle tridiagonal-solve bridges into a single computed chain `ẑ,q̂,ŷ,ŵ,x̂` exposing all three perturbed equations |
| §11.2 Aasen solve chain eq (11.15), algebraic source collapse | `higham11_15_aasenChainDeltaA`, `higham11_15_aasenTripleTerm_abs_bound`, `higham11_15_aasenTripleTerm_abs_bound_gamma`, `higham11_15_aasenChainDeltaA_abs_bound_of_entrywise`, `higham11_15_aasenChainDeltaABound`, `higham11_15_aasenChainDeltaA_abs_bound_gamma`, `higham11_15_aasen_chain_source_backward_error_of_components` | Ch11 | **new this session**; collapses `(L+ΔL)(T+ΔT)(U+ΔU)` against `LTU=A` to obtain a single source equation `(A+ΔA)w=rhs`; also proves the scalar seven-term triple-product bound, its collected outer-`γ`/middle-budget specialization, the summation bridge, and the closed componentwise `higham11_15_aasenChainDeltaABound` for the collapsed perturbation |
| §11.2 Aasen solve chain eq (11.15), closed-budget norm aggregation | `higham11_15_aasenChainDeltaABound_nonneg`, `higham11_15_aasenMiddleSolveBudget_nonneg`, `higham11_15_aasenMiddleSolveBudget_infNorm_le`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_absLU`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_norm_bound`, `higham11_15_absLU_infNorm_le_of_componentwise_T_bound`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_colDiagDom_LUFactSpec`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_rowDiagDom_LUFactSpec`, `higham11_15_aasenChainDeltaABound_infNorm_le`, `higham11_15_infNorm_le_of_aasenChainDeltaABound` | Ch11 | **new this session**; proves the closed chain and middle tridiagonal-solve budgets are nonnegative, aggregates the middle budget both to `f(γ_n)‖L_T‖∞‖U_T‖∞` and directly to `f(γ_n)‖|L_T||U_T|‖∞`, provides relative factor-product and abs-LU norm forms, converts componentwise `|L_T||U_T|≤κ|T̂|` into the corresponding norm bound, and instantiates the concrete column- and row-dominant tridiagonal LUFactSpec `3|T̂|` Chapter 9 bounds; the closed chain's two scalar triple-product sums are aggregated into the normwise bound `(2γ+γ²)‖L‖∞‖T‖∞‖U‖∞ + (1+2γ+γ²)‖L‖∞‖BT‖∞‖U‖∞`, then transferred to any perturbation dominated componentwise by `higham11_15_aasenChainDeltaABound` |
| Thm 11.8 summed Aasen budget norm aggregation | `higham11_8_infNorm_le_of_sum_aasenChainDeltaABounds`, `higham11_8_aasenNormwiseBackwardBound_of_sum_aasenChainDeltaABounds` | Ch11 | **new this session**; if a source perturbation is bounded componentwise by the sum of two closed Aasen chain budgets, its `∞`-norm is bounded by the sum of the corresponding two-term normwise budgets; the new predicate bridge turns that scalar norm budget directly into the printed Theorem 11.8 normwise target, avoiding an entrywise `η|T̂|` comparison when a normwise scalar comparison is available |
| Thm 11.8 scalar norm-budget reducer | `higham11_8_aasen_factor_solve_coeff_le_of_parts`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds`, `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds`, `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_gamma_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_middle_factor_product_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_absLU_norm_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_absLU_componentwise_T_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff`, `higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff` | Ch11 | **new this session**; reduces the scalar norm-budget hypothesis for the factorization+solve wrapper to primitive `∞`-norm factor bounds for `L`, `Lᵀ`, `L̂`, `L̂ᵀ`, `T`, the factor `BT`, and the middle solve budget, plus one printed-coefficient inequality; the relative-factor reducers derive the `L̂` and `L̂ᵀ` norm constants as `(1+γ_factor)` times the source-factor constants from `|L̂-L|≤γ_factor|L|`, with either a monolithic coefficient inequality or four gamma-share obligations; the coefficient splitters let later work prove the four factorization/solve contributions separately, either as raw scalar pieces or as shares of the printed `(n−1)^2γ_{15n+25}` coefficient; the direct column/row-dominant variants accept the same four terms as one scalar sum; the middle-route reducers discharge the middle budget either from a separate factor product, the more concrete abs-LU norm or componentwise `|T̂|` bound, or directly from the column- or row-dominant tridiagonal LUFactSpec `3f(γ_n)` specializations |
| Thm 11.8 scalar coefficient product-cap helpers | `higham9_14_f_mono_nonneg`, `higham11_8_two_gamma_plus_sq_mul_le_of_le`, `higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_le`, `higham11_8_two_gamma_plus_sq_mul_le_of_majorants`, `higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_bounds`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_concrete_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_concrete_product_majorants` | Ch9/Ch11 | **new this session**; factors the four gamma-share coefficient comparisons through reusable product caps, larger gamma/product majorants, and monotonicity of Chapter 9's tridiagonal LU polynomial `f(u)=4u+3u²+u³`, so later work can prove product-size bounds, gamma-radius comparisons, and scaled gamma-share bounds separately before invoking the existing four-share splitter, discharge the same product-majorant route with one aggregate printed-coefficient inequality, or instantiate the product caps with the exact products from the relative Aasen norm budget in either aggregate or four-share form; the product-majorant reducers also transport the concrete middle term `f(γ_solve)κmidLU` through a larger `γ_mid_cap` |
| Thm 11.8 Aasen factorization product residual budget | `higham11_8_aasenFactorizationProductBudget`, `higham11_8_aasen_factorization_product_abs_bound_of_entrywise_factor_bounds`, `higham11_8_aasen_factorization_product_abs_bound_gamma`, `higham11_8_aasen_factorization_product_abs_bound_of_source_prefix_updates` | Ch11 | **new this session**; from exact `A=LTLᵀ` and entrywise factor budgets `|L̂−L|≤BL`, `|T̂−T|≤BT`, proves the product residual `|L̂T̂L̂ᵀ−A|` is bounded by an explicit seven-term double-sum budget; specializes relative `|L̂−L|≤γ|L|` and middle `|T̂−T|≤BT` budgets to the closed `higham11_15_aasenChainDeltaABound`; now also instantiates the relative `L_hat` factor hypothesis from the source-prefix rounded recurrence bridge, so the factorization-product residual can be consumed from the modeled next-column updates plus the remaining concrete `T_hat` budget |
| §11.2 Aasen solve chain eq (11.15), rounded source backward-error wrapper | `higham11_15_aasenMiddleSolveBudget`, `higham11_15_fl_aasen_solve_chain_source_backward_error_of_delta_bound`, `higham11_15_fl_aasen_solve_chain_source_backward_error` | Ch11 | **new this session**; instantiates the rounded component package and algebraic collapse, first under an explicit componentwise budget and then with the closed `higham11_15_aasenChainDeltaABound` generated from the outer `γ_n` solve bounds and the middle `f(γ_n)|L_T||U_T|` budget |
| Thm 11.8 factorization + solve-chain source wrapper | `higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals`, `higham11_8_fl_aasen_factor_solve_source_backward_error` | Ch11 | **new this session**; combines a factorization residual `A_fact−A` with a solve-chain residual `ΔS` into one source perturbation `ΔA`, then instantiates this for rounded Aasen solves with computed factors `L̂,T̂`, yielding `(A+ΔA)ŵ=Pᵀb` with componentwise budget `B_factor+B_solve` |
| §11.2 Aasen solve chain eq (11.15), exact unpermuted algebra | `higham11_15_aasenSolveChain_identity_solve_of_product` | Ch11 | **new this session**; if `A = L T Lᵀ` and the exact chain `Lz=b`, `Ty=z`, `Lᵀw=y`, `x=w` holds (identity permutation), then `A x = b`; this is the algebraic base for later rounded solve-chain perturbation |
| Thm 11.8 norm bridge: componentwise perturbation ⇒ `∞`-norm bound | `higham11_8_infNorm_le_card_mul_of_uniform_componentwise_bound`, `higham11_8_aasenNormwiseBackwardBound_of_uniform_componentwise_bound`, `higham11_8_infNorm_le_mul_of_componentwise_T_bound`, `higham11_8_infNorm_factor_le_of_relative_entry_bound`, `higham11_8_infNorm_factorTranspose_le_of_relative_entry_bound`, `higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound`, `higham11_8_componentwise_T_bound_add_of_parts`, `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound`, `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound_coeff_le` | Ch11 | **new this session**; if `|ΔAᵢⱼ| ≤ β`, then `‖ΔA‖∞ ≤ nβ`; if `|ΔAᵢⱼ| ≤ η|T̂ᵢⱼ|`, then `‖ΔA‖∞ ≤ η‖T̂‖∞`; relative factor perturbations `|L_hat-L|≤γ|L|` give `(1+γ)` bounds for `L_hat` and its transpose; all bridge into the printed `(n−1)^2γ_{15n+25}‖T̂‖∞` target once the scalar budget is available; the closed solve-chain budget `higham11_15_aasenChainDeltaABound` now feeds the same printed normwise predicate under an entrywise comparison to `η|T̂|`; the splitter combines separate factorization and solve-chain entrywise comparisons `η_factor|T̂|` and `η_solve|T̂|` when `η_factor+η_solve≤η`; the coefficient adapter accepts `η ≤ (n−1)^2γ_{15n+25}` and multiplies by `‖T̂‖∞` internally |
| Thm 11.8 solve-chain source + normwise wrapper | `higham11_8_fl_aasen_solve_chain_source_normwise_backward_error` | Ch11 | **new this session**; packages the rounded Aasen solve-chain source equation `(A+ΔA)ŵ=Pᵀb` with the printed normwise predicate once the closed chain budget is compared entrywise to `η|T̂|` and the scalar `(n−1)^2γ_{15n+25}` budget is supplied |
| Thm 11.8 primitive relative gamma-share source wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds_gamma_parts` | Ch11 | **new this session**; lifts the four-share `(n−1)^2γ_{15n+25}` coefficient interface from the scalar relative-factor reducer to the rounded source wrappers, both when the relative `L_hat` perturbation is supplied and when it is generated from the source-prefix rounded recurrence model |
| Thm 11.8 factorization+solve source + normwise wrapper | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets` | Ch11 | **new this session**; packages the rounded Aasen factorization and solve-chain source equation `(A+ΔA)ŵ=Pᵀb` together with the printed normwise predicate. The original wrapper uses an explicit entrywise comparison from the summed factorization+solve budgets to `η|T̂|`; the scalar norm wrapper accepts one normwise comparison from the summed closed budgets to `(n−1)^2γ_{15n+25}‖T̂‖∞`, and the factor-norm wrappers discharge that comparison from primitive `∞`-norm factor bounds plus one coefficient inequality, including variants where the computed `L̂`/`L̂ᵀ` norm bounds are derived from the relative entrywise factor perturbation, where the factorization-side `BT_factor` norm is derived from a componentwise `BT_factor≤κ|T̂|` bound, and source-prefix variants that generate the relative `L̂` factor hypothesis from the modeled rounded recurrence updates; the middle-factor-product and abs-LU wrappers replace the hand-supplied middle-budget norm with either a relative `‖L_T‖∞‖U_T‖∞` bound, the sharper `‖|L_T||U_T|‖∞` bound, or its componentwise `|T̂|` source; the combined wrappers consume componentwise bounds for both `BT_factor` and `|L_T||U_T|`; the column- and row-dominant wrappers use the concrete Chapter 9 `3f(γ_n)` middle coefficient, either as four scalar pieces or as one direct scalar sum, including source-prefix variants that also derive the computed `L̂`/`L̂ᵀ` norm bounds from the generated relative factor hypothesis and can derive the `BT_factor` norm from a componentwise `T_hat` comparison; the split-entry wrappers accept separate factorization and solve-chain entrywise comparisons and combine their coefficients |
| Thm 11.8 supplied-relative column/row middle wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff_componentwise_BT` | Ch11 | **new this session**; specialize the non-source factorization+solve source wrapper for the case where a relative `L_hat` perturbation hypothesis is already available, derive the computed `L_hat`/`L_hatᵀ` norms from it, use the concrete Chapter 9 column- or row-dominant `3f(γ_n)` middle coefficient, and optionally derive the `BT_factor` norm from a componentwise `T_hat` comparison |
| Thm 11.8 supplied/source-prefix relative middle/abs-LU wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_T_factor`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_T_factor`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_coeff_parts` | Ch11 | **new this session**; specialize the relative `L_hat` route for non-dominance middle-budget hypotheses: a relative `‖L_T‖∞‖U_T‖∞` product bound, including variants that derive the `BT_factor` norm from a componentwise `T_hat` comparison or instantiate `BT_factor` directly as `κBT|T_hat|`, a sharper `‖|L_T||U_T|‖∞` bound with split scalar coefficients, componentwise middle variants against `T_hat`, and combined componentwise variants deriving both the `BT_factor` and abs-LU middle norms from `T_hat` or instantiating the concrete `T_hat` factor budget directly; the source-prefix variants combine these with the generated relative `L_hat` hypothesis from rounded recurrence updates |
| Thm 11.8 concrete `T_hat` gamma-share/product-majorant wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts` | Ch11 | **new this session**; specializes the most concrete supplied/source-prefix relative abs-LU path where `|T_hat-T|≤κBT|T_hat|` and `|L_T||U_T|≤κmidLU|T_hat|`, while accepting either four shares of the printed `(n−1)^2γ_{15n+25}` coefficient, one aggregate product-cap/gamma-majorant coefficient inequality, or the same gamma-share/aggregate inequalities after the product caps have been instantiated by exact products; the product-majorant variants let callers supply coarser product caps and larger gamma radii, with the middle `f(γ)` term transported by Ch9 monotonicity |
| Problem-support algebra 11.1/11.2/11.4/11.7/11.8/11.9 | `higham11_problem_11_*` (see file) | Ch11 | reusable symmetric/SPD/quasidefinite algebra; not exercise transcriptions |

## Source predicates / definitions (honest models, no assumed conclusions)
- Eq (11.1) block LDLᵀ spec `BlockLDLTSpec`; (11.2) `higham11_2_NonsingularPivotBlock`;
  (11.3) `higham11_3_symmetricSchurComplement`; (11.4) `higham11_4_twoByTwoSchurEntry`.
- Alg 11.1/11.2/11.5/11.6/11.9 decision predicates: `BunchParlettCompletePivotChoice`,
  `BunchKaufmanPartialPivotCase`, `SymmetricRookFirstPivotChoice`,
  `BunchTridiagonalPivotChoice`, `SkewBunchPivotChoice`, plus `PivotSize`, `BunchKaufmanCase`.
- §11.2 Aasen: `AasenSpec`, `IsSymTridiagonal`, eqs (11.10)–(11.15) `higham11_1{0,2,3,4,5}_*`.
- §11.3 skew: `IsSkewSymmetric`, `IsSkewBlockDiag`, `SkewBlockLDLTSpec`, eq (11.16)
  `higham11_16_skewSchurComplement`.

## Reused from repository
| Source concept | Existing declaration | File |
|---|---|---|
| SPD predicate, symmetric part, nonsym-posdef | `IsSymPosDef`, `symmetricPart`, `IsNonsymPosDef`, `nonsymPosDef_iff_symPartSPD` | Ch10 / Cholesky |
| Permutation predicate | `IsPermutation` | LU/GaussianElimination |
| 2×2 principal-minor positivity (SPD) | `higham10_problem_10_1_two_by_two_minor_pos` | Ch10 |

## Open selected-scope items (not-proved ledger)
These are the rows that keep the gate FAIL. Each is currently a conditional-transfer
interface (`hypothesis ⊢ same statement`). **Update (2026-07-05):** the proofs are no
longer citation-blocked — Higham [608,1997] was obtained (see *External proof sources*
below), giving the full proof of Theorems 11.3/11.4. What remains is *formalizing* the
block-matrix backward-error **induction** (a large but now-unblocked, tractable effort);
this session proved the exact base case and the key constants.

| Source label | Exact claim | Current Lean status | Missing foundation | Smallest next Lean theorem |
|---|---|---|---|---|
| Theorem 11.3 | block LDLᵀ backward error: `P(A+ΔA₁)Pᵀ = L̂D̂L̂ᵀ`, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` (eq 11.5) | `higham11_3_block_ldlt_backward_error_interface` (assumes the whole conclusion) | **substantially advanced (all-1×1 case)**: proved the exact recursion (`exact_blockLDLT_all_oneByOne`), the component stage bounds, packaged all-index one-stage envelope with nonnegativity, raw-Schur recursive all-1×1 envelope, stored-symmetric rounded Schur bridge, storage-defect one-stage bridge, recursive stored-symmetric all-1×1 envelope (`fl_blockLDLT_stored_all_oneByOne_bound`, `higham11_3_fl_blockLDLT_stored_all_oneByOne_bound`), and source-facing all-1×1 perturbation packages (`higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne`, `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne`). NOTE: (11.5) for 2×2 pivots = **Problem 11.5 (benchmark-reserved)** → stays a hypothesis. | extend the induction to mixed 1×1/2×2 pivots while keeping the 2×2 solve bound as a hypothesis, then relate the accumulated envelope to the printed `p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` form |
| Theorem 11.4 | Bunch–Kaufman normwise stability `(A+ΔA)x̂=b`, `‖ΔA‖_M ≤ p(n)ρₙu‖A‖_M+O(u²)` via `‖|L̂||D̂||L̂ᵀ|‖_M ≤ 36nρₙ‖A‖_M` | `higham11_4_bunch_kaufman_stability` / `..._solve_backward_error_interface` (assume) | proof now available (Higham [608,1997] §4.3, eqs 4.11–4.14, appendix A). The **constants** are proved (`bunch_kaufman_bound_const_le_36` = eq 4.13's `36`, `..._pivot_norm_const_le_six` = A.3, `..._recip_alpha_lt_two`). Remaining: the entrywise `|L||D||Lᵀ|` block bound (4.11)–(4.12) + recursion into (4.14) via `geom_growth_iterate`. | assemble the per-pivot `\|E\|\|E⁻¹\|\|E\|`/`CE⁻¹` entry bounds (constants proved) over the `‖S‖_M ≤ ρₙ‖A‖_M` recursion into eq (4.14) |
| Theorem 11.7 | Bunch tridiagonal normwise stability, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ c·u·‖A‖` | `higham11_7_tridiagonal_backward_error_interface` (assumes); Algorithm 11.6 branch tests, the accepted `2×2` pivot determinant lower bound/nonsingularity, inverse-entry bounds, the atomic rounded scalar Schur update, a `Fin 1` trailing-block one-stage printed-budget handoff, the ambient `Fin 3` first-stage embedding, the dimension-generic `Fin (n+3)` local-recursion embedding, trailing-block support packaging, support-preserving perturbation addition, offset-generic zero-prefix base/add packaging including printed-coefficient variants, mixed-depth accumulation, and the offset-two bridge, first local+recursive residual accumulation with printed coefficient addition, the recursive trailing-subproblem perturbation lift, recursive scalar residual composition, zero-prefix support shifting under recursive lifts, leading-support versions of the subproblem and recursive-residual accumulators, the solve-side `ΔA₂` bridge into the source-facing interface with separate nonnegative and direct inf-norm budget forms, the entrywise `|Aᵢⱼ|≤‖A‖∞` bridge for local `Amax` hypotheses, componentwise-to-∞-norm aggregation and source-side norm-bound packaging, and the trailing-subproblem offset/injectivity bookkeeping for the `2×2` tridiagonal step are now proved | tridiagonal block-LDLᵀ fl analysis | turn the subproblem-lifted local+recursive perturbation into a recursive theorem over the full tridiagonal block-LDLᵀ path, then aggregate it to the normwise theorem |
| Theorem 11.8 | Aasen componentwise backward error + `‖ΔA‖_∞ ≤ (n−1)²γ_{15n+25}‖T̂‖_∞` | `higham11_8_aasen_backward_error_interface` (assumes) | remaining: **fl** analysis of the Aasen recurrences + solve chain (11.15). The **exact-arithmetic** recurrence identities (11.12), (11.13), (11.14) are proved; scalar and finite-sum fl additive error forms of (11.14), including the exact-recurrence bridge to `L k next`, are proved; rounded prefix-dot formation residuals in both ambient `γ_n` and source-length `γ_{i+1}` forms are proved; source-prefix formed-update componentwise and column-lift bounds are proved; the source-prefix column budget is packaged into the relative `L_hat` factor hypothesis for one next-column update and then dispatched to the global relative-factor hypothesis; that source-prefix global bridge now feeds the factorization-product residual directly, leaving the concrete `T_hat` budget as the factorization side's remaining modeled input; the factorization-product residual is bounded by an explicit seven-term budget from entrywise `L̂`/`T̂` factor budgets and by the closed `higham11_15_aasenChainDeltaABound` under relative outer-factor bounds; the exact unpermuted solve-chain algebra is proved; the two outer triangular solves in (11.15) are connected to existing backward-error theorems; the middle tridiagonal solve is connected to Chapter 9's equation-(9.20)--(9.22) source perturbation model; the middle budget is now proved nonnegative and norm-aggregated both to `f(γ_n)‖L_T‖∞‖U_T‖∞` and to the more concrete `f(γ_n)‖|L_T||U_T|‖∞`, with a column-dominant LUFactSpec specialization giving `3f(γ_n)‖T̂‖∞`; the rounded solve-chain components are packaged together; the algebraic collapse to `(A+ΔA)w=rhs` is proved and instantiated with the closed `higham11_15_aasenChainDeltaABound`; factorization and solve-chain residuals are combined into a single `(A+ΔA)ŵ=Pᵀb` source equation with summed componentwise budget; the closed chain budget is aggregated into a two-term normwise triple-product bound; a perturbation dominated by the sum of the factorization and solve-chain closed budgets now receives both the summed normwise budget and the printed normwise predicate when a scalar norm budget is supplied; the scalar norm-budget comparison can now be reduced to primitive factor norm bounds and split into four scalar coefficient pieces, and the rounded/source-prefix source wrappers consume that reduced form directly, including variants where the middle budget is discharged from a relative tridiagonal LU factor-product or abs-LU norm bound; the componentwise/closed-chain ⇒ printed `∞`-norm bridges are proved; the rounded solve-chain source equation is packaged with the printed normwise predicate, and the rounded factorization+solve source equation is packaged with that predicate under an explicit entrywise `η|T̂|` comparison, the scalar norm-budget comparison, separate factor/solve entrywise comparisons whose coefficients add to `η`, or a concrete `T_hat` abs-LU/product-majorant route with exact product majorants and either one aggregate coefficient inequality or four gamma-share inequalities, including the source-prefix generated `L_hat` case. | prove the aggregate or four-share coefficient comparisons for the exact-product `T_hat` abs-LU/product-majorant route, reducing the factorization and solve-chain budgets to the printed `(n−1)^2γ_{15n+25}` coefficient |

Both single-step §11.1.1 element-growth bounds are now proved: the 1×1 step
`(1+1/α)μ₀` (`oneByOne_schur_growth`) and the 2×2 step `(1+2/(1−α))μ₀`
(`twoByTwo_schur_growth`), the latter resting on the proved determinant magnitude
bound `twoByTwo_completePivot_absdet_lower` and the length-2 inner product over the
inverse-block entries. What remains for Theorem 11.4 is the *recursion*: iterating
these per-stage bounds over the whole factorization to obtain the growth factor
`ρₙ ≤ (1+α⁻¹)^{n−1}`, plus the `36nρₙ` product bound and the floating-point solve
error — the foundation tracked in the ledger row above.

## External proof sources
| Selected claim | Source and exact location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| Theorems 11.3, 11.4 (proofs not in book ch.11) | N. J. Higham, *Stability of the diagonal pivoting method with partial pivoting*, SIAM J. Matrix Anal. Appl. 18(1) (1997) 52–65 = book ref **[608]**. Free: `nhigham.com/wp-content/uploads/2022/11/high97d.pdf`, MIMS EPrints 344. Obtained 2026-07-05 (Max authorized web pull). | full proof: paper Thm 4.1 = book 11.3 (componentwise induction §4.2, eqs 4.6–4.10), paper Thm 4.2 = book 11.4 (norm bound §4.3, eqs 4.11–4.14, appendix A.1–A.3) | constants formalized (`bunch_kaufman_bound_const_le_36` eq 4.13, `..._pivot_norm_const_le_six` A.3, `..._recip_alpha_lt_two`); exact base `oneByOne_step_factorization`; per-step fl `fl_oneByOne_schur_step_error`/`_solve_backward_error` | **partially formalized**; block-matrix induction remains (unblocked, large). Paper's (4.5) 2×2-solve backward error = book **Problem 11.5 (benchmark-reserved)** → stays a hypothesis. |
| Theorem 11.7 | N. J. Higham, *Stability of block LDLᵀ factorization of a symmetric tridiagonal matrix*, Linear Algebra Appl. 287 (1999) 181–189 = ref **[613]**. Free (NA report): `maths.manchester.ac.uk/~higham/narep/narep308.pdf`. Located 2026-07-05, not yet formalized. | tridiagonal block-LDLᵀ stability proof | — | located; formalization is later multi-session fl work |
| Theorem 11.8 | Higham **[612, 1999]** (Aasen backward error) — precise ref identified, free PDF not yet located | Aasen backward-error proof | exact recurrences (11.12)–(11.14) proved | to locate |

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| Ch 11 epigraphs (Bunch–Kaufman, Bunch quotes) | motivation | editorial |
| §11.1.2 "no example known to attain the bound", timing "≈40%" | empirical observation | empirical, no formalizable subclaim |
| §11.4 Notes and References, LAPACK/LINPACK pointers | historical / software | non-mathematical |

## Benchmark-reserved (identifiers only — NOT formalized as chapter work)
Problems 11.1–11.7, 11.9, 11.10 and Appendix A solutions 11.1, 11.3, 11.4, 11.7, 11.8, 11.9
are benchmark-reserved. Some independent, reusable symmetric/SPD/quasidefinite algebra facts
carry `higham11_problem_11_*` names; they are general lemmas (e.g. singular-principal-pivots ⇒
zero matrix, quasidefinite kernel-trivial), not transcriptions of the exercise tasks, and are
used only as chapter infrastructure.

**Important scope note (Problem 11.5).** Problem 11.5 asks to prove that condition
(11.5) — `(E+ΔE)ŷ=f`, `|ΔE| ≤ (cu+O(u²))|E|` — holds for the 2×2 pivots when the
system is solved by GEPP or the explicit inverse. This is exactly the *hypothesis*
of Theorem 11.3. Because Problem 11.5 is benchmark-reserved, (11.5) for 2×2 pivots
must remain a **hypothesis** of any honest Theorem 11.3 formalization and must not be
proved as chapter work. The 1×1 instance of (11.5) is *not* the reserved problem
(1×1 pivots "involve no computation" per §11.3) and is proved as
`fl_oneByOne_solve_backward_error`; the atomic 1×1 Schur-update fl error
(`fl_oneByOne_schur_step_error`) is likewise general chapter infrastructure, not a
Problem transcription.

## Hidden-hypothesis summary
- New lemmas (`oneByOne_multiplier_bound`, `oneByOne_schur_growth`,
  `twoByTwo_completePivot_det_bound`, `twoByTwo_completePivot_absdet_lower`,
  `twoByTwo_schur_growth`): all hypotheses are on the *data* (entry magnitudes
  `≤ μ₀/μ₁/ω`, pivot-acceptance `α·μ₀ ≤ |e|`, inverse-entry bounds `≤ αK,K` with the
  *equational* scale constraint `(1−α²)μ₀K = 1`, α range), never on the conclusion. The
  growth/determinant bounds are derived, not assumed. The self-contained corollary
  `twoByTwo_schur_growth_of_block` additionally *discharges* the inverse-entry
  hypotheses via `twoByTwo_inverse_entry_bounds`, so the 2×2 growth follows from the
  pivot-block data alone.
- Interface theorems (11.3/11.4/11.7/11.8): the analytic bound IS taken as a hypothesis and
  restated — this is exactly why those rows are logged OPEN, not closed.

## Verification
- Commands:
  - `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`.
  - 2026-07-07 norm-budget bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    post-merge full `lake build` → `Build completed successfully (3800 jobs)`.
  - 2026-07-07 split-entry budget bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_componentwise_T_bound_add_of_parts` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`;
    post-merge full `lake build` → `Build completed successfully (3800 jobs)`.
  - 2026-07-07 source-prefix split-entry wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`;
    post-merge full `lake build` → `Build completed successfully (3800 jobs)`.
  - 2026-07-07 scalar norm-budget reducer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`;
    post-merge full `lake build` → `Build completed successfully (3800 jobs)`.
  - 2026-07-07 factor-norm source wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`;
    post-merge full `lake build` → `Build completed successfully (3800 jobs)`.
  - 2026-07-07 source-prefix factor-norm wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`;
    post-merge full `lake build` → `Build completed successfully (3800 jobs)`.
  - 2026-07-07 middle factor-product norm increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_15_aasenMiddleSolveBudget_infNorm_le`,
    `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_middle_factor_product_bound`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_middle_factor_product_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 abs-LU middle budget and coefficient-parts increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_15_aasenMiddleSolveBudget_infNorm_le_absLU`,
    `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_norm_bound`,
    `higham11_15_absLU_infNorm_le_of_componentwise_T_bound`,
    `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound`,
    `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_colDiagDom_LUFactSpec`,
    `higham11_8_aasen_factor_solve_coeff_le_of_parts`,
    `higham11_8_aasen_factor_solve_norm_budget_of_middle_factor_product_coeff_parts`, and
    `higham11_8_aasen_factor_solve_norm_budget_of_absLU_norm_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 column-dominant middle coefficient reducer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 column-dominant middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 source-prefix column-dominant middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 row-dominant middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_rowDiagDom_LUFactSpec`,
    `higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff_parts`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff_parts`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 abs-LU middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_norm_coeff_parts` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_norm_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 componentwise abs-LU middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_norm_budget_of_absLU_componentwise_T_coeff_parts`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_componentwise_T_coeff_parts`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_componentwise_T_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 componentwise BT-factor wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds_componentwise_BT` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds_componentwise_BT`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 combined componentwise BT and middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_componentwise_BT_absLU_componentwise_T_coeff_parts` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_componentwise_BT_absLU_componentwise_T_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 relative factor norm increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_infNorm_factor_le_of_relative_entry_bound` and
    `higham11_8_infNorm_factorTranspose_le_of_relative_entry_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 derived relative factor norm wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 direct column/row middle coefficient reducer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff` and
    `higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 direct column/row middle source-wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 direct source-prefix column/row middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 relative source-prefix column/row middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 relative source-prefix column/row middle componentwise-BT wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff_componentwise_BT` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff_componentwise_BT`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 supplied-relative column/row middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff_componentwise_BT`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff_componentwise_BT`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 supplied-relative middle/abs-LU wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_norm_coeff_parts`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_componentwise_BT_absLU_componentwise_T_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 source-prefix relative abs-LU wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_norm_coeff_parts` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_componentwise_BT_absLU_componentwise_T_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 supplied/source-prefix relative abs-LU componentwise-middle wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_coeff_parts` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 relative middle-factor-product componentwise-BT wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_BT` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_BT`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 relative middle-factor-product concrete `T_hat` factor-budget wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_T_factor` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_T_factor`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 relative abs-LU concrete `T_hat` factor-budget wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_coeff_parts` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_coeff_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 coefficient share splitter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 relative-factor gamma-share norm-budget reducer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_gamma_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 source-wrapper gamma-share relative-factor increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds_gamma_parts`
    and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds_gamma_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 concrete `T_hat` factor gamma-share wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_parts`
    and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 scalar coefficient product-cap helper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` → pass;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham9_14_f_mono_nonneg`,
    `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_bounds`
    plus the four coefficient transport helpers → elaborate; axioms
    `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 scalar coefficient product-majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-07 concrete `T_hat` product-majorant source-wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    focused lookup/axiom check of
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants`
    and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 aggregate product-majorant coefficient increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_coeff_le_of_product_majorants`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants_coeff`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants_coeff`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 concrete-product majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_coeff_le_of_concrete_product_majorants`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 four-share concrete-product majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_concrete_product_majorants`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Algorithm 11.6 tridiagonal alpha increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `bunch_tridiagonal_alpha_pos`, `bunch_tridiagonal_alpha_lt_one`,
    `bunch_tridiagonal_alpha_sq`, and their `higham11_6_` wrappers
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Algorithm 11.6 tridiagonal pivot-choice increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `bunch_tridiagonal_pivot_choice_one_threshold`,
    `bunch_tridiagonal_pivot_choice_two_threshold`,
    `bunch_tridiagonal_pivot_choice_one_of_threshold`,
    `bunch_tridiagonal_pivot_choice_two_of_threshold`,
    `bunch_tridiagonal_pivot_choice_one_a11_ne_zero_of_a21_ne_zero`,
    `bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg`,
    `bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg`,
    and the corresponding `higham11_6_tridiagonal_pivot_choice_*` wrappers
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 determinant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound`,
    `bunch_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound`,
    `higham11_7_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound`, and
    `higham11_7_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 inverse-entry increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `bunch_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound` and
    `higham11_7_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 scalar fl-update increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_schur_step_error` and
    `higham11_7_fl_tridiagonal_twoByTwo_schur_step_error`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 source-shaped fl-budget increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound` and
    `higham11_7_fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 scalar backward-error-form increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound` and
    `higham11_7_fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 uniform scalar-bound increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound` and
    `higham11_7_fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 trailing one-stage increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_trailing_one_stage_bound` and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 trailing printed-budget increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound` and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 first-stage embedding increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three` and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 local-recursion embedding increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed` and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 trailing-subproblem index increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `tridiagonalTwoByTwoTrailingSubproblemIndex_zero`,
    `tridiagonalTwoByTwoTrailingSubproblemIndex_injective`,
    `higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex_zero`, and
    `higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex_injective`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 trailing-block support increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `TridiagonalTwoByTwoTrailingBlockSupport`,
    `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support`,
    `higham11_7_TridiagonalTwoByTwoTrailingBlockSupport`, and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 support-add combiner increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `tridiagonalTwoByTwoTrailingBlockSupport_add_bound` and
    `higham11_7_tridiagonalTwoByTwoTrailingBlockSupport_add_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 local+recursive accumulation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate` and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 printed-coefficient accumulation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed` and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 recursive-subproblem lift increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support`,
    `higham11_7_tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support`,
    `fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate`, and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 recursive residual composition increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate` and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 recursive support-shift increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport` and
    `higham11_7_tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal 2×2 packaged recursive support lift increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of
    `tridiagonalTwoByTwoLiftTrailingPerturbation_bound_leadingBlockSupport` and
    `higham11_7_tridiagonalTwoByTwoLiftTrailingPerturbation_bound_leadingBlockSupport`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal recursive zero-prefix support base/add increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `tridiagonalLeadingBlockSupport_zero_bound`,
    `tridiagonalLeadingBlockSupport_add_bound`,
    `higham11_7_tridiagonalLeadingBlockSupport_zero_bound`, and
    `higham11_7_tridiagonalLeadingBlockSupport_add_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal recursive printed zero-prefix support increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `tridiagonalLeadingBlockSupport_zero_printed_bound`,
    `tridiagonalLeadingBlockSupport_add_bound_printed`,
    `tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport`,
    `higham11_7_tridiagonalLeadingBlockSupport_zero_printed_bound`,
    `higham11_7_tridiagonalLeadingBlockSupport_add_bound_printed`, and
    `higham11_7_tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal recursive mixed-depth support increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `tridiagonalLeadingBlockSupport_of_le_offset`,
    `tridiagonalLeadingBlockSupport_add_bound_of_le_offset`,
    `tridiagonalLeadingBlockSupport_add_bound_printed_of_le_offset`,
    `higham11_7_tridiagonalLeadingBlockSupport_of_le_offset`,
    `higham11_7_tridiagonalLeadingBlockSupport_add_bound_of_le_offset`, and
    `higham11_7_tridiagonalLeadingBlockSupport_add_bound_printed_of_le_offset`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal recursive leading-support accumulation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite` → `Build completed successfully (2979 jobs)`;
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate_leadingBlockSupport`,
    `fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport`,
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate_leadingBlockSupport`, and
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal solve-side interface bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_solve_delta`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal solve-side nonnegative-budget bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal entrywise infinity-norm bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_7_abs_entry_le_infNorm`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal direct inf-norm solve bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal componentwise-to-infinity-norm bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_7_infNorm_le_card_mul_of_uniform_componentwise_bound` and
    `higham11_7_infNorm_le_card_mul_of_printed_componentwise_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.7 tridiagonal solve-side norm-bound packaging increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_with_norm_bounds` and
    `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm_with_norm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.3 all-1×1 source-facing package increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_3_fl_oneByOneStageBound_nonneg`,
    `higham11_3_fl_storedAllOneByOneBound_nonneg`,
    `higham11_3_fl_allOneByOneBound_nonneg`,
    `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne`, and
    `higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - `lake env lean examples/LibraryLookup.lean` → still aborts with the pre-existing stack overflow in the older IEEE lookup section before reaching the Chapter 11 checks; the focused Chapter 11 lookup/axiom check below was used for this milestone.
  - Focused lookup check of `higham11_3_fl_blockLDLT_all_oneByOne_bound` → elaborates.
  - Focused lookup check of `higham11_3_fl_storedSymSchurCompl_symm` → elaborates.
  - Focused lookup check of `higham11_3_fl_blockLDLT_oneByOne_stage_bound_of_stored_schur` → elaborates.
  - Focused lookup check of `higham11_3_fl_blockLDLT_stored_all_oneByOne_bound` → elaborates.
  - Focused lookup check of `higham11_8_infNorm_le_card_mul_of_uniform_componentwise_bound` → elaborates.
  - Focused lookup check of `higham11_8_aasenNormwiseBackwardBound_of_uniform_componentwise_bound` → elaborates.
  - Focused lookup check of `higham11_8_infNorm_le_mul_of_componentwise_T_bound` → elaborates.
  - Focused lookup check of `higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound` → elaborates.
  - Focused lookup check of `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound` → elaborates.
  - Focused lookup check of `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound_coeff_le` → elaborates.
  - Focused lookup check of `higham11_8_fl_aasen_solve_chain_source_normwise_backward_error` → elaborates.
  - Focused lookup/axiom check of `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error` → elaborates; axioms `[propext, Classical.choice, Quot.sound]`.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_rel_error` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_abs_error` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_sum_abs_error` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_abs_error_of_exact_recurrence` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_prefix_dot_abs_error` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_source_prefix_dot_abs_error` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_formed_sum_abs_error_of_exact_recurrence` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_formed_sum_single_abs_error_of_exact_recurrence` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_formed_sum_abs_sub_bound_of_exact_recurrence` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_source_prefix_abs_sub_bound_of_exact_recurrence` → elaborates.
  - Focused lookup check of `higham11_14_fl_aasen_next_column_update_source_prefix_column_component_bound_of_exact_recurrence` → elaborates.
  - Focused lookup/axiom check of `higham11_14_fl_aasen_next_column_source_prefix_Lhat_column_relative_bound_of_exact_recurrence` → elaborates; axioms `[propext, Classical.choice, Quot.sound]`.
  - Focused lookup/axiom check of `higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence` → elaborates; axioms `[propext, Classical.choice, Quot.sound]`.
  - Focused lookup check of `higham11_15_fl_aasen_outer_triangular_solves_backward_error` → elaborates.
  - Focused lookup check of `higham11_15_fl_aasen_middle_tridiagonal_solve_backward_error` → elaborates.
  - Focused lookup check of `higham11_15_fl_aasen_solve_chain_backward_error_components` → elaborates.
  - Focused lookup check of `higham11_15_aasenChainDeltaA` → elaborates.
  - Focused lookup check of `higham11_15_aasenTripleTerm_abs_bound` → elaborates.
  - Focused lookup check of `higham11_15_aasenTripleTerm_abs_bound_gamma` → elaborates.
  - Focused lookup check of `higham11_15_aasenChainDeltaA_abs_bound_of_entrywise` → elaborates.
  - Focused lookup check of `higham11_15_aasenChainDeltaABound` → elaborates.
  - Focused lookup check of `higham11_15_aasenChainDeltaA_abs_bound_gamma` → elaborates.
  - Focused lookup check of `higham11_15_aasenChainDeltaABound_nonneg` → elaborates.
  - Focused lookup check of `higham11_15_aasenChainDeltaABound_infNorm_le` → elaborates.
  - Focused lookup check of `higham11_15_infNorm_le_of_aasenChainDeltaABound` → elaborates.
  - Focused lookup/axiom check of `higham11_8_infNorm_le_of_sum_aasenChainDeltaABounds` → elaborates; axioms `[propext, Classical.choice, Quot.sound]`.
  - Focused lookup/axiom check of `higham11_15_aasenMiddleSolveBudget_nonneg`,
    `higham11_8_aasenNormwiseBackwardBound_of_sum_aasenChainDeltaABounds`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - Focused lookup check of `higham11_8_aasenFactorizationProductBudget` → elaborates.
  - Focused lookup check of `higham11_8_aasen_factorization_product_abs_bound_of_entrywise_factor_bounds` → elaborates.
  - Focused lookup check of `higham11_8_aasen_factorization_product_abs_bound_gamma` → elaborates.
  - Focused lookup/axiom check of `higham11_8_aasen_factorization_product_abs_bound_of_source_prefix_updates` → elaborates; axioms `[propext, Classical.choice, Quot.sound]`.
  - Focused lookup check of `higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals` → elaborates.
  - Focused lookup check of `higham11_8_fl_aasen_factor_solve_source_backward_error` → elaborates.
  - Focused lookup check of `higham11_15_aasenMiddleSolveBudget` → elaborates.
  - Focused lookup check of `higham11_15_aasen_chain_source_backward_error_of_components` → elaborates.
  - Focused lookup check of `higham11_15_fl_aasen_solve_chain_source_backward_error_of_delta_bound` → elaborates.
  - Focused lookup check of `higham11_15_fl_aasen_solve_chain_source_backward_error` → elaborates.
  - Focused lookup check of `higham11_15_aasenSolveChain_identity_solve_of_product` → elaborates.
  - `#print axioms` on the new declarations (`oneByOne_multiplier_bound`,
    `oneByOne_schur_growth`, `twoByTwo_completePivot_det_bound`,
    `twoByTwo_completePivot_absdet_lower`, `twoByTwo_schur_growth`, `abs_triple_mul_le`,
    and the `higham11_*` wrappers) → `[propext, Classical.choice, Quot.sound]`
    (no `sorryAx`, no custom axioms).
  - Placeholder scan `grep -nE 'sorry|admit|^\s*axiom |native_decide|unsafe '` over ch11 +
    CholeskyIndefinite → clean.
- New vs pre-existing warnings: **no new warnings** from the two edited files. The only build
  warnings are pre-existing in `HighamChapter10.lean` (an unused-simp-arg hint, one unused
  variable `hm`, and `Fin.coe_castAdd`/`Fin.coe_natAdd` deprecations).

## Documentation
- Inventory + report: `docs/source_coverage/higham_ch11.md` (this file).
- Not-proved ledger: the "Open selected-scope items" table above (4 primary theorems: 11.3, 11.4, 11.7, 11.8). The 2×2 growth sub-step listed there last session is now proved (`twoByTwo_schur_growth`).

## Open issues
- Gate is FAIL by design: Theorems 11.3/11.4/11.7/11.8 remain conditional-transfer
  interfaces. This session added the honest per-step §11.1.1 element-growth,
  multiplier, and determinant lemmas — **both** single-step growth bounds
  (`oneByOne_schur_growth` `(1+1/α)μ₀`, `twoByTwo_schur_growth` `(1+2/(1−α))μ₀`) and the
  2×2 determinant nonsingularity bound — the genuine building blocks of the Theorem 11.4
  growth-factor bound, all derived from the pivot-acceptance tests. Converting the
  interfaces to end-to-end proofs requires (i) the per-stage-to-`ρₙ` recursion, (ii) the
  `36nρₙ` product bound, and (iii) the block-LDLᵀ / Aasen floating-point backward-error
  foundation — a multi-session effort tracked in the not-proved ledger.
