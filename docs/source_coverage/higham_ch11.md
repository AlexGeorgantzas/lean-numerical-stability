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
| Thm 11.7 finite support-sum aggregation | `higham11_7_tridiagonalLeadingBlockSupport_sum_bound`, `higham11_7_tridiagonalLeadingBlockSupport_sum_uniform_bound`, `higham11_7_tridiagonalLeadingBlockSupport_sum_bound_with_norm`, `higham11_7_tridiagonalLeadingBlockSupport_sum_uniform_bound_with_norm`, `higham11_7_tridiagonalLeadingBlockSupport_sum_bound_of_le_offsets`, `higham11_7_tridiagonalLeadingBlockSupport_sum_bound_with_norm_of_le_offsets`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_nonneg`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_nonneg`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_of_le_offsets`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_of_le_offsets`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_of_le_offsets_nonneg`, `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_of_le_offsets_nonneg` | Ch11 | **new this session**; finite same-ambient families of zero-prefix supported perturbations can now be summed while preserving zero-prefix support and summing their componentwise budgets; the uniform form packages the common-bound case as `k*β`, the norm variants carry the induced row-sum `∞`-norm bound `m*Σβ` or `m*(k*β)`, mixed-offset variants first lower deeper zero-prefix support to a common shallower offset, the printed-coefficient forms specialize this to `(Σc)uAmax` and `kc u Amax`, mixed-offset printed forms combine those two adaptations, and the nonnegative forms derive product-budget nonnegativity from separate `c`, `u`, and `Amax` nonnegativity. This is the first finite-family aggregation layer needed after extracting per-branch witnesses. |
| Thm 11.7 recursive residual norm aggregation | `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_with_norm_bound`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_with_norm_bound_nonneg` | Ch11 | **new this session**; extends the zero-prefix supported local+recursive `2×2` tridiagonal residual accumulator with the induced row-sum bound `‖ΔA‖∞ ≤ (n+3)(c_bound+c_rec)uAmax`, preserving the scalar residual equation and support package; the nonnegative form derives the combined printed-budget side condition from separate nonnegativity of the local/recursive coefficients, unit roundoff, and `Amax` |
| Thm 11.7 local `2×2` matrix-entry norm bridge | `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_exact_inverse_ratio`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_exact_inverse_ratio_of_pivot_bounds`, `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_infNorm_choice` | Ch11 | **new this session**; specializes the local+recursive `2×2` accumulator to the actual trailing diagonal and coupling entries in an ambient `Fin (n+3)` matrix, deriving the local `|b|≤Amax` and `|c|≤Amax` hypotheses from `Amax=‖A‖∞`. The exact-inverse-ratio variants choose `κ = σ/((1-α)a₂₁²)` directly, derive its nonnegativity from the accepted `2×2` branch, and in the pivot-bound form derive `σ≥0` from `|a11|≤σ`; the `σ=‖A‖∞` endpoint ties the pivot scalars to the leading matrix entries and derives the pivot-entry bounds from `‖A‖∞`, removing another scalar handoff before the remaining full tridiagonal recursion theorem. |
| Thm 11.7 local `1×1` matrix-entry norm bridge | `higham11_7_tridiagonalOneByOneFirstTrailingIndex`, `higham11_7_tridiagonalOneByOneTrailingSubproblemIndex`, `higham11_7_tridiagonalOneByOneLiftTrailingPerturbation`, `higham11_7_tridiagonalOneByOneLiftTrailingPerturbation_bound_leadingBlockSupport`, `higham11_7_tridiagonal_oneByOne_correction_le_of_choice`, `higham11_7_fl_tridiagonal_oneByOne_schur_step_printed_bound_of_choice`, `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_with_norm_bound`, `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries`, `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_of_subdiagonal_ne_zero`, `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_infNorm_choice_of_subdiagonal_ne_zero` | Ch11 | **new this session**; adds the offset-one trailing-subproblem embedding for Algorithm 11.6's `1×1` branch, packages the lifted recursive tail with bound/support/embedded-entry identity, derives the local correction bound `|a21*a21/a11|≤Amax/α` from the printed one-pivot threshold plus `σ≤Amax`, packages the rounded first trailing Schur scalar with a recursive tail residual in a dimension-generic `Amax` theorem, specializes it to `Amax=‖A‖∞` with the resulting componentwise and `∞`-norm perturbation bounds, adds a branch-derived wrapper that obtains the required nonzero leading pivot from the accepted `1×1` branch plus nonzero subdiagonal coupling, and exposes a direct `σ=‖A‖∞` choice wrapper for the recursive branch. This is the `1×1` companion to the existing `2×2` local accumulator, not the full mixed-pivot recursion theorem. |
| Thm 11.7 mixed local-branch adapter | `higham11_7_tridiagonalBranchAmbientDim`, `higham11_7_TridiagonalBranchMatrix`, `higham11_7_tridiagonalBranchLeadingIndex`, `higham11_7_tridiagonalBranchFirstTrailingIndex`, `higham11_7_tridiagonalTwoByTwoSecondPivotIndex`, `higham11_7_tridiagonalBranchSupportOffset`, `higham11_7_TridiagonalBranchLocalAssumptions`, `higham11_7_TridiagonalBranchLocalResidual`, `higham11_7_tridiagonalBranchLocalResidual_of_localAssumptions` | Ch11 | **new this session**; packages the accepted local `1×1` or `2×2` tridiagonal branch into a common `PivotSize`-indexed residual interface, deriving it from the existing branch-specific local-recursive theorems while keeping the recursive tail certificate explicit. This is the adapter the future mixed-pivot path induction can consume; it does not assume or close the full recursive theorem. |
| Thm 11.7 terminal-tail branch adapter | `higham11_7_tridiagonalRecursiveTailZeroResidual`, `higham11_7_tridiagonalRecursiveTailZeroResidual_infNorm`, `higham11_7_TridiagonalBranchTerminalAssumptions`, `higham11_7_tridiagonalBranchLocalResidual_of_terminalTailAssumptions` | Ch11 | **new this session**; supplies the zero recursive-tail certificate for the terminal local branch and packages either accepted branch into the common branch residual when `tail_fl = tail_exact`. This gives the future mixed-pivot path induction a base case companion to the branch-indexed local step adapter. |
| Thm 11.7 finite mixed-pivot path interface | `higham11_7_TridiagonalBranchPathLocalAssumptions`, `higham11_7_TridiagonalBranchPathLocalResiduals`, `higham11_7_tridiagonalBranchPathLocalResiduals_of_localAssumptions`, `higham11_7_TridiagonalBranchPathTerminalAssumptions`, `higham11_7_tridiagonalBranchPathLocalResiduals_of_terminalTailAssumptions`, `higham11_7_tridiagonalBranchPathLocalResiduals_empty`, `higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_localAssumptions`, `higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_terminalTailAssumptions`, `higham11_7_tridiagonalBranchPathLocalAssumptions_head`, `higham11_7_tridiagonalBranchPathLocalAssumptions_tail`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_head`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_tail`, `higham11_7_tridiagonalBranchPathLocalResiduals_head`, `higham11_7_tridiagonalBranchPathLocalResiduals_tail` | Ch11 | **new this session**; lifts the branch-local and terminal-tail adapters pointwise over a finite family of `1×1`/`2×2` tridiagonal branch choices with per-step dimensions, matrices, budgets, and tail scalars. The empty and singleton adapters expose the induction base and one-step entry points; the head/tail projections expose the elimination side for future induction. This is path-level scaffolding for the remaining mixed-pivot induction; it still leaves the global accumulation of those pointwise residuals open. |
| Thm 11.7 finite mixed-pivot path witness extraction | `higham11_7_tridiagonalBranchLocalResidual_exists_supported_witness`, `higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses`, `higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses`, `higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses_of_uniform_budgets`, `higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses_of_uniform_budgets`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses_of_uniform_budgets` | Ch11 | **new this session**; extracts explicit per-branch perturbation matrices from branch-local, finite-path residual, path-local-assumption, and terminal-tail-assumption packages, retaining the componentwise budget, leading-block support, and `∞`-norm bound needed by the later global accumulation theorem. Uniform-budget variants package supplied per-branch scalar comparisons into the extracted witnesses directly. |
| Thm 11.7 solve-side interface bridge | `higham11_7_tridiagonal_backward_error_interface_of_solve_delta`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_nonneg`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm` | Ch11 | **new this session**; if the recursive tridiagonal analysis constructs the solve-side perturbation `ΔA₂` with the printed componentwise budget, the factorization-side perturbation `ΔA₁` can be filled by zero to produce the source-facing Theorem 11.7 interface shape; the `_nonneg` form derives `0 ≤ c*u*Amax` from separate nonnegativity of `c`, `u`, and `Amax`, and the `_infNorm` form specializes the budget to `c*u*‖A‖∞` |
| Thm 11.7 entrywise infinity-norm bridge | `higham11_7_abs_entry_le_infNorm` | Ch11 | **new this session**; row-sum bridge showing every entry satisfies `|Aᵢⱼ| ≤ ‖A‖∞`, used to discharge local scalar `Amax` hypotheses from a norm budget |
| Thm 11.7 componentwise-to-infinity-norm bridge | `higham11_7_infNorm_le_card_mul_of_uniform_componentwise_bound`, `higham11_7_infNorm_le_card_mul_of_printed_componentwise_bound` | Ch11 | **new this session**; aggregates a uniform componentwise perturbation budget to an infinity-norm bound by row sums, with the printed `c*u*Amax` form exposed for the final normwise theorem |
| Thm 11.7 solve-side norm-bound packaging | `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_with_norm_bounds`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm_with_norm_bounds`, `higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_uniform_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm_of_le_offsets` | Ch11 | **new this session**; carries the recursive solve perturbation through the source-facing interface while also recording `‖ΔA₁‖∞` and `‖ΔA₂‖∞` bounds obtained from the componentwise budget, including the direct `Amax = ‖A‖∞` specialization; the finite sum bridges collapse already-embedded residual matrices without support hypotheses, including coefficient-majorant and uniform-coefficient variants, while the finite supported-sum bridges additionally preserve same-ambient support, including mixed-offset families, under printed coefficient budgets and then feed the result into the solve-side interface, with coefficient-majorant variants replacing `Σc_t` by a supplied printed constant `C` and uniform-coefficient variants exposing the common `k*c*u‖A‖∞` budget |
| Thm 11.7 embedded path solve-side aggregation | `higham11_7_TridiagonalBranchPathSupportedWitnesses`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_embedded_sum`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_embedded_sum_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_embedded_sum_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_embedded_sum_of_coeff_sum_le` | Ch11 | **new this session**; extracts the finite path-local residual witnesses, accepts an explicit same-ambient embedding with support/budget preservation plus the final summed solve equation, and feeds that data into the supported solve-delta source interface. The local-assumption and terminal-tail wrappers compose the branch/path adapters before extraction. This does not close Theorem 11.7 yet; the concrete full pivot path still has to provide the embedding data and summed solve equation. |
| Thm 11.7 local-to-ambient path lift | `higham11_7_tridiagonalLocalBlockIndex`, `higham11_7_tridiagonalLocalBlockIndex_val`, `higham11_7_tridiagonalLiftLocalBlockPerturbation`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_embedded`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_bound`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_leadingBlockSupport`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_bound_leadingBlockSupport`, `higham11_7_tridiagonalBranchPathSupportedWitnesses_lift_to_ambient`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_of_coeff_sum_le` | Ch11 | **new this session**; gives the concrete same-ambient lift used by the embedded path bridge: a local branch perturbation is placed at a supplied row/column start offset, zero-filled elsewhere, retains its componentwise bound, shifts zero-prefix support by the start offset, and agrees on embedded local entries. The lifted-sum source wrapper now uses this explicit lift directly, leaving only the scalar budget comparisons and final lifted solve equation for the concrete mixed pivot path. |
| Thm 11.7 local-to-global path budget comparisons | `higham11_7_tridiagonal_local_budget_le_global_of_coeff_roundoff_norm`, `higham11_7_tridiagonalBranchPath_local_budgets_le_global_of_coeff_roundoff_norm` | Ch11 | **new this session**; converts pointwise coefficient, roundoff, and local matrix norm comparisons into the exact budget hypothesis required by the lifted path solve aggregation theorem, i.e. `(c_bound+c_rec)u_loc‖A_loc‖∞ ≤ c_t u ‖A‖∞` for every branch. |
| Thm 11.7 lifted zero-offset path endpoints | `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le` | Ch11 | **new this session**; specializes the lifted path solve aggregation to common support offset `0`, removing the routine offset-lowering proof, and exposes local-assumption and terminal-tail entry points that match the concrete mixed-pivot path construction. The scheduled variants choose an existing zero-based start-offset schedule internally, leaving the lifted solve equation as the path-specific handoff. |
| Thm 11.7 lifted zero-offset scalar-budget endpoints | `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm` | Ch11 | **new this session**; composes the zero-offset lifted source endpoints with the path budget-comparison lemma, so a concrete pivot path can discharge budgets by supplying nonnegativity, coefficient domination, roundoff domination, and local-to-global matrix norm domination. The scheduled variants use the proved start-offset existence theorem, so callers provide the lifted solve equation only for scheduled starts. |
| Thm 11.7 mixed-path start-offset schedule | `higham11_7_tridiagonalBranchSupportOffset_pos`, `higham11_7_tridiagonalBranchSupportOffset_le_two`, `higham11_7_tridiagonalPathPivotSpan`, `higham11_7_tridiagonalPathPivotSpan_zero`, `higham11_7_tridiagonalPathPivotSpan_cons`, `higham11_7_tridiagonalPathPivotSpan_pos`, `higham11_7_tridiagonalPathPivotSpan_ge_length`, `higham11_7_tridiagonalPathPivotSpan_le_two_mul`, `higham11_7_TridiagonalPathStartOffsetsFrom`, `higham11_7_TridiagonalPathStartOffsets`, `higham11_7_tridiagonalPathStartOffsetsFrom_head`, `higham11_7_tridiagonalPathStartOffsetsFrom_succ`, `higham11_7_tridiagonalPathStartOffsetsFrom_succ_lt`, `higham11_7_tridiagonalPathStartOffsetsFrom_cons`, `higham11_7_tridiagonalPathStartOffsetsFrom_tail`, `higham11_7_tridiagonalPathStartOffsetsFrom_iff_head_tail`, `higham11_7_tridiagonalPathStartOffsetsFrom_exists`, `higham11_7_tridiagonalPathStartOffsetsFrom_base_le`, `higham11_7_tridiagonalPathStartOffsetsFrom_lt_base_add_pivotSpan`, `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_base_add_pivotSpan`, `higham11_7_tridiagonalPathStartOffsetsFrom_last_branch_end_eq`, `higham11_7_tridiagonalPathStartOffsets_head`, `higham11_7_tridiagonalPathStartOffsets_succ`, `higham11_7_tridiagonalPathStartOffsets_succ_lt`, `higham11_7_tridiagonalPathStartOffsets_tail`, `higham11_7_tridiagonalPathStartOffsets_iff_head_tail`, `higham11_7_tridiagonalPathStartOffsets_exists`, `higham11_7_tridiagonalPathStartOffsets_lt_pivotSpan`, `higham11_7_tridiagonalPathStartOffsets_branch_end_le_pivotSpan`, `higham11_7_tridiagonalPathStartOffsets_last_branch_end_eq` | Ch11 | **new this session**; defines the concrete offset recurrence for a mixed `1×1`/`2×2` tridiagonal pivot path, with branch span bounds, zero/cons/positive/lower/upper pivot-span lemmas, a base-offset variant, zero-based specialization, existence theorems, head/successor/tail projections, strict successor growth from positive branch spans, start-offset total-span bounds, branch-end containment bounds, last-branch endpoint equalities, cons constructors, and head-tail iff lemmas that make nonempty schedules composable by induction. |
| Thm 11.7 mixed-path schedule ordering | `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_of_lt`, `higham11_7_tridiagonalPathStartOffsetsFrom_lt_of_lt`, `higham11_7_tridiagonalPathStartOffsets_branch_end_le_of_lt`, `higham11_7_tridiagonalPathStartOffsets_lt_of_lt` | Ch11 | **new this session**; proves any earlier scheduled branch consumes its pivot block before any later branch starts, and that scheduled starts are strictly ordered by path index. |
| Thm 11.7 mixed-path schedule uniqueness | `higham11_7_tridiagonalPathStartOffsetsFrom_unique`, `higham11_7_tridiagonalPathStartOffsetsFrom_exists_unique`, `higham11_7_tridiagonalPathStartOffsets_unique`, `higham11_7_tridiagonalPathStartOffsets_exists_unique` | Ch11 | **new this session**; proves the base-offset and zero-based mixed-path start schedules are unique, and packages existence plus uniqueness for canonical schedule handoffs. |
| §11.1.1 1×1 multiplier bound `|c/e| ≤ 1/α` | `oneByOne_multiplier_bound`, `higham11_1_oneByOne_multiplier_bound` | " | **new this session**; derived from pivot test `α·ω ≤ |e|`; the honest content behind the `bunch_parlett_L_bound`/`bunch_kaufman` `‖L‖`-interfaces |
| §11.1.1 / §11.1.2 1×1 Schur step growth `|b−c₁c₂/e| ≤ (1+1/α)μ₀` | `oneByOne_schur_growth`, `higham11_1_oneByOne_schur_growth` | " | **new this session**; printed bound `|ã_ij| ≤ μ₀+μ₀²/μ₁ ≤ (1+1/α)μ₀`; mechanism behind ρₙ ≤ (1+α⁻¹)^{n−1} |
| §11.1.1 2×2 pivot det bound `det E ≤ (α²−1)μ₀²` | `twoByTwo_completePivot_det_bound`, `higham11_4_twoByTwo_det_bound` | " | **new this session**; printed `det(E) ≤ μ₁²−μ₀² ≤ (α²−1)μ₀²` |
| §11.1.1 2×2 pivot nonsingularity `|det E| ≥ (1−α²)μ₀²` | `twoByTwo_completePivot_absdet_lower`, `higham11_4_twoByTwo_absdet_lower` | " | **new this session**; α∈[0,1); printed `|det E| ≥ (1−α²)μ₀²` |
| §11.1.1 2×2 Schur step growth `|ã| ≤ (1+2/(1−α))μ₀` (eq 11.4) | `twoByTwo_schur_growth`, `higham11_4_twoByTwo_schur_growth` (+ helper `abs_triple_mul_le`) | " | **new this session**; inverse-block entries `≤ αK,K`, `K = 1/((1−α²)μ₀)`; with the 1×1 bound this gives both single-step growth bounds of §11.1.1 |
| §11.1.1 α-derivation: growth balance `(1+1/α)² = 1+2/(1−α)` ⟺ `4α²−α−1=0`; `0<α<1` | `growth_balance_of_root`, `bunch_parlett_growth_balance`, `bunch_parlett_alpha_pos`, `bunch_parlett_alpha_lt_one`, `higham11_1_growth_balance` | " | **new this session**; the printed derivation fixing `α = (1+√17)/8`; ties the two single-step growth bounds together |
| §11.1.1 growth-factor recursion `r n ≤ (1+1/α)ⁿ·ρ₀` from per-stage ratio `r(k+1) ≤ (1+1/α)·r k` | `geom_growth_iterate`, `higham11_1_growth_factor_recursion`, `higham11_1_growth_factor_recursion_prefix`, `higham11_1_growth_factor_bound_of_prefix_steps`, `higham11_1_bunch_parlett_growth_bound_of_prefix_steps` | " | **new this session**; derives the printed `ρₙ ≤ (1+α⁻¹)^{n−1}` from the single-step bounds (induction, not assumed); the finite-prefix variant accepts stage bounds only for `k < m`, matching a concrete pivot path's active Schur-complement stages, and the printed-alpha wrappers package the normalized final-stage route directly into the book's growth-factor bound |
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
| §4.2 all-1×1 perturbation norm aggregation | `higham11_3_infNorm_le_of_componentwise_bound_nonneg`, `higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne_with_norm_bounds`, `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne_with_norm_bounds` | Ch11 | **new this session**; any nonnegative entrywise all-1×1 envelope now induces the corresponding `∞`-norm perturbation bound, and both raw-Schur and stored-symmetric source-facing all-1×1 packages carry those norm bounds for `ΔA₁` and `ΔA₂`. This remains an all-1×1-path dependency and does **not** close the mixed-pivot Theorem 11.3 row. |
| §11.1 exact block-LDLᵀ step, eq (11.3) `s=1`: `∑ L·D·Lᵀ = A` | `oneByOne_step_factorization`, `higham11_3_oneByOne_step_factorization` | " | **new this session**; exact 1×1-pivot factorization identity (unit-lower-tri `L`, block-diag `D` with Schur complement) — the **exact base of Theorem 11.3's diagonal-pivoting recursion** (fl version adds `fl_oneByOne_schur_step_error`) |
| §11.1 exact block-LDLᵀ **inductive step**, eq (11.1)/(11.3) | `blockLDLT_assemble_step`, `higham11_3_blockLDLT_assemble_step` | " | **new this session**; trailing block factorized recursively (`L_S·D_S·L_Sᵀ = S`, IH) + 1×1 multipliers ⇒ assembled `∑ L·D·Lᵀ = A`; iterating gives the exact `PAPᵀ = LDLᵀ` recursion |
| §11.1 exact **full recursion**, eq (11.1)/(11.2): `∃ L D, ∑ L·D·Lᵀ = A` | `exact_blockLDLT_all_oneByOne`, `higham11_1_exact_blockLDLT_all_oneByOne` (+ `schurCompl`, `schurCompl_symm`, `AllOnePivots`) | " | **new this session**; symmetric `A` with all Schur-complement pivots nonzero ⇒ exact `LDLᵀ` (no-2×2-pivot case), by induction on `n` via `blockLDLT_assemble_step` — the exact factorization scaffold for Theorem 11.3 |
| Thm 11.4 constant, Higham [608,1997] eq (4.13): `(3+α²)(3+α)/(1−α²)² ≤ 36` | `bunch_kaufman_bound_const_le_36`, `higham11_4_bound_const_le_36`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_absLDLTProduct_entries` | " | **new this session**; the `36` in `‖\|L̂\|\|D̂\|\|L̂ᵀ\|‖_M ≤ 36nρₙ‖A‖_M` (α=(1+√17)/8); the handoff bridges turn pointwise eq-(4.14) estimates with the exact Higham coefficient into both the source-facing `36nρₙ` max-entry norm bound and the scalar max-entry product certificate consumed by the stability/solve wrappers |
| Thm 11.4 constant, Higham [608,1997] (A.3): `(3+α²)/(1−α²) ≤ 6` (`\|E\|\|E⁻¹\|\|E\| ≤ 6\|E\|`) | `bunch_kaufman_pivot_norm_const_le_six`, `higham11_4_pivot_norm_const_le_six` | " | **new this session** |
| §11.1.2 1×1-pivot growth constant `1/α < 2` (Higham [608,1997]) | `bunch_kaufman_recip_alpha_lt_two`, `higham11_4_recip_alpha_lt_two` | " | **new this session**; `g_ij ≤ α⁻¹·max < 2·max` |
| Thm 11.4 max-entry product bridge, Higham [608,1997] eq (4.14) | `higham11_4_bunch_kaufman_stability_of_max_entry_product_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_max_entry_product_bound`, `higham11_4_bunch_kaufman_stability_of_higham_const_absLDLTProduct_entries`, `higham11_4_bunch_kaufman_stability_of_higham_const_product_entries`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_absLDLTProduct_entries`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_product_entries` | Ch11 | **new this session**; turns a scalar max-entry certificate for `\||L̂||D̂||L̂ᵀ|\|_M` into the existing pointwise stability surface, and transports a solve perturbation budget proportional to that product into the advertised `36nρₙ` normwise budget; the exact-coefficient direct wrappers combine the eq-(4.13) constant handoff with the stability and solve consumers, in both matrix-product and expanded double-sum entry notation. This does **not** prove eq (4.14); it makes eq (4.14) the exact next scalar target instead of a pointwise interface hypothesis. |
| Thm 11.4 row-sum stability consumers | `higham11_4_bunch_kaufman_stability_of_higham_const_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_stability_of_higham_const_uniform_entry_bounds`, `higham11_4_bunch_kaufman_stability_of_higham_const_row_sum_bounds` | Ch11 | **new this session**; exact-coefficient row-sum and uniform-entry product caps now feed the pointwise Bunch-Kaufman stability surface directly through the max-entry norm route, while deriving `0≤Dmax` from the nonempty absolute `D̂` entry cap. |
| Thm 11.4 row-sum solve consumers | `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_row_sum_bounds` | Ch11 | **new this session**; the same exact-coefficient row-sum and uniform-entry product caps feed the solve-side Bunch-Kaufman normwise perturbation wrapper, converting a solve residual proportional to `‖|L̂||D̂||L̂ᵀ|‖_M` into the advertised `36nρₙ` budget. |
| Thm 11.4 loose row-sum/uniform-entry consumers | `higham11_4_bunch_kaufman_stability_of_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_stability_of_uniform_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_uniform_entry_bounds` | Ch11 | **new this session**; when row-sum or uniform-entry caps are already compared directly to the printed `36nρₙ‖A‖_M` budget, the loose routes now feed both the stability surface and solve-side normwise perturbation wrapper without first exposing an intermediate max-entry proof. |
| Thm 11.4 finite max-entry product norm | `higham11_4_bunchKaufmanProductEntry`, `higham11_4_absLDLTProduct`, `higham11_4_bunchKaufmanProductEntry_eq_absLDLTProduct`, `higham11_4_bunchKaufmanProductEntry_nonneg`, `higham11_4_bunchKaufmanProductMax`, `higham11_4_bunchKaufmanProductEntry_le_productMax`, `higham11_4_absLDLTProduct_entry_le_productMax`, `higham11_4_bunchKaufmanProductMax_nonneg`, `higham11_4_bunchKaufmanProductMax_le_iff`, `higham11_4_bunchKaufmanProductMax_le_iff_absLDLTProduct`, `higham11_4_bunchKaufmanProductMax_eq_maxEntryNorm_absLDLTProduct`, `higham11_4_absLDLTProduct_entry_le_maxEntryNorm`, `higham11_4_maxEntryNorm_absLDLTProduct_le_iff`, `higham11_4_maxEntryNorm_absLDLTProduct_le_iff_product_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_product_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_absLDLTProduct_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_maxEntryNorm_absLDLTProduct`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_absLDLTProduct_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_product_entries`, `higham11_4_bunch_kaufman_stability_of_productMax_le`, `higham11_4_bunch_kaufman_stability_of_maxEntryNorm_absLDLTProduct_le`, `higham11_4_bunch_kaufman_solve_backward_error_of_productMax_le`, `higham11_4_bunch_kaufman_solve_backward_error_of_maxEntryNorm_absLDLTProduct_le` | Ch11 | **new this session**; defines the project matrix product `|L̂||D̂||L̂ᵀ|`, proves it is exactly the expanded double-sum entry form, defines the positive-dimension finite maximum `maxᵢⱼ (|L̂||D̂||L̂ᵀ|)ᵢⱼ`, identifies that finite maximum with the repository `maxEntryNorm` of `|L̂||D̂||L̂ᵀ|`, proves nonnegativity, the least-scalar property, and the direct equivalence between a `maxEntryNorm` bound and pointwise bounds in both expanded and matrix-product notation, packages pointwise/max-entry estimates into the scalar product-bound predicate including the exact Higham-coefficient handoff in both notations, and connects the source eq-(4.14) statement for this finite maximum directly to both the pointwise stability and solve-budget consumers. |
| Thm 11.4 row-sum/product majorant bridge | `higham11_4_bunchKaufmanProductEntry_le_row_sum_bounds`, `higham11_4_bunchKaufmanProductEntry_le_uniform_row_sum_bound`, `higham11_4_abs_row_sum_le_card_mul_of_uniform_entry_bound`, `higham11_4_bunchKaufmanProductEntry_le_uniform_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_row_sum_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_uniform_row_sum_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_uniform_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_row_sum_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_row_sum_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_row_sum_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_row_sum_bounds` | Ch11 | **new this session**; proves the algebraic step from absolute-entry bounds on `D̂` plus row-sum bounds on `|L̂|` to the source product entries of `|L̂||D̂||L̂ᵀ|`, and packages the uniform-row, uniform-entry, and per-row versions into the `maxEntryNorm` target and scalar product certificate consumed by the existing 11.4 stability/solve wrappers, including the exact-coefficient route before the proved `≤36` handoff. Uniform `|L̂|≤Lmax` facts now automatically supply the row sums as `n*Lmax`. This still leaves the pivot-path proof of the required `|L̂|` and `D̂` caps open. |
| Thm 11.4 product-entry nonnegativity adapters | `higham11_4_bunchKaufmanProductEntry_le_row_sum_bounds_entry_nonneg`, `higham11_4_bunchKaufmanProductEntry_le_uniform_row_sum_bound_entry_nonneg`, `higham11_4_bunchKaufmanProductEntry_le_uniform_entry_bounds_entry_nonneg` | Ch11 | **new this session**; lower-level row-sum, uniform-row, and uniform-entry product-entry adapters now derive `0≤Dmax` from the nonempty absolute `D̂` entry cap, matching the existing scalar and max-entry norm wrappers. |
| Thm 11.4 loose max-entry product cap nonnegativity wrappers | `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_row_sum_bound_entry_nonneg`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_entry_bounds_entry_nonneg` | Ch11 | **new this session**; the loose `maxEntryNorm` row-sum and uniform-entry routes now derive `0≤Dmax` from the nonempty uniform absolute `D̂` entry cap, matching the loose scalar product-certificate wrappers. |
| Thm 11.4 max-entry product cap nonnegativity wrappers | `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_row_sum_bound_entry_nonneg`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_entry_bounds_entry_nonneg`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_row_sum_bounds_entry_nonneg` | Ch11 | **new this session**; the exact-coefficient max-entry norm routes now derive `0≤Dmax` from the nonempty uniform absolute `D̂` entry cap, matching the scalar product-certificate wrappers and removing a separate positivity handoff for uniform-row, uniform-entry, and per-row row-sum paths. |
| Thm 11.4 first-stage/recursive product aggregation | `higham11_4_first_stage_recursive_product_bound`, `higham11_4_product_entries_of_first_stage_recursive_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_bounds`, `higham11_4_first_stage_recursive_product_bound_of_higham_const`, `higham11_4_product_entries_of_first_stage_recursive_higham_const_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_bounds` | Ch11 | **new this session**; formalizes the scalar handoff implicit in Higham [608, 1997], eqs. (4.11)--(4.14): one local first-stage product share plus a recursive Schur-complement product share bounded by `36(n-s)ρₙ‖A‖_M` fits inside the printed `36nρₙ‖A‖_M` budget, and the resulting entrywise split packages directly into the scalar max-entry product certificate. The exact-coefficient variants let callers supply Higham's `(3+α²)(3+α)/(1−α²)^2` bound first and use the proved eq-(4.13) `≤36` handoff only at the final source-facing step. This does not prove the concrete first-stage or recursive split hypotheses; it removes the remaining scalar aggregation once those pivot-path bounds are supplied. |
| Thm 11.4 first-stage/recursive max-entry norm bridge | `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_bounds` | Ch11 | **new this session**; the loose and exact-coefficient first-stage/trailing product splits now also package directly into the source-shaped `maxEntryNorm` target for `|L̂||D̂||L̂ᵀ|`, not just the scalar finite-product certificate. |
| Thm 11.4 first-stage/recursive stability/solve consumers | `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_bounds` | Ch11 | **new this session**; the loose and exact-coefficient first-stage/trailing product split now feeds both the pointwise Bunch-Kaufman stability surface and the solve-side normwise perturbation wrapper directly, so the remaining pivot-path proof can target the concrete local/trailing split hypotheses. |
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
| Thm 11.8 relative `T_hat` fallback scalar norm-budget reducers | `higham11_8_aasen_factor_solve_norm_budget_of_relative_T_hat_error`, `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_relative_T_hat_error` | Ch11 | **new this session**; a supplied relative middle-factor error `|T_hat-T|≤κBT|T_hat|` now directly instantiates the concrete factorization-side budget `κBT|T_hat|` and feeds the scalar norm-budget route, including the generated relative-`L_hat` outer-factor variant. This fallback uses the proved `‖T‖∞≤(1+κBT)‖T_hat‖∞` cap, so it is useful for non-exact-radius norm budgeting but does **not** close the sharper source route requiring `κT=1` or a direct `‖T‖∞≤‖T_hat‖∞`/entrywise `|T|≤|T_hat|` fact. |
| Thm 11.8 Aasen outer-factor `(n-1)` majorant | `higham11_8_sum_abs_le_card_pred_mul_of_one_zero`, `higham11_8_aasen_outer_factor_row_col_sum_majorants_of_entry_bound`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound`, `higham11_8_aasen_outer_factor_scaled_entry_cap`, `higham11_8_one_plus_mul_le_one_of_le_inv_one_plus`, `higham11_8_aasen_outer_factor_scaled_entry_cap_of_le_inv_one_plus`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_scaled_unit`, `higham11_8_nonneg_of_uniform_abs_entry_bound`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus_of_entry_bound`, `higham11_8_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`, `higham11_8_outer_factor_caps_of_aasen_entry_bound_inv_one_plus_of_entry_bound`, `higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus`, `higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus_of_entry_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap` | Ch11 | **new this session**; proves that Aasen's exact outer factor structure (strict upper-zero entries plus first-column zeros below the first row) turns a uniform exact-factor entry bound into row and column sum majorants with `(n-1)` entries, then feeds those majorants to the relative outer-factor norm caps required by the exact-radius route. The normalized scalar helper reduces the row/column scale comparison to `(1+γ)κ≤1`, and the inverse-scale wrapper discharges that normalized cap from the source-style hypothesis `κ≤1/(1+γ)`; the unscaled and base-square wrappers derive the exact outer-factor caps and `(n-1)^2` product caps consumed by exact-radius routes. The source-prefix endpoints consume the sharper cap directly in both the entrywise `|T|≤|T̂|` middle route and the direct `‖T‖∞≤‖T̂‖∞` route, either with a supplied middle product estimate or with the checkerboard LU specialization, replacing the crude `n`-entry fallback once the concrete source entry bound and scalar comparison are supplied; both the checkerboard and direct-middle endpoints now accept the source-style inverse-scale entry estimate directly, and the matching normalized endpoint wrappers derive their own `0≤κ` side condition from the entry bound. The lower-level inverse-scale and normalized cap/base-square helpers can also derive `0≤κ` from the same nonempty uniform absolute entry bound. |
| Thm 11.8 scalar coefficient product-cap helpers | `higham9_14_f_mono_nonneg`, `higham11_gamma_add_le`, `higham11_8_two_gamma_plus_sq_mul_le_of_le`, `higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_le`, `higham11_8_two_gamma_plus_sq_mul_le_of_majorants`, `higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants`, `higham11_8_higham9_14_f_gamma_le_gamma_4n`, `higham11_8_three_higham9_14_f_gamma_le_gamma_12n`, `higham11_8_two_gamma_plus_sq_le_gamma_2n`, `higham11_8_one_plus_two_gamma_plus_sq_mul_gamma_le_gamma_3n`, `higham11_8_one_plus_two_gamma_plus_sq_mul_higham9_14_f_gamma_le_gamma_6n`, `higham11_8_one_plus_two_gamma_plus_sq_mul_three_higham9_14_f_gamma_le_gamma_14n`, `higham11_8_gamma_2n_plus_3n_plus_2n_plus_6n_le_gamma_15n25`, `higham11_8_triple_product_square_bound_of_middle_le_one`, `higham11_8_aasen_product_square_bounds_of_base_le_one`, `higham11_8_aasen_factor_solve_coeff_le_of_product_square_bounds`, `higham11_8_aasen_relative_coeff_le_of_gamma_product_square_bounds`, `higham11_8_aasen_relative_coeff_le_of_gamma_base_square_bounds`, `higham11_8_aasen_relative_coeff_le_of_gamma_base_square_exact_radius`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_bounds`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_concrete_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_concrete_product_majorants` | Ch9/Ch11 | **new this session**; factors the four gamma-share coefficient comparisons through reusable product caps, larger gamma/product majorants, exact product-square caps for the printed `(n−1)^2` prefactor, and monotonicity/absorption of Chapter 9's tridiagonal LU polynomial `f(u)=4u+3u²+u³`, including direct absorptions for `2γ_n+γ_n²`, `(1+2γ_n+γ_n²)γ_n`, `f(γ_n)`, `(1+2γ_n+γ_n²)f(γ_n)`, `3f(γ_n)`, and `(1+2γ_n+γ_n²)3f(γ_n)`; the exact-product discharge now allocates the concrete `T_hat` route to `γ_{2n}+γ_{3n}+γ_{2n}+γ_{6n}≤γ_{15n+25}` from square bounds and `κBT≤γ_n`, the reduced base-square interface derives the four exact-product caps from the two base square caps plus `κT≤1` and `κmidLU≤1`, and the exact-radius specialization uses the printed `γ_{15n+25}` directly, so later work can prove product-size bounds and scaled gamma-share bounds separately before invoking the existing four-share splitter, discharge the same product-majorant route with one aggregate printed-coefficient inequality, or instantiate the product caps with the exact products from the relative Aasen norm budget in either aggregate or reduced aggregate form; the product-majorant reducers also transport the concrete middle term `f(γ_solve)κmidLU` through a larger `γ_mid_cap` |
| Thm 11.8 printed gamma-validity guard | `higham11_8_gammaValid_15n25_of_unit_roundoff_bound`, `higham11_8_gammaValid_15n25_of_u_le_cap`, `higham11_8_gammaValid_n_two_prefix_of_u_le_cap` | Ch11 | **new this session**; turns the source smallness condition `(15n+25)u<1`, or a displayed cap `u≤Ucap` with `(15n+25)Ucap<1`, into the repository `gammaValid fp (15*n+25)` hypothesis and the local `gammaValid n`, `gammaValid 2`, and prefix-dot validity side conditions used by the Aasen wrappers. This discharges only the gamma-validity guard plumbing; the concrete Aasen product-size and `T_hat` comparison facts remain open. |
| Thm 11.8 Aasen factorization product residual budget | `higham11_8_aasenFactorizationProductBudget`, `higham11_8_aasen_factorization_product_abs_bound_of_entrywise_factor_bounds`, `higham11_8_aasen_factorization_product_abs_bound_gamma`, `higham11_8_aasen_factorization_product_abs_bound_of_source_prefix_updates` | Ch11 | **new this session**; from exact `A=LTLᵀ` and entrywise factor budgets `|L̂−L|≤BL`, `|T̂−T|≤BT`, proves the product residual `|L̂T̂L̂ᵀ−A|` is bounded by an explicit seven-term double-sum budget; specializes relative `|L̂−L|≤γ|L|` and middle `|T̂−T|≤BT` budgets to the closed `higham11_15_aasenChainDeltaABound`; now also instantiates the relative `L_hat` factor hypothesis from the source-prefix rounded recurrence bridge, so the factorization-product residual can be consumed from the modeled next-column updates plus the remaining concrete `T_hat` budget |
| §11.2 Aasen solve chain eq (11.15), rounded source backward-error wrapper | `higham11_15_aasenMiddleSolveBudget`, `higham11_15_fl_aasen_solve_chain_source_backward_error_of_delta_bound`, `higham11_15_fl_aasen_solve_chain_source_backward_error` | Ch11 | **new this session**; instantiates the rounded component package and algebraic collapse, first under an explicit componentwise budget and then with the closed `higham11_15_aasenChainDeltaABound` generated from the outer `γ_n` solve bounds and the middle `f(γ_n)|L_T||U_T|` budget |
| Thm 11.8 factorization + solve-chain source wrapper | `higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals`, `higham11_8_fl_aasen_factor_solve_source_backward_error` | Ch11 | **new this session**; combines a factorization residual `A_fact−A` with a solve-chain residual `ΔS` into one source perturbation `ΔA`, then instantiates this for rounded Aasen solves with computed factors `L̂,T̂`, yielding `(A+ΔA)ŵ=Pᵀb` with componentwise budget `B_factor+B_solve` |
| §11.2 Aasen solve chain eq (11.15), exact unpermuted algebra | `higham11_15_aasenSolveChain_identity_solve_of_product` | Ch11 | **new this session**; if `A = L T Lᵀ` and the exact chain `Lz=b`, `Ty=z`, `Lᵀw=y`, `x=w` holds (identity permutation), then `A x = b`; this is the algebraic base for later rounded solve-chain perturbation |
| Thm 11.8 norm bridge: componentwise perturbation ⇒ `∞`-norm bound | `higham11_8_infNorm_le_card_mul_of_uniform_componentwise_bound`, `higham11_8_aasenNormwiseBackwardBound_of_uniform_componentwise_bound`, `higham11_8_infNorm_le_mul_of_componentwise_T_bound`, `higham11_8_infNorm_T_hat_sub_T_le_mul_of_relative_error`, `higham11_8_infNorm_scaled_abs_T_hat_le`, `higham11_8_abs_T_le_one_plus_gamma_T_hat_of_relative_error`, `higham11_8_infNorm_T_le_one_plus_gamma_T_hat_of_relative_error`, `higham11_8_infNorm_factor_le_of_relative_entry_bound`, `higham11_8_infNorm_factorTranspose_le_of_relative_entry_bound`, `higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound`, `higham11_8_componentwise_T_bound_add_of_parts`, `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound`, `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound_coeff_le` | Ch11 | **new this session**; if `|ΔAᵢⱼ| ≤ β`, then `‖ΔA‖∞ ≤ nβ`; if `|ΔAᵢⱼ| ≤ η|T̂ᵢⱼ|`, then `‖ΔA‖∞ ≤ η‖T̂‖∞`; a supplied source-style `|T̂−T|≤γ|T̂|` now directly yields both `‖T̂−T‖∞≤γ‖T̂‖∞` and the concrete envelope norm `‖γ|T̂|‖∞≤γ‖T̂‖∞`, while the exact factor itself gets only the weaker entrywise/norm consequences `|Tᵢⱼ|≤(1+γ)|T̂ᵢⱼ|` and `‖T‖∞≤(1+γ)‖T̂‖∞`; relative factor perturbations `|L_hat-L|≤γ|L|` give `(1+γ)` bounds for `L_hat` and its transpose; all bridge into the printed `(n−1)^2γ_{15n+25}‖T̂‖∞` target once the scalar budget is available; the closed solve-chain budget `higham11_15_aasenChainDeltaABound` now feeds the same printed normwise predicate under an entrywise comparison to `η|T̂|`; the splitter combines separate factorization and solve-chain entrywise comparisons `η_factor|T̂|` and `η_solve|T̂|` when `η_factor+η_solve≤η`; the coefficient adapter accepts `η ≤ (n−1)^2γ_{15n+25}` and multiplies by `‖T̂‖∞` internally |
| Thm 11.8 zero-relative `T_hat` cap | `higham11_8_abs_T_le_T_hat_of_zero_relative_error`, `higham11_8_infNorm_T_le_T_hat_of_zero_relative_error` | Ch11 | **new this session**; specializes the relative `|T̂−T|≤γ|T̂|` diagnostics at `γ=0`, recovering the coefficient-one entrywise and `∞`-norm exact-`T` caps required by exact middle-matrix routes when the computed and exact tridiagonal factors coincide componentwise. |
| Thm 11.8 zero-relative `T_hat` source-constant endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_constants_of_zero_relative_T_hat` | Ch11 | **new this session**; specializes the supplied exact-radius source-constant route so a zero relative `T_hat - T` comparison supplies both the `γ_n` factorization budget and the direct `‖T‖∞≤‖T_hat‖∞` cap, removing two separate middle-factor handoffs from that endpoint. |
| Thm 11.8 zero-relative `T_hat` supplied checkerboard endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle` | Ch11 | **new this session**; specializes the supplied checkerboard-middle route with relative exact outer-factor caps so the zero relative `T_hat - T` comparison supplies both the concrete `γ_n` middle-factor budget and the direct exact-`T` norm cap. |
| Thm 11.8 zero-relative `T_hat` source-prefix checkerboard endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle` | Ch11 | **new this session**; specializes the source-prefix checkerboard-middle route with relative exact outer-factor caps so the zero relative `T_hat - T` comparison supplies the middle-factor budget and exact-`T` norm cap while the relative `L_hat` hypothesis is generated from the rounded Aasen recurrence model. |
| Thm 11.8 zero-relative `T_hat` source-prefix direct norm-cap endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_zero_relative_T_hat` | Ch11 | **new this session**; generic direct-middle source-prefix wrapper turning zero relative `T_hat - T` into the `γ_n` factorization-side middle budget and exact `T`-norm cap under supplied outer factor norm caps and a supplied `|L_T||U_T|≤|T_hat|` product estimate. |
| Thm 11.8 zero-relative `T_hat` source-prefix row-sum endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_zero_relative_T_hat_checkerboard_middle` | Ch11 | **new this session**; combines scaled exact outer-factor row/column sum caps with the zero-relative `T_hat - T` comparison, feeding the source-prefix checkerboard-middle exact-radius route without separate `T` norm or `γ_n` middle-budget hypotheses. |
| Thm 11.8 source-prefix direct row-sum endpoints | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_T_norm_cap` | Ch11 | **new this session**; direct-middle counterparts of the row-sum exact-radius routes, deriving exact and relative outer-factor norm caps from scaled row/column sums while keeping a supplied `|L_T||U_T|≤|T_hat|` middle-product estimate. |
| Thm 11.8 source-prefix direct entrywise-majorant endpoints | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap` | Ch11 | **new this session**; direct-middle counterparts of the generic entrywise-majorant exact-radius routes, deriving exact and relative outer-factor norm caps from a uniform exact-factor entry bound while keeping a supplied `|L_T||U_T|≤|T_hat|` middle-product estimate. |
| Thm 11.8 direct entrywise-majorant endpoint nonnegativity wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap_entry_bound_nonneg` | Ch11 | **new this session**; direct-middle nonnegativity-discharge variants for the generic entrywise-majorant routes, deriving `0≤κ` from the nonempty uniform absolute entry bound for both componentwise-`T` and direct-`T`-norm endpoints. |
| Thm 11.8 zero-relative `T_hat` source-prefix entrywise-majorant endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat_checkerboard_middle` | Ch11 | **new this session**; combines a uniform exact outer-factor entrywise majorant with the zero-relative `T_hat - T` comparison, feeding the source-prefix checkerboard-middle exact-radius route through the entrywise-majorant outer-factor cap adapter. |
| Thm 11.8 zero-relative `T_hat` source-prefix direct row-sum/entrywise endpoints | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_zero_relative_T_hat`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat` | Ch11 | **new this session**; direct-middle variants of the row-sum and entrywise-majorant exact-radius routes, keeping a supplied `|L_T||U_T|≤|T_hat|` product estimate while the zero-relative comparison supplies the `γ_n` factor budget and exact `T` norm cap. |
| Thm 11.8 generic entrywise-majorant endpoint nonnegativity wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat_entry_bound_nonneg` | Ch11 | **new this session**; lifts the existing nonempty absolute-entry-bound nonnegativity helper to the generic `n`-entry majorant endpoints, so source callers no longer provide `0≤κ` separately for checkerboard componentwise-`T`, checkerboard direct-`T`-norm, checkerboard zero-relative, or direct-middle zero-relative routes. |
| Thm 11.8 zero-relative `T_hat` source-prefix Aasen-entry endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_zero_relative_T_hat_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg` | Ch11 | **new this session**; specializes the sharper Aasen-structure outer-factor entry-bound route, using strict-upper and first-column zero structure plus a uniform entry cap for `L`, while the zero-relative `T_hat - T` comparison supplies the exact-radius middle-factor handoffs; the nonnegativity companion derives `0≤κLentry` from the same uniform absolute entry bound. |
| Thm 11.8 zero-relative `T_hat` normalized/source-style Aasen endpoints | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg` | Ch11 | **new this session**; zero-relative checkerboard wrappers for the normalized `(1+γ_n)κ≤1` and source-style `κ≤1/(1+γ_n)` Aasen entry-cap routes, including variants that derive `0≤κ` from the nonempty uniform absolute entry bound. |
| Thm 11.8 zero-relative `T_hat` direct-middle normalized/source-style Aasen endpoints | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_entry_bound_nonneg` | Ch11 | **new this session**; direct-middle zero-relative wrappers for the same normalized and source-style Aasen entry-cap routes, keeping a supplied `|L_T||U_T|≤|T_hat|` middle-product estimate while deriving the exact-`T` norm handoff and optional `0≤κ` side condition. |
| Thm 11.8 Aasen outer-factor row/column and entrywise majorant bridge | `higham11_8_relative_infNorm_cap_of_row_sum_majorant`, `higham11_8_relative_outer_factor_caps_of_row_col_sum_majorants`, `higham11_8_relative_outer_factor_caps_of_entrywise_majorant`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap_checkerboard_middle` | Ch11 | **new this session**; unscaled row and column sum majorants for the exact Aasen outer factor `L`, together with scalar comparisons `(1+γ)κ≤cap`, now feed the relative `∞`-norm caps for both `L` and `Lᵀ` required by the exact-radius source-prefix wrappers. A uniform entrywise majorant now automatically supplies both row and column majorants via row/column sums, and the source-prefix checkerboard-middle endpoints consume that entrywise majorant directly for either entrywise `|T|≤|T̂|` or supplied `‖T‖∞≤‖T̂‖∞`. This reduces the remaining source/product-size work to proving the actual row/column or entrywise majorants and scalar scale comparisons for the concrete Aasen factor. |
| Thm 11.8 solve-chain source + normwise wrapper | `higham11_8_fl_aasen_solve_chain_source_normwise_backward_error` | Ch11 | **new this session**; packages the rounded Aasen solve-chain source equation `(A+ΔA)ŵ=Pᵀb` with the printed normwise predicate once the closed chain budget is compared entrywise to `η|T̂|` and the scalar `(n−1)^2γ_{15n+25}` budget is supplied |
| Thm 11.8 printed split-entry normwise endpoints | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma_validity`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma_validity` | Ch11 | **new this session**; instantiates the split-entry `η_factor+η_solve` routes with the final printed coefficient `(n−1)^2γ_{15n+25}`, deriving the intermediate nonnegativity from `0≤γ_{15n+25}` and removing the redundant `η`/`η≤...` handoff for supplied-relative and source-prefix callers. The printed-gamma variants specialize `γ_{15n+25}` to `gamma fp (15*n+25)` and derive nonnegativity from `gammaValid fp (15*n+25)`; the validity variants also derive the local `gammaValid n`, `gammaValid 2`, and source-prefix dot-product validity side conditions from the same printed validity guard. |
| Thm 11.8 primitive relative gamma-share source wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds_gamma_parts` | Ch11 | **new this session**; lifts the four-share `(n−1)^2γ_{15n+25}` coefficient interface from the scalar relative-factor reducer to the rounded source wrappers, both when the relative `L_hat` perturbation is supplied and when it is generated from the source-prefix rounded recurrence model |
| Thm 11.8 factorization+solve source + normwise wrapper | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets` | Ch11 | **new this session**; packages the rounded Aasen factorization and solve-chain source equation `(A+ΔA)ŵ=Pᵀb` together with the printed normwise predicate. The original wrapper uses an explicit entrywise comparison from the summed factorization+solve budgets to `η|T̂|`; the scalar norm wrapper accepts one normwise comparison from the summed closed budgets to `(n−1)^2γ_{15n+25}‖T̂‖∞`, and the factor-norm wrappers discharge that comparison from primitive `∞`-norm factor bounds plus one coefficient inequality, including variants where the computed `L̂`/`L̂ᵀ` norm bounds are derived from the relative entrywise factor perturbation, where the factorization-side `BT_factor` norm is derived from a componentwise `BT_factor≤κ|T̂|` bound, and source-prefix variants that generate the relative `L̂` factor hypothesis from the modeled rounded recurrence updates; the middle-factor-product and abs-LU wrappers replace the hand-supplied middle-budget norm with either a relative `‖L_T‖∞‖U_T‖∞` bound, the sharper `‖|L_T||U_T|‖∞` bound, or its componentwise `|T̂|` source; the combined wrappers consume componentwise bounds for both `BT_factor` and `|L_T||U_T|`; the column- and row-dominant wrappers use the concrete Chapter 9 `3f(γ_n)` middle coefficient, either as four scalar pieces or as one direct scalar sum, including source-prefix variants that also derive the computed `L̂`/`L̂ᵀ` norm bounds from the generated relative factor hypothesis and can derive the `BT_factor` norm from a componentwise `T_hat` comparison; the split-entry wrappers accept separate factorization and solve-chain entrywise comparisons and combine their coefficients |
| Thm 11.8 supplied-relative column/row middle wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff_componentwise_BT` | Ch11 | **new this session**; specialize the non-source factorization+solve source wrapper for the case where a relative `L_hat` perturbation hypothesis is already available, derive the computed `L_hat`/`L_hatᵀ` norms from it, use the concrete Chapter 9 column- or row-dominant `3f(γ_n)` middle coefficient, and optionally derive the `BT_factor` norm from a componentwise `T_hat` comparison |
| Thm 11.8 supplied/source-prefix relative middle/abs-LU wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_BT`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_T_factor`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_T_factor`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_norm_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_componentwise_BT_absLU_componentwise_T_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_coeff_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_coeff_parts` | Ch11 | **new this session**; specialize the relative `L_hat` route for non-dominance middle-budget hypotheses: a relative `‖L_T‖∞‖U_T‖∞` product bound, including variants that derive the `BT_factor` norm from a componentwise `T_hat` comparison or instantiate `BT_factor` directly as `κBT|T_hat|`, a sharper `‖|L_T||U_T|‖∞` bound with split scalar coefficients, componentwise middle variants against `T_hat`, and combined componentwise variants deriving both the `BT_factor` and abs-LU middle norms from `T_hat` or instantiating the concrete `T_hat` factor budget directly; the source-prefix variants combine these with the generated relative `L_hat` hypothesis from rounded recurrence updates |
| Thm 11.8 concrete `T_hat` gamma-share/product-majorant wrappers | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants_coeff`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_square_products`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_square_products`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_products`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_products`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts`, `higham11_15_absLU_componentwise_T_bound_of_checkerboard_LUFactSpec`, `higham11_8_infNorm_cap_of_relative_infNorm_cap`, `higham11_8_relative_infNorm_cap_of_row_sum_caps`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_T_norm_cap_checkerboard_middle` | Ch11 | **new this session**; specializes the most concrete supplied/source-prefix relative abs-LU path where `|T_hat-T|≤κBT|T_hat|` and `|L_T||U_T|≤κmidLU|T_hat|`, while accepting either four shares of the printed `(n−1)^2γ_{15n+25}` coefficient, one aggregate product-cap/gamma-majorant coefficient inequality, the same gamma-share/aggregate inequalities after the product caps have been instantiated by exact products, or the new supplied/source-prefix exact-product wrappers that discharge the aggregate coefficient from square product bounds and `κBT≤γ_n`; the reduced supplied/source-prefix wrappers further replace the four exact-product square caps by two base square caps plus `κT≤1` and `κmidLU≤1`, with exact-radius variants using the printed `γ_{15n+25}` directly; the product-majorant variants let callers supply coarser product caps and larger gamma radii, with the middle `f(γ)` term transported by Ch9 monotonicity; the checkerboard-middle endpoints derive the coefficient-one `|L_T||U_T|≤|T_hat|` hypothesis from Chapter 9's checkerboard total-nonnegative LU product identity, the relative-norm-caps endpoints derive the unscaled exact outer-factor caps from the displayed relative `(1+γ_n)` caps, and the row-sum-caps endpoints derive those relative caps from scaled row/column sum budgets, with either entrywise `|T|≤|T_hat|` or a direct `‖T‖∞≤‖T_hat‖∞` cap for the exact middle matrix |
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
| Theorem 11.3 | block LDLᵀ backward error: `P(A+ΔA₁)Pᵀ = L̂D̂L̂ᵀ`, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` (eq 11.5) | `higham11_3_block_ldlt_backward_error_interface` (assumes the whole conclusion) | **substantially advanced (all-1×1 case)**: proved the exact recursion (`exact_blockLDLT_all_oneByOne`), the component stage bounds, packaged all-index one-stage envelope with nonnegativity, raw-Schur recursive all-1×1 envelope, stored-symmetric rounded Schur bridge, storage-defect one-stage bridge, recursive stored-symmetric all-1×1 envelope (`fl_blockLDLT_stored_all_oneByOne_bound`, `higham11_3_fl_blockLDLT_stored_all_oneByOne_bound`), source-facing all-1×1 perturbation packages (`higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne`, `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne`), and norm-bound variants for both all-1×1 packages (`..._with_norm_bounds`). NOTE: (11.5) for 2×2 pivots = **Problem 11.5 (benchmark-reserved)** → stays a hypothesis. | extend the induction to mixed 1×1/2×2 pivots while keeping the 2×2 solve bound as a hypothesis, then relate the accumulated envelope to the printed `p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` form |
| Theorem 11.4 | Bunch–Kaufman normwise stability `(A+ΔA)x̂=b`, `‖ΔA‖_M ≤ p(n)ρₙu‖A‖_M+O(u²)` via `‖|L̂||D̂||L̂ᵀ|‖_M ≤ 36nρₙ‖A‖_M` | `higham11_4_bunch_kaufman_stability` / `..._solve_backward_error_interface` (assume); scalar max-product bridges `higham11_4_bunch_kaufman_stability_of_max_entry_product_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_max_entry_product_bound`, and the finite-max routes `..._of_productMax_le` now reduce those consumers to the source-style eq-(4.14) scalar certificate; `higham11_4_absLDLTProduct`/`..._eq_absLDLTProduct` connect the expanded Lean entry to the project `matMul` notation for `|L̂||D̂||L̂ᵀ|`, `..._eq_maxEntryNorm_absLDLTProduct` identifies the specialized finite maximum with the existing max-entry norm, `..._maxEntryNorm_absLDLTProduct_le` bridges feed that notation directly to both stability and solve endpoints, the row-sum/product majorant bridges package uniform or per-row `|L̂|` row-sum caps plus a uniform `|D̂|` cap into that target, including the exact Higham coefficient before the `≤36` handoff, and the first-stage/recursive aggregation bridges package Higham [608] eq. (4.11)'s local-plus-recursive product split, with either loose `36` shares or the exact eq-(4.13) coefficient, into the same scalar certificate | proof now available (Higham [608,1997] §4.3, eqs 4.11–4.14, appendix A). The **constants** are proved (`bunch_kaufman_bound_const_le_36` = eq 4.13's `36`, `..._pivot_norm_const_le_six` = A.3, `..._recip_alpha_lt_two`), the finite max-entry product norm is defined, its matrix-product/max-entry-norm notation bridges, nonnegativity, least-bound property, pointwise-to-scalar packaging, direct pointwise-to-max-entry-norm packaging, row-sum/product majorant packaging, loose and exact-coefficient first-stage/recursive scalar aggregation, and consumer bridges are proved, and the all-stage, finite-prefix, printed-alpha, and normalized final-stage growth recursions are formalized. Remaining: prove the concrete pivot-path first-stage/trailing split, row-sum and `D̂` entry caps (or a sharper direct product-entry proof) from the paper's block bounds (4.11)–(4.12), then instantiate them into the exact-coefficient (4.14) estimate. | prove per-row or uniform `|D̂|` and `|L̂|` row-sum caps from the per-pivot `\|E\|\|E⁻¹\|\|E\|`/`CE⁻¹` bounds and the Schur-recursion `‖S‖_M ≤ ρₙ‖A‖_M`, then feed `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_row_sum_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_row_sum_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_bounds`, or `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_bounds` (or an equivalent direct entry proof) to obtain the source max-entry estimate |
| Theorem 11.7 | Bunch tridiagonal normwise stability, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ c·u·‖A‖` | `higham11_7_tridiagonal_backward_error_interface` (assumes); Algorithm 11.6 branch tests, the accepted `2×2` pivot determinant lower bound/nonsingularity, inverse-entry bounds, the atomic rounded scalar Schur update, a `Fin 1` trailing-block one-stage printed-budget handoff, the ambient `Fin 3` first-stage embedding, the dimension-generic `Fin (n+3)` local-recursion embedding, trailing-block support packaging, support-preserving perturbation addition, offset-generic zero-prefix base/add packaging including printed-coefficient variants, mixed-depth accumulation, and the offset-two bridge, first local+recursive residual accumulation with printed coefficient addition, the recursive trailing-subproblem perturbation lift, recursive scalar residual composition, zero-prefix support shifting under recursive lifts, leading-support versions of the subproblem and recursive-residual accumulators, the norm-bound version of the leading-support recursive-residual accumulator, the solve-side `ΔA₂` bridge into the source-facing interface with separate nonnegative and direct inf-norm budget forms, the entrywise `|Aᵢⱼ|≤‖A‖∞` bridge for local `Amax` hypotheses, componentwise-to-∞-norm aggregation, source-side norm-bound packaging, finite support-sum aggregation including mixed-offset printed variants, finite supported solve-delta aggregation into the source interface, the trailing-subproblem offset/injectivity bookkeeping for the `2×2` tridiagonal step, matching offset-one lift/support plus scalar and matrix-entry local-recursive norm-bound packages for the `1×1` tridiagonal step, the branch-indexed local assumptions/residual adapter, the terminal-tail branch adapter, finite mixed-pivot path-local adapter, embedded path solve-delta aggregation adapters, the concrete local-to-ambient lift package, generic local-to-global budget comparison lemmas, zero-offset lifted source endpoints, zero-offset scalar-budget source endpoints, and mixed-path start-offset schedule interface are now proved | tridiagonal block-LDLᵀ fl analysis | instantiate the finite path-local assumption interface along a concrete full mixed `1×1`/`2×2` tridiagonal block-LDLᵀ pivot path, using the terminal-tail adapter as its base case, then instantiate the concrete schedule against `higham11_7_TridiagonalPathStartOffsets`, prove concrete coefficient/roundoff/local-norm comparisons, and final lifted solve equation |

2026-07-09 update: `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries`
specializes the leading `2×2` local+recursive residual accumulator to ambient matrix
entries under `Amax=‖A‖∞`. A later 2026-07-09 update adds the matching leading
`1×1` local+recursive branch
`higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries`,
including the offset-one recursive lift and Algorithm 11.6 one-pivot scalar
correction bound. A follow-up 2026-07-09 increment factors that branch through
the reusable scalar theorem
`higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_with_norm_bound`
and the bound/support/embedded-entry lift package
`higham11_7_tridiagonalOneByOneLiftTrailingPerturbation_bound_leadingBlockSupport`.
The latest 2026-07-09 increment adds direct `σ=‖A‖∞` wrappers for both the
local `1×1` and `2×2` tridiagonal branches, so the later mixed recursion can
invoke the branch packages without separate pivot-scale or pivot-entry norm
handoffs.
A later 2026-07-09 increment adds the branch-indexed local assumptions/residual
adapter `higham11_7_tridiagonalBranchLocalResidual_of_localAssumptions`, giving
the future mixed-pivot path induction one common local target for either pivot
size while leaving the recursive tail certificate explicit.
The latest 2026-07-09 increment adds the terminal-tail zero residual and
`higham11_7_tridiagonalBranchLocalResidual_of_terminalTailAssumptions`, so the
future mixed-pivot path induction has a base-case package in the same common
branch-local result shape.
A follow-up 2026-07-09 increment adds
`higham11_7_tridiagonalBranchLocalAssumptions_of_terminalTailAssumptions` and
`higham11_7_tridiagonalBranchPathLocalAssumptions_of_terminalTailAssumptions`,
so terminal branches and terminal paths can also be consumed through the
ordinary local-assumption interface with `tail_fl = tail_exact`.
The latest 2026-07-09 increment adds the finite path predicates
`higham11_7_TridiagonalBranchPathLocalAssumptions`,
`higham11_7_TridiagonalBranchPathLocalResiduals`, and terminal path variants,
plus pointwise adapters from branch assumptions to branch residuals. The global
Theorem 11.7 row still needs the actual mixed-pivot path instantiation and
accumulation into one perturbation.
The follow-up 2026-07-09 increment adds
`higham11_7_tridiagonalBranchPathLocalResiduals_empty`,
`higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_localAssumptions`,
and
`higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_terminalTailAssumptions`,
providing explicit finite-path base and one-step adapters.
A later 2026-07-09 increment adds head/tail projection lemmas for local
assumptions, terminal assumptions, and residuals, giving the future finite-path
induction its elimination helpers.
The latest 2026-07-09 increment adds the matching cons constructors
`higham11_7_tridiagonalBranchPathLocalAssumptions_cons`,
`higham11_7_tridiagonalBranchPathTerminalAssumptions_cons`, and
`higham11_7_tridiagonalBranchPathLocalResiduals_cons`, so the future finite-path
induction can rebuild nonempty path predicates from a head certificate and a
tail path certificate.
The follow-up 2026-07-09 increment packages those projections and constructors
as nonempty-path iff lemmas for local assumptions, terminal assumptions, and
local residuals, exposing the standard head/tail induction split directly.
A later 2026-07-09 increment adds head-step residual handoffs
`higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_localAssumptions`
and
`higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_terminalTailAssumptions`,
so an induction step can rebuild a full path residual from a proved head branch
and an already packaged tail residual.
The latest 2026-07-09 increment adds head-plus-tail assumption handoffs
`higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_tail_localAssumptions`
and
`higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_tail_terminalTailAssumptions`,
so the finite-path induction can consume a head branch certificate and tail path
assumptions directly.
The follow-up 2026-07-09 increment adds the mixed terminal-tail handoff
`higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_localAssumptions_tail_terminalTailAssumptions`,
which covers a local head branch followed by terminal tail assumptions, with the
tail `tail_fl = tail_exact` equalities stated explicitly.
The latest 2026-07-09 increment adds the complementary mixed handoff
`higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_terminalTailAssumptions_tail_localAssumptions`,
which covers a terminal head branch followed by a tail path of local branch
assumptions, with the head `tail_fl = tail_exact` equality stated explicitly.
The path witness extraction increment adds
`higham11_7_tridiagonalBranchLocalResidual_exists_supported_witness` and
`higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses`, so
the next aggregation proof can consume explicit per-branch perturbation matrices
with their componentwise, support, and norm budgets.
A follow-up 2026-07-09 increment composes that extractor with the path-local and
terminal-tail assumption surfaces via
`higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses`
and
`higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses`.
The latest witness increment adds
`higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses_of_uniform_budgets`,
which lets the later aggregation proof replace each branch-local scalar budget
by supplied uniform entry and norm budgets at extraction time.
A companion 2026-07-09 increment exposes the same uniform-budget extraction
directly from path-local and terminal-tail assumptions through
`higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses_of_uniform_budgets`
and
`higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses_of_uniform_budgets`.
The support-sum aggregation increment adds
`higham11_7_tridiagonalLeadingBlockSupport_sum_bound` and
`higham11_7_tridiagonalLeadingBlockSupport_sum_uniform_bound`, so a finite
same-ambient family of supported branch perturbations can be collapsed into one
supported perturbation with summed or uniform componentwise budget.
A follow-up support-sum norm increment adds
`higham11_7_tridiagonalLeadingBlockSupport_sum_bound_with_norm` and
`higham11_7_tridiagonalLeadingBlockSupport_sum_uniform_bound_with_norm`, carrying
the corresponding row-sum `∞`-norm bounds for the collapsed perturbation.
A mixed-offset support-sum increment adds
`higham11_7_tridiagonalLeadingBlockSupport_sum_bound_of_le_offsets` and
`higham11_7_tridiagonalLeadingBlockSupport_sum_bound_with_norm_of_le_offsets`,
so perturbations supported at deeper recursion offsets can be lowered to a
common shallower zero-prefix support before summing.
The printed-budget finite-sum increment adds
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm` and
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm`,
specializing the same aggregation to per-branch budgets `c_t*u*Amax` and the
uniform coefficient budget `c*u*Amax`.
A nonnegative printed-budget increment adds
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_nonneg`
and
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_nonneg`,
deriving the required product-budget nonnegativity from separate nonnegativity
of the coefficients, `u`, and `Amax`.
A mixed-offset printed-budget increment adds
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_of_le_offsets`,
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_of_le_offsets`,
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_of_le_offsets_nonneg`,
and
`higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_of_le_offsets_nonneg`,
combining support-depth lowering with the printed coefficient budgets.
A finite solve-delta sum increment adds
`higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm`,
which aggregates already-embedded residual matrices directly into the
source-facing solve perturbation interface once the final summed solve equation
is available.
A support-free scalar-budget solve-delta increment adds
`higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm_of_coeff_sum_le`
and
`higham11_7_tridiagonal_backward_error_interface_of_uniform_sum_solve_delta_infNorm`,
giving the same already-embedded residual aggregation with a supplied
coefficient majorant or a common per-residual coefficient.
A finite supported solve-delta increment adds
`higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm`
and
`higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets`,
which collapse same-ambient residual families and feed the resulting summed
solve equation into the source-facing perturbation interface with norm bounds.
A coefficient-majorant solve-delta increment adds
`higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_coeff_sum_le`
and
`higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets_of_coeff_sum_le`,
so the summed coefficient can be replaced by a supplied printed constant once
`Σc_t ≤ C` is available.
A uniform-coefficient solve-delta increment adds
`higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm`
and
`higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm_of_le_offsets`,
packaging the common per-branch coefficient case with budget `k*c*u*‖A‖∞`.
An embedded path solve-delta increment adds
`higham11_7_TridiagonalBranchPathSupportedWitnesses`,
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_embedded_sum`,
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_embedded_sum_of_coeff_sum_le`,
`higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_embedded_sum_of_coeff_sum_le`,
and
`higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_embedded_sum_of_coeff_sum_le`,
so path-local or terminal-tail residual packages now feed the source-facing
solve perturbation interface after a concrete same-ambient embedding and summed
solve equation are supplied.
A local-to-ambient lift increment adds
`higham11_7_tridiagonalLocalBlockIndex`,
`higham11_7_tridiagonalLiftLocalBlockPerturbation`,
`higham11_7_tridiagonalLiftLocalBlockPerturbation_bound_leadingBlockSupport`,
`higham11_7_tridiagonalBranchPathSupportedWitnesses_lift_to_ambient`, and
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_of_coeff_sum_le`,
so branch-local witnesses can now be placed into one ambient matrix at supplied
start offsets, with bounds/support preserved and embedded local entries
identified.
A local-to-global budget comparison increment adds
`higham11_7_tridiagonal_local_budget_le_global_of_coeff_roundoff_norm` and
`higham11_7_tridiagonalBranchPath_local_budgets_le_global_of_coeff_roundoff_norm`,
reducing the lifted path theorem's branch-budget side condition to pointwise
coefficient, roundoff, and local norm comparisons.
A lifted zero-offset endpoint increment adds
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_sum_le`,
`higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`,
and
`higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`,
matching the concrete path proof's expected entry points without a separate
offset-lowering side condition.
A scheduled coefficient-majorant endpoint increment adds
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`,
`higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`,
and
`higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`,
choosing an existing zero-based start schedule internally for the coefficient
majorant route.
A scalar-budget zero-offset endpoint increment adds
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
`higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
and
`higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
composing those entry points with the coefficient/roundoff/local-norm budget
comparison lemma.
The scheduled zero-offset endpoint increment adds
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
`higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
and
`higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
choosing an existing zero-based start schedule internally and leaving only the
scheduled lifted solve equation as the path-specific obligation.
A start-offset schedule increment adds
`higham11_7_tridiagonalPathPivotSpan`,
its zero/cons/positive/range lemmas,
`higham11_7_TridiagonalPathStartOffsetsFrom`,
`higham11_7_TridiagonalPathStartOffsets`, and their head/successor/strict-growth
projection lemmas, plus existence, cons, tail, head-tail iff, start-span,
branch-end containment, and last-branch endpoint lemmas, making the mixed
path's concrete offset recurrence explicit and composable by head/tail
induction.
The follow-up schedule-ordering increment adds
`higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_of_lt`,
`higham11_7_tridiagonalPathStartOffsetsFrom_lt_of_lt`,
`higham11_7_tridiagonalPathStartOffsets_branch_end_le_of_lt`, and
`higham11_7_tridiagonalPathStartOffsets_lt_of_lt`, proving that every earlier
scheduled pivot block is consumed before any later branch starts.
The schedule-uniqueness increment adds
`higham11_7_tridiagonalPathStartOffsetsFrom_unique`,
`higham11_7_tridiagonalPathStartOffsetsFrom_exists_unique`,
`higham11_7_tridiagonalPathStartOffsets_unique`, and
`higham11_7_tridiagonalPathStartOffsets_exists_unique`, so later concrete path
proofs can identify any supplied schedule with the canonical recurrence.
The remaining Theorem 11.7 work is still instantiating those adapters over the
full mixed pivot path and instantiating this start-offset schedule,
coefficient/roundoff/local-norm comparisons, and final lifted solve equation.

| Theorem 11.8 | Aasen componentwise backward error + `‖ΔA‖_∞ ≤ (n−1)²γ_{15n+25}‖T̂‖_∞` | `higham11_8_aasen_backward_error_interface` (assumes) | remaining: **fl** analysis of the Aasen recurrences + solve chain (11.15). The **exact-arithmetic** recurrence identities (11.12), (11.13), (11.14) are proved; scalar and finite-sum fl additive error forms of (11.14), including the exact-recurrence bridge to `L k next`, are proved; rounded prefix-dot formation residuals in both ambient `γ_n` and source-length `γ_{i+1}` forms are proved; source-prefix formed-update componentwise and column-lift bounds are proved; the source-prefix column budget is packaged into the relative `L_hat` factor hypothesis for one next-column update and then dispatched to the global relative-factor hypothesis; that source-prefix global bridge now feeds the factorization-product residual directly, leaving the concrete `T_hat` budget as the factorization side's remaining modeled input; the factorization-product residual is bounded by an explicit seven-term budget from entrywise `L̂`/`T̂` factor budgets and by the closed `higham11_15_aasenChainDeltaABound` under relative outer-factor bounds; the exact unpermuted solve-chain algebra is proved; the two outer triangular solves in (11.15) are connected to existing backward-error theorems; the middle tridiagonal solve is connected to Chapter 9's equation-(9.20)--(9.22) source perturbation model; the middle budget is now proved nonnegative and norm-aggregated both to `f(γ_n)‖L_T‖∞‖U_T‖∞` and to the more concrete `f(γ_n)‖|L_T||U_T|‖∞`, with a column-dominant LUFactSpec specialization giving `3f(γ_n)‖T̂‖∞`; the rounded solve-chain components are packaged together; the algebraic collapse to `(A+ΔA)w=rhs` is proved and instantiated with the closed `higham11_15_aasenChainDeltaABound`; factorization and solve-chain residuals are combined into a single `(A+ΔA)ŵ=Pᵀb` source equation with summed componentwise budget; the closed chain budget is aggregated into a two-term normwise triple-product bound; a perturbation dominated by the sum of the factorization and solve-chain closed budgets now receives both the summed normwise budget and the printed normwise predicate when a scalar norm budget is supplied; the scalar norm-budget comparison can now be reduced to primitive factor norm bounds and split into four scalar coefficient pieces, and the rounded/source-prefix source wrappers consume that reduced form directly, including variants where the middle budget is discharged from a relative tridiagonal LU factor-product or abs-LU norm bound; the componentwise/closed-chain ⇒ printed `∞`-norm bridges are proved; the rounded solve-chain source equation is packaged with the printed normwise predicate, and the rounded factorization+solve source equation is packaged with that predicate under an explicit entrywise `η|T̂|` comparison, the scalar norm-budget comparison, separate factor/solve entrywise comparisons whose coefficients add to `η`, or a concrete `T_hat` abs-LU/product-majorant route with exact product majorants, square-product gamma discharge, reduced supplied/source-prefix base-square interfaces, exact-radius endpoints for the source-prefix generated `L_hat` case, `γ_n` exact-radius endpoints (`..._gamma_base_square_exact_radius_gamma_n`) that derive the local `gammaValid n`, `gammaValid 2`, and source-prefix `gammaValid next.val` side conditions from the printed `gammaValid (15n+25)` hypothesis, source-constant endpoints (`..._gamma_base_square_exact_radius_source_constants`) that substitute `κT=1`, `κBT=γ_n`, and `κmidLU=1` directly, factor-cap square helpers (`higham11_8_product_square_bound_of_factor_caps`, `higham11_8_aasen_base_square_bounds_of_factor_caps`), the supplied direct-`T` relative-cap checkerboard endpoint `..._relative_norm_caps_of_T_norm_cap_checkerboard_middle`, the source-prefix factor-cap endpoint `..._gamma_base_square_exact_radius_source_factor_caps`, the direct matrix-norm cap endpoint `..._gamma_base_square_exact_radius_source_norm_caps`, the componentwise-`T` variant `..._source_norm_caps_of_componentwise_T` using `higham11_8_infNorm_le_of_componentwise_abs_bound`, the checkerboard-middle variant `..._source_norm_caps_of_componentwise_T_checkerboard_middle` using `higham11_15_absLU_componentwise_T_bound_of_checkerboard_LUFactSpec`, the source-prefix relative-norm-caps variants `..._relative_norm_caps_of_componentwise_T_checkerboard_middle` and `..._relative_norm_caps_of_T_norm_cap_checkerboard_middle` deriving unscaled exact outer-factor caps from relative caps, the row-sum-caps variants `..._row_sum_caps_of_componentwise_T_checkerboard_middle` and `..._row_sum_caps_of_T_norm_cap_checkerboard_middle` deriving those relative caps from scaled row/column sums, the row/column majorant bridge (`higham11_8_relative_outer_factor_caps_of_row_col_sum_majorants`) deriving relative caps from unscaled sum majorants plus scalar scale comparisons, the entrywise-majorant adapter (`higham11_8_relative_outer_factor_caps_of_entrywise_majorant`) deriving both row and column majorants from a uniform exact-factor entry bound, the Aasen-structure adapter (`higham11_8_relative_outer_factor_caps_of_aasen_entry_bound`) deriving the sharper `(n-1)` row/column majorants from strict-upper and first-column zeros plus that uniform entry bound, the normalized scale bridge (`higham11_8_aasen_outer_factor_scaled_entry_cap`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_scaled_unit`) and inverse-scale bridge (`higham11_8_one_plus_mul_le_one_of_le_inv_one_plus`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`) reduce the Aasen cap side condition to the source-style `κ≤1/(1+γ)`, source-prefix Aasen-structure checkerboard endpoints consuming either that sharper cap or the normalized `(1+γ_n)κ≤1` condition directly, source-prefix entrywise-majorant checkerboard endpoints deriving the exact-radius route's outer-factor caps directly from the uniform exact-factor entry bound, and relative `T_hat` comparison bridges that turn a supplied `|T̂−T|≤γ|T̂|` into the `BT_factor` norm budget plus diagnostic `(1+γ)` exact-`T` entrywise and norm caps. | prove the remaining source/product-size facts feeding the exact-product `T_hat` route: the concrete uniform exact outer-factor entry bound, plus either entrywise `|T|≤|T̂|` or direct `‖T‖∞≤‖T̂‖∞` (the relative error bridge gives only `|Tᵢⱼ|≤(1+γ)|T̂ᵢⱼ|` and `‖T‖∞≤(1+γ)‖T̂‖∞`), a checkerboard total-nonnegative LU certificate for the coefficient-one middle product `|L_T||U_T|≤|T̂|` (or a direct entrywise proof), the concrete source fact `|T̂−T|≤γ_n|T̂|`, and the printed `gammaValid (15n+25)`; the scalar `κT`, `κmidLU`, `κBT` side conditions, relative and unscaled exact outer-factor caps, direct `T`-norm replacement plumbing, local prefix/update/solve gamma-validity conditions, normalized/source-style inverse Aasen entry-cap and base-square handoffs, entrywise outer-factor majorant handoff, and norm/entrywise consequences of a supplied relative `T_hat` perturbation are now discharged by wrappers |

2026-07-09 update: the printed split-entry endpoints
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_coeff`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_coeff`
instantiate the intermediate `η` in the supplied-relative and source-prefix
split-entry routes with the final printed coefficient `(n−1)^2γ_{15n+25}`.
The follow-up printed-gamma variants
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma`
specialize that radius to `gamma fp (15*n+25)` and derive its nonnegativity
from `gammaValid fp (15*n+25)`.
A second follow-up adds
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma_validity`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma_validity`,
which also derive the local `gammaValid n`, `gammaValid 2`, and source-prefix
validity hypotheses from the printed guard.

2026-07-09 update: `higham11_8_aasen_factor_solve_norm_budget_of_relative_T_hat_error`
and
`higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_relative_T_hat_error`
turn the supplied relative `T_hat` comparison into a concrete fallback scalar norm-budget
route. The route uses `κT = 1 + κBT`, so the exact-radius source endpoints still need a
direct `‖T‖∞≤‖T_hat‖∞` or entrywise `|T|≤|T_hat|` fact.
Equivalently, the relative comparison alone gives only the new diagnostic
`|Tᵢⱼ|≤(1+κBT)|T_hatᵢⱼ|` entrywise cap and its `(1+κBT)` norm consequence,
not the coefficient-one exact middle-factor cap.
A later 2026-07-09 increment adds the zero-radius specializations
`higham11_8_abs_T_le_T_hat_of_zero_relative_error` and
`higham11_8_infNorm_T_le_T_hat_of_zero_relative_error`, so if the relative
`T_hat` comparison is supplied with radius `0`, the coefficient-one exact
middle-factor entrywise and norm caps are recovered directly.
The follow-up 2026-07-09 increment adds the supplied exact-radius endpoint
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_constants_of_zero_relative_T_hat`,
which turns the same zero-relative comparison into both the `γ_n` middle
factorization budget and the direct exact-`T` norm cap required by the
source-constant route.
A later 2026-07-09 increment adds the supplied checkerboard endpoint
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle`,
so the same zero-relative handoff now plugs into the route that derives the
middle product from the checkerboard total-nonnegative LU certificate and the
outer products from relative factor caps.
The follow-up 2026-07-09 increment adds the matching source-prefix endpoint
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle`,
so the rounded Aasen recurrence model can generate the relative `L_hat`
hypothesis while the zero-relative `T_hat` comparison supplies the exact-radius
middle-factor handoffs.
A later 2026-07-09 increment adds the row-sum-cap version
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_zero_relative_T_hat_checkerboard_middle`,
so callers can provide scaled exact outer-factor row and column sums directly,
with the zero-relative `T_hat` comparison discharging the remaining
middle-factor obligations.
A follow-up 2026-07-09 increment adds the direct-middle row-sum counterparts
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_componentwise_T`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_T_norm_cap`,
so the same scaled row/column sums can feed routes with a supplied middle
product estimate instead of the checkerboard LU certificate.
The follow-up 2026-07-09 increment adds the entrywise-majorant version
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat_checkerboard_middle`,
so a uniform exact outer-factor entry cap can feed the same source-prefix
checkerboard route when the zero-relative `T_hat` comparison is available.
A later 2026-07-09 increment adds the direct-middle entrywise-majorant
counterparts
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap`,
so the same uniform entry cap can feed routes with a supplied middle product
estimate instead of the checkerboard LU certificate.
A follow-up 2026-07-09 increment adds direct-middle `_entry_bound_nonneg`
variants for those two endpoints, so the uniform absolute entry bound also
supplies the nonnegativity of `κLentry`.
A later 2026-07-09 increment adds the sharper Aasen-structure version
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_zero_relative_T_hat_checkerboard_middle`,
so the strict-upper and first-column-zero structure can reduce the outer-factor
entry-count side while the zero-relative `T_hat` comparison handles the middle
factor.
A follow-up 2026-07-09 increment adds the direct-middle arbitrary-cap
Aasen-structure counterparts
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap`,
so the same strict-upper/first-column-zero outer-factor entry bound can feed
routes with a supplied `|L_T||U_T|≤|T_hat|` middle-product estimate instead of
the checkerboard LU certificate.
A companion 2026-07-09 increment adds direct-middle `_entry_bound_nonneg`
variants
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_entry_bound_nonneg`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_entry_bound_nonneg`,
so the same uniform absolute entry bound supplies the `0≤κLentry` side
condition for those arbitrary-cap direct-middle Aasen endpoints.
A further 2026-07-09 increment adds the matching arbitrary-cap checkerboard
and zero-relative checkerboard `_entry_bound_nonneg` wrappers
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_checkerboard_middle_entry_bound_nonneg`,
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_checkerboard_middle_entry_bound_nonneg`,
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg`,
so every arbitrary-cap Aasen checkerboard route now gets `0≤κLentry` from
the same uniform absolute entry bound.
The latest 2026-07-09 increment adds the normalized Aasen-structure source-prefix
checkerboard endpoints
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T_checkerboard_middle`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap_checkerboard_middle`,
so a concrete uniform exact outer-factor entry bound now only needs the source-scale
comparison `(1+γ_n)κ≤1` before it can feed the checkerboard exact-radius route.
A follow-up adds the direct-middle variants
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap`,
so the same normalized Aasen factor bound can also be used when the
`|L_T||U_T|≤|T_hat|` middle product estimate is proved directly rather than via
the checkerboard LU certificate.
A later 2026-07-09 increment adds the gamma-validity cap wrappers
`higham11_8_gammaValid_15n25_of_unit_roundoff_bound`,
`higham11_8_gammaValid_15n25_of_u_le_cap`, and
`higham11_8_gammaValid_n_two_prefix_of_u_le_cap`, so the printed
`gammaValid fp (15*n+25)` guard can be discharged from either the direct
smallness statement `(15n+25)u<1` or a displayed cap `u≤Ucap`. This does not
settle the remaining exact-product route; it only removes the local gamma
guard plumbing once a source smallness cap is supplied.
The latest 2026-07-09 increment adds
`higham11_8_one_plus_mul_le_one_of_le_inv_one_plus`,
`higham11_8_aasen_outer_factor_scaled_entry_cap_of_le_inv_one_plus`, and
`higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`, so
the Aasen `(n-1)` outer-factor cap can consume a source-style entry estimate
`κ≤1/(1+γ)` directly instead of requiring a separate normalized
`(1+γ)κ≤1` handoff.
A follow-up 2026-07-09 increment adds
`higham11_8_outer_factor_caps_of_aasen_entry_bound_inv_one_plus` and
`higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus`, deriving the
unscaled exact outer-factor caps and the two base square product caps directly
from the same source-style inverse-scale entry estimate.
A later 2026-07-09 increment adds the direct-middle source-prefix endpoints
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap`,
so the exact-radius route can consume `κ≤1/(1+γ_n)` directly when the middle
product estimate is supplied without going through checkerboard LU.
A follow-up 2026-07-09 increment adds the checkerboard-middle inverse-scale
companions
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T_checkerboard_middle`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap_checkerboard_middle`,
so the same source-style entry estimate also feeds the checkerboard LU route
without a normalized-cap handoff.
A later 2026-07-09 increment adds
`higham11_8_nonneg_of_uniform_abs_entry_bound`,
`higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus_of_entry_bound`,
`higham11_8_outer_factor_caps_of_aasen_entry_bound_inv_one_plus_of_entry_bound`,
and
`higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus_of_entry_bound`,
so the lower-level inverse-scale route no longer needs `0≤κ` as a separate
source handoff once the nonempty uniform absolute entry bound is available.
Another 2026-07-09 increment adds the matching normalized-entry helpers
`higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_scaled_unit_of_entry_bound`,
`higham11_8_outer_factor_caps_of_aasen_entry_bound_scaled_unit_of_entry_bound`,
and
`higham11_8_aasen_base_square_bounds_of_entry_bound_scaled_unit_of_entry_bound`,
so the older `(1+γ)κ≤1` route also derives `0≤κ` from the uniform absolute
entry bound.
A follow-up 2026-07-09 increment adds
`higham11_8_relative_outer_factor_caps_of_entrywise_majorant_of_entry_bound`
and
`higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_of_entry_bound`,
so both the generic `n`-entry majorant route and the arbitrary-cap Aasen
`(n-1)` route can derive `0≤κ` from a nonempty uniform absolute entry bound.
A later 2026-07-09 increment lifts that generic `n`-entry nonnegativity
discharge to the source-prefix entrywise-majorant endpoints themselves, adding
`_entry_bound_nonneg` variants for the checkerboard componentwise-`T`,
checkerboard direct-`T`-norm, checkerboard zero-relative, and direct-middle
zero-relative routes.
The follow-up 2026-07-09 endpoint increment lifts that nonnegativity discharge
to the inverse-scale source-prefix exact-radius endpoints themselves, adding
direct-middle and checkerboard-middle `_entry_bound_nonneg` variants for both
the componentwise-`T` and direct-`T`-norm routes.
The latest 2026-07-09 increment adds the matching normalized
`(1+γ_n)κ≤1` source-prefix endpoint wrappers, so the direct-middle and
checkerboard-middle scaled-unit routes now also derive `0≤κ` from the uniform
absolute entry bound.
A further 2026-07-09 increment adds zero-relative `T_hat` checkerboard wrappers
for both the normalized `(1+γ_n)κ≤1` route and the source-style
`κ≤1/(1+γ_n)` route, including `_entry_bound_nonneg` variants. These wrappers
turn the zero relative `T_hat - T` comparison into the `γ_n` middle budget and
the direct exact-`T` norm cap, so the scaled-unit and inverse-scale Aasen
entry-cap endpoints no longer need a separate `T`-norm handoff in the
zero-radius case.
A companion 2026-07-09 increment adds the same zero-relative handoff for the
direct-middle normalized and inverse-scale endpoints
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat`,
plus their `_entry_bound_nonneg` variants. These keep the supplied
`|L_T||U_T|≤|T_hat|` product estimate and remove only the exact-`T` norm
handoff.
A later 2026-07-09 increment factors out the generic direct-middle source-norm
version
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_zero_relative_T_hat`,
so future direct product routes with supplied outer norm caps can use the same
zero-relative handoff without passing a separate exact-`T` norm cap.
A follow-up 2026-07-09 increment instantiates that direct source-norm wrapper
for the row/column sum-cap and entrywise-majorant outer-factor routes, adding
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_zero_relative_T_hat`
and
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat`;
these are the direct-product counterparts of the checkerboard zero-relative
endpoints.

Both single-step §11.1.1 element-growth bounds are now proved: the 1×1 step
`(1+1/α)μ₀` (`oneByOne_schur_growth`) and the 2×2 step `(1+2/(1−α))μ₀`
(`twoByTwo_schur_growth`), the latter resting on the proved determinant magnitude
bound `twoByTwo_completePivot_absdet_lower` and the length-2 inner product over the
inverse-block entries. The finite-prefix and printed-alpha recursion helpers now
match concrete pivot paths whose one-step bounds are available only through the
final active Schur complement and whose initial maximum is normalized. What remains
for Theorem 11.4 is proving those concrete path hypotheses over the whole
factorization, plus the concrete pivot-path first-stage/trailing split and the
floating-point solve error.
The new finite-max, matrix-product, and row-sum/product majorant bridges mean the
remaining 11.4 consumer
can target the source-shaped scalar eq-(4.14) product certificate directly as a
`maxEntryNorm` bound on `|L̂||D̂||L̂ᵀ|`, rather than restating the pointwise
expanded-sum interface; the latest per-row and uniform-entry variants let the
pivot-path proof either postpone final uniformization of the `|L̂|` row-sum caps
or feed plain entry caps directly. The first-stage
plus recursive Schur-complement aggregation bridges now package Higham [608],
eq. (4.11)'s local-plus-recursive product split directly into the same scalar
max-entry certificate once the concrete block bounds are proved, either from
loose `36` shares or from the exact eq-(4.13) coefficient before the final
`≤36` handoff.
A later 2026-07-09 increment adds
`higham11_4_nonneg_of_uniform_abs_entry_bound` plus loose and exact-coefficient
uniform row-sum/entry product wrappers with `_entry_nonneg` suffixes, so a
concrete `|D_hat|≤Dmax` cap no longer needs a separate `0≤Dmax` handoff.
A companion 2026-07-09 increment adds
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_row_sum_bound_entry_nonneg`
and
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_entry_bounds_entry_nonneg`,
so the loose source-shaped `maxEntryNorm` row-sum and uniform-entry routes have
the same discharge.
The follow-up 2026-07-09 increment adds the same `0≤Dmax` discharge for the
per-row exact-coefficient product route
`higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_row_sum_bounds_entry_nonneg`.
Another 2026-07-09 increment adds the corresponding max-entry norm wrappers
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_row_sum_bound_entry_nonneg`,
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_entry_bounds_entry_nonneg`,
and
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_row_sum_bounds_entry_nonneg`,
so the source-shaped `maxEntryNorm` route and the scalar product-certificate
route now have the same `Dmax` nonnegativity discharge.
The latest product-entry nonnegativity increment adds the same discharge for the
lower-level row-sum, uniform-row, and uniform-entry product-entry adapters
`higham11_4_bunchKaufmanProductEntry_le_row_sum_bounds_entry_nonneg`,
`higham11_4_bunchKaufmanProductEntry_le_uniform_row_sum_bound_entry_nonneg`, and
`higham11_4_bunchKaufmanProductEntry_le_uniform_entry_bounds_entry_nonneg`.
A further 2026-07-09 increment composes those exact-coefficient row-sum and
uniform-entry routes into direct Bunch-Kaufman stability consumers
`higham11_4_bunch_kaufman_stability_of_higham_const_uniform_row_sum_bound`,
`higham11_4_bunch_kaufman_stability_of_higham_const_uniform_entry_bounds`, and
`higham11_4_bunch_kaufman_stability_of_higham_const_row_sum_bounds`.
The companion solve-side increment adds
`higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_row_sum_bound`,
`higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_entry_bounds`, and
`higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_row_sum_bounds`.
The latest loose-consumer increment adds
`higham11_4_bunch_kaufman_stability_of_uniform_row_sum_bound`,
`higham11_4_bunch_kaufman_stability_of_uniform_entry_bounds`,
`higham11_4_bunch_kaufman_solve_backward_error_of_uniform_row_sum_bound`, and
`higham11_4_bunch_kaufman_solve_backward_error_of_uniform_entry_bounds` for
routes where the row-sum or uniform-entry cap is already compared to the
printed `36nρₙ‖A‖_M` budget.
Another 2026-07-09 increment composes the first-stage/recursive split
certificates into the source-shaped max-entry norm target through
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_bounds`
and
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_bounds`,
then directly into the stability and solve consumers via
`higham11_4_bunch_kaufman_stability_of_first_stage_recursive_bounds`,
`higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_bounds`,
`higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_bounds`,
and
`higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_bounds`.

## External proof sources
| Selected claim | Source and exact location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| Theorems 11.3, 11.4 (proofs not in book ch.11) | N. J. Higham, *Stability of the diagonal pivoting method with partial pivoting*, SIAM J. Matrix Anal. Appl. 18(1) (1997) 52–65 = book ref **[608]**. Free: `nhigham.com/wp-content/uploads/2022/11/high97d.pdf`, MIMS EPrints 344. Obtained 2026-07-05 (Max authorized web pull). | full proof: paper Thm 4.1 = book 11.3 (componentwise induction §4.2, eqs 4.6–4.10), paper Thm 4.2 = book 11.4 (norm bound §4.3, eqs 4.11–4.14, appendix A.1–A.3) | constants formalized (`bunch_kaufman_bound_const_le_36` eq 4.13, `..._pivot_norm_const_le_six` A.3, `..._recip_alpha_lt_two`); exact base `oneByOne_step_factorization`; per-step fl `fl_oneByOne_schur_step_error`/`_solve_backward_error`; 11.4 finite max-entry product norm, matrix-product/max-entry-norm notation bridge, row-sum/product majorant bridge, loose and exact-coefficient first-stage/recursive aggregation bridges, and consumer bridges | **partially formalized**; concrete block-matrix induction and pivot-path product split remain (unblocked, large). Paper's (4.5) 2×2-solve backward error = book **Problem 11.5 (benchmark-reserved)** → stays a hypothesis. |
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
  - 2026-07-09 Theorem 11.7 tridiagonal matrix-entry norm bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal 2×2 exact inverse-ratio local-recursive increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_exact_inverse_ratio`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal 2×2 exact inverse-ratio pivot-bound increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_exact_inverse_ratio_of_pivot_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal 1×1 local-recursive branch increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_oneByOne_correction_le_of_choice`,
    `higham11_7_fl_tridiagonal_oneByOne_schur_step_printed_bound_of_choice`, and
    `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal 1×1 scalar local-recursive norm-bound increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalOneByOneLiftTrailingPerturbation_bound_leadingBlockSupport` and
    `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_with_norm_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal 1×1 branch-derived nonzero-pivot increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_of_subdiagonal_ne_zero`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal local `σ=‖A‖∞` branch endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_infNorm_choice` and
    `higham11_7_fl_tridiagonal_oneByOne_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport_infNorm_entries_infNorm_choice_of_subdiagonal_ne_zero`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal branch-indexed local residual increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_TridiagonalBranchLocalAssumptions`,
    `higham11_7_TridiagonalBranchLocalResidual`, and
    `higham11_7_tridiagonalBranchLocalResidual_of_localAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 tridiagonal terminal-tail branch increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalRecursiveTailZeroResidual`,
    `higham11_7_tridiagonalRecursiveTailZeroResidual_infNorm`,
    `higham11_7_TridiagonalBranchTerminalAssumptions`, and
    `higham11_7_tridiagonalBranchLocalResidual_of_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 terminal-tail local-assumption adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchLocalAssumptions_of_terminalTailAssumptions`
    and
    `higham11_7_tridiagonalBranchPathLocalAssumptions_of_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot path interface increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_TridiagonalBranchPathLocalAssumptions`,
    `higham11_7_TridiagonalBranchPathLocalResiduals`,
    `higham11_7_tridiagonalBranchPathLocalResiduals_of_localAssumptions`, and
    `higham11_7_tridiagonalBranchPathLocalResiduals_of_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot path base/singleton increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalResiduals_empty`,
    `higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_localAssumptions`, and
    `higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot path head/tail projection increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalAssumptions_tail`,
    `higham11_7_tridiagonalBranchPathTerminalAssumptions_tail`, and
    `higham11_7_tridiagonalBranchPathLocalResiduals_tail`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot path cons constructor increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalAssumptions_cons`,
    `higham11_7_tridiagonalBranchPathTerminalAssumptions_cons`, and
    `higham11_7_tridiagonalBranchPathLocalResiduals_cons`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot path head/tail iff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalAssumptions_iff_head_tail`,
    `higham11_7_tridiagonalBranchPathTerminalAssumptions_iff_head_tail`, and
    `higham11_7_tridiagonalBranchPathLocalResiduals_iff_head_tail`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot head residual handoff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_localAssumptions`
    and
    `higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot head/tail assumption handoff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_tail_localAssumptions`
    and
    `higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_tail_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot local-head terminal-tail handoff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_localAssumptions_tail_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot terminal-head local-tail handoff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalResiduals_cons_of_head_terminalTailAssumptions_tail_localAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot path witness extraction increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchLocalResidual_exists_supported_witness` and
    `higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot assumption-to-witness increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses`
    and
    `higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot uniform-budget witness increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses_of_uniform_budgets`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot assumption uniform-budget witness increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses_of_uniform_budgets`
    and
    `higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses_of_uniform_budgets`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite support-sum aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_sum_bound` and
    `higham11_7_tridiagonalLeadingBlockSupport_sum_uniform_bound`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite support-sum norm aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_sum_bound_with_norm` and
    `higham11_7_tridiagonalLeadingBlockSupport_sum_uniform_bound_with_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-offset support-sum aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_sum_bound_of_le_offsets` and
    `higham11_7_tridiagonalLeadingBlockSupport_sum_bound_with_norm_of_le_offsets`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-offset printed support-sum aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_of_le_offsets`,
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_of_le_offsets`,
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_of_le_offsets_nonneg`,
    and
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_of_le_offsets_nonneg`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite solve-delta sum aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite solve-delta scalar-budget aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm_of_coeff_sum_le`
    and
    `higham11_7_tridiagonal_backward_error_interface_of_uniform_sum_solve_delta_infNorm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite supported solve-delta aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm`
    and
    `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite supported solve-delta coefficient-majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_coeff_sum_le`
    and
    `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets_of_coeff_sum_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite supported solve-delta uniform-coefficient increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm`
    and
    `higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm_of_le_offsets`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite support-sum printed-budget aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm` and
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite support-sum printed-budget nonnegative increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_bound_with_norm_nonneg`
    and
    `higham11_7_tridiagonalLeadingBlockSupport_sum_printed_uniform_bound_with_norm_nonneg`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 embedded path solve-delta aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_embedded_sum_of_coeff_sum_le`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_embedded_sum_of_coeff_sum_le`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_embedded_sum_of_coeff_sum_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 local-to-ambient path lift increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_bound_leadingBlockSupport`,
    `higham11_7_tridiagonalBranchPathSupportedWitnesses_lift_to_ambient`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_of_coeff_sum_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 local-to-global path budget comparison increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_local_budget_le_global_of_coeff_roundoff_norm` and
    `higham11_7_tridiagonalBranchPath_local_budgets_le_global_of_coeff_roundoff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 lifted zero-offset path endpoints increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_sum_le`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 lifted zero-offset scalar-budget endpoints increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 printed split-entry normwise endpoints increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_coeff`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_coeff`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma`,
    plus the validity-discharge variants
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma_validity` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma_validity`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 scheduled lifted zero-offset endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 mixed-path start-offset schedule increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchSupportOffset_pos`,
    `higham11_7_tridiagonalBranchSupportOffset_le_two`,
    `higham11_7_tridiagonalPathPivotSpan`,
    `higham11_7_tridiagonalPathPivotSpan_zero`,
    `higham11_7_tridiagonalPathPivotSpan_cons`,
    `higham11_7_tridiagonalPathPivotSpan_pos`,
    `higham11_7_tridiagonalPathPivotSpan_ge_length`,
    `higham11_7_tridiagonalPathPivotSpan_le_two_mul`,
    `higham11_7_TridiagonalPathStartOffsetsFrom`,
    `higham11_7_TridiagonalPathStartOffsets`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_head`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_succ`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_succ_lt`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_cons`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_tail`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_iff_head_tail`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_exists`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_base_le`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_lt_base_add_pivotSpan`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_base_add_pivotSpan`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_last_branch_end_eq`,
    `higham11_7_tridiagonalPathStartOffsets_head`,
    `higham11_7_tridiagonalPathStartOffsets_succ`,
    `higham11_7_tridiagonalPathStartOffsets_succ_lt`,
    `higham11_7_tridiagonalPathStartOffsets_tail`,
    `higham11_7_tridiagonalPathStartOffsets_iff_head_tail`,
    `higham11_7_tridiagonalPathStartOffsets_exists`,
    `higham11_7_tridiagonalPathStartOffsets_lt_pivotSpan`,
    `higham11_7_tridiagonalPathStartOffsets_branch_end_le_pivotSpan`, and
    `higham11_7_tridiagonalPathStartOffsets_last_branch_end_eq`
    → elaborate; projection lemmas axiom-free, branch/span/strict-growth/positivity/existence/cons/tail/iff/containment/endpoint lemmas axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 mixed-path schedule ordering increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_of_lt`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_lt_of_lt`,
    `higham11_7_tridiagonalPathStartOffsets_branch_end_le_of_lt`, and
    `higham11_7_tridiagonalPathStartOffsets_lt_of_lt`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 mixed-path schedule uniqueness increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathStartOffsetsFrom_unique`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_exists_unique`,
    `higham11_7_tridiagonalPathStartOffsets_unique`, and
    `higham11_7_tridiagonalPathStartOffsets_exists_unique`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
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
  - 2026-07-09 Theorem 11.3 all-1×1 norm-bound packaging increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_3_infNorm_le_of_componentwise_bound_nonneg`,
    `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne_with_norm_bounds`, and
    `higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne_with_norm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 outer-factor row/column majorant bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_relative_infNorm_cap_of_row_sum_majorant` and
    `higham11_8_relative_outer_factor_caps_of_row_col_sum_majorants`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 outer-factor entrywise-majorant bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_relative_outer_factor_caps_of_entrywise_majorant`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 Aasen outer-factor `(n-1)` majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_sum_abs_le_card_pred_mul_of_one_zero`,
    `higham11_8_aasen_outer_factor_row_col_sum_majorants_of_entry_bound`, and
    `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 Aasen outer-factor normalized scale-cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_aasen_outer_factor_scaled_entry_cap` and
    `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_scaled_unit`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 Aasen outer-factor inverse-scale cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_one_plus_mul_le_one_of_le_inv_one_plus`,
    `higham11_8_aasen_outer_factor_scaled_entry_cap_of_le_inv_one_plus`, and
    `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 Aasen outer-factor inverse-scale square-cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_outer_factor_caps_of_aasen_entry_bound_inv_one_plus` and
    `higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 Aasen outer-factor `(n-1)` source-prefix endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_checkerboard_middle` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 source-prefix entrywise outer-factor endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T_checkerboard_middle` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 generic entrywise-majorant endpoint nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T_checkerboard_middle_entry_bound_nonneg`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap_checkerboard_middle_entry_bound_nonneg`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat_entry_bound_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 relative `T_hat` norm bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_infNorm_T_hat_sub_T_le_mul_of_relative_error`,
    `higham11_8_infNorm_scaled_abs_T_hat_le`, and
    `higham11_8_infNorm_T_le_one_plus_gamma_T_hat_of_relative_error`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 relative `T_hat` entrywise bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_abs_T_le_one_plus_gamma_T_hat_of_relative_error` and
    `higham11_8_infNorm_T_le_one_plus_gamma_T_hat_of_relative_error`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_abs_T_le_T_hat_of_zero_relative_error` and
    `higham11_8_infNorm_T_le_T_hat_of_zero_relative_error`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` source-constant endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_constants_of_zero_relative_T_hat`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` supplied checkerboard endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` source-prefix checkerboard endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` source-prefix direct norm-cap endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_zero_relative_T_hat`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` direct row-sum/entrywise endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_zero_relative_T_hat` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` source-prefix row-sum endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_zero_relative_T_hat_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 source-prefix direct row-sum endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_componentwise_T` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_row_sum_caps_of_T_norm_cap`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 source-prefix direct entrywise-majorant endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 direct entrywise-majorant endpoint nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_componentwise_T_entry_bound_nonneg` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_T_norm_cap_entry_bound_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 direct Aasen-entry arbitrary-cap endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 direct Aasen-entry arbitrary-cap nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_entry_bound_nonneg` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_entry_bound_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 checkerboard Aasen-entry arbitrary-cap nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_checkerboard_middle_entry_bound_nonneg`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_checkerboard_middle_entry_bound_nonneg`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` source-prefix entrywise-majorant endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_entrywise_outer_factor_majorant_of_zero_relative_T_hat_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` source-prefix Aasen-entry endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_zero_relative_T_hat_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` normalized/source-style Aasen endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat_checkerboard_middle`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_checkerboard_middle`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_checkerboard_middle_entry_bound_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 zero-relative `T_hat` direct-middle normalized/source-style Aasen endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_zero_relative_T_hat_entry_bound_nonneg`,
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat`, and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_entry_bound_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 relative `T_hat` scalar budget reducer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_aasen_factor_solve_norm_budget_of_relative_T_hat_error` and
    `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_relative_T_hat_error`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 printed gamma-validity guard increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_gammaValid_15n25_of_unit_roundoff_bound`,
    `higham11_8_gammaValid_15n25_of_u_le_cap`, and
    `higham11_8_gammaValid_n_two_prefix_of_u_le_cap`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 normalized Aasen outer-factor source-prefix endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T_checkerboard_middle` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 normalized Aasen direct-middle source-prefix endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 inverse-scale Aasen direct-middle source-prefix endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 inverse-scale Aasen checkerboard source-prefix endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T_checkerboard_middle` and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap_checkerboard_middle`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 inverse-scale entry-bound nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_nonneg_of_uniform_abs_entry_bound`,
    `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus_of_entry_bound`, and
    `higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus_of_entry_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 normalized entry-bound nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_scaled_unit_of_entry_bound`,
    `higham11_8_outer_factor_caps_of_aasen_entry_bound_scaled_unit_of_entry_bound`, and
    `higham11_8_aasen_base_square_bounds_of_entry_bound_scaled_unit_of_entry_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 arbitrary-cap entry-bound nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_relative_outer_factor_caps_of_entrywise_majorant_of_entry_bound`
    and
    `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_of_entry_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 source-prefix endpoint nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified direct-middle and checkerboard-middle
    `_entry_bound_nonneg` inverse-scale source-prefix endpoints → elaborate;
    axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.8 normalized source-prefix endpoint nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified direct-middle and checkerboard-middle
    scaled-unit `_entry_bound_nonneg` source-prefix endpoints → elaborate;
    axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 max-entry norm iff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_absLDLTProduct_entry_le_maxEntryNorm` and
    `higham11_4_maxEntryNorm_absLDLTProduct_le_iff`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 expanded max-entry norm iff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_maxEntryNorm_absLDLTProduct_le_iff_product_entries`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 row-sum/product majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanProductEntry_le_row_sum_bounds`,
    `higham11_4_bunchKaufmanProductEntry_le_uniform_row_sum_bound`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_row_sum_bound`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_uniform_row_sum_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 loose max-entry product cap nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_row_sum_bound_entry_nonneg`
    and
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_entry_bounds_entry_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 exact-coefficient row-sum/product majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_row_sum_bound`
    and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_row_sum_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 uniform-entry product majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanProductEntry_le_uniform_entry_bounds`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_entry_bounds`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_entry_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 uniform product cap nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_nonneg_of_uniform_abs_entry_bound`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_uniform_entry_bounds_entry_nonneg`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_entry_bounds_entry_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 per-row product cap nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_row_sum_bounds_entry_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 max-entry norm product cap nonnegativity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_row_sum_bound_entry_nonneg`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_entry_bounds_entry_nonneg`, and
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_row_sum_bounds_entry_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 product-entry nonnegativity adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanProductEntry_le_row_sum_bounds_entry_nonneg`,
    `higham11_4_bunchKaufmanProductEntry_le_uniform_row_sum_bound_entry_nonneg`, and
    `higham11_4_bunchKaufmanProductEntry_le_uniform_entry_bounds_entry_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 row-sum stability consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_stability_of_higham_const_uniform_row_sum_bound`,
    `higham11_4_bunch_kaufman_stability_of_higham_const_uniform_entry_bounds`, and
    `higham11_4_bunch_kaufman_stability_of_higham_const_row_sum_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 row-sum solve consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_row_sum_bound`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_entry_bounds`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_row_sum_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 loose row-sum/uniform-entry consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_stability_of_uniform_row_sum_bound`,
    `higham11_4_bunch_kaufman_stability_of_uniform_entry_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_uniform_row_sum_bound`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_uniform_entry_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 per-row exact-coefficient row-sum/product majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_row_sum_bounds`
    and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_row_sum_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 first-stage/recursive product aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_first_stage_recursive_product_bound`,
    `higham11_4_product_entries_of_first_stage_recursive_bounds`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 exact-coefficient first-stage/recursive product aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_first_stage_recursive_product_bound_of_higham_const`,
    `higham11_4_product_entries_of_first_stage_recursive_higham_const_bounds`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 first-stage/recursive max-entry norm increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_bounds`
    and
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 first-stage/recursive consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_bounds`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_bounds`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.4 max-entry product bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_stability_of_max_entry_product_bound` and
    `higham11_4_bunch_kaufman_solve_backward_error_of_max_entry_product_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.4 finite max-entry product norm increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanProductEntry_le_productMax`,
    `higham11_4_bunchKaufmanProductMax_le_iff`,
    `higham11_4_bunch_kaufman_stability_of_productMax_le`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_productMax_le`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.4 finite max-entry packaging increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanProductEntry_nonneg`,
    `higham11_4_bunchKaufmanProductMax_nonneg`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_product_entries`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.4 matrix-product notation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanProductEntry_eq_absLDLTProduct`,
    `higham11_4_bunchKaufmanProductMax_le_iff_absLDLTProduct`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_absLDLTProduct_entries`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.4 max-entry norm bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanProductMax_eq_maxEntryNorm_absLDLTProduct` and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_maxEntryNorm_absLDLTProduct`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-08 Theorem 11.4 direct max-entry consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_stability_of_maxEntryNorm_absLDLTProduct_le` and
    `higham11_4_bunch_kaufman_solve_backward_error_of_maxEntryNorm_absLDLTProduct_le`
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
- New vs pre-existing warnings: **no new warnings** from the edited Chapter 11 file. The target
  build warnings are pre-existing in `HighamChapter9.lean`, `CholeskyFl.lean`, and
  `HighamChapter10.lean` (deprecated `Fin` coercions, unused simp arguments, one `ring`
  linter note, unnecessary `simpa`, and unused variables).

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
