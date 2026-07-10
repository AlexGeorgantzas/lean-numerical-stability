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
| Thm 11.7 branch residual equation witnesses | `higham11_7_TridiagonalBranchLocalResidualWitness`, `higham11_7_tridiagonalBranchLocalResidual_exists_residual_witness`, `higham11_7_tridiagonalBranchLocalResidualWitness_supported` | Ch11 | **new this session**; opens a branch-local residual to a specific perturbation matrix that retains not only bounds/support/norm data but also the branch scalar residual equation, and then strips the equation-bearing witness back to the supported perturbation package consumed by path aggregation. |
| Thm 11.7 terminal-tail branch adapter | `higham11_7_tridiagonalRecursiveTailZeroResidual`, `higham11_7_tridiagonalRecursiveTailZeroResidual_infNorm`, `higham11_7_TridiagonalBranchTerminalAssumptions`, `higham11_7_tridiagonalBranchLocalResidual_of_terminalTailAssumptions` | Ch11 | **new this session**; supplies the zero recursive-tail certificate for the terminal local branch and packages either accepted branch into the common branch residual when `tail_fl = tail_exact`. This gives the future mixed-pivot path induction a base case companion to the branch-indexed local step adapter. |
| Thm 11.7 finite mixed-pivot path interface | `higham11_7_TridiagonalBranchPathLocalAssumptions`, `higham11_7_TridiagonalBranchPathLocalResiduals`, `higham11_7_tridiagonalBranchPathLocalResiduals_of_localAssumptions`, `higham11_7_TridiagonalBranchPathTerminalAssumptions`, `higham11_7_tridiagonalBranchPathLocalResiduals_of_terminalTailAssumptions`, `higham11_7_tridiagonalBranchPathLocalResiduals_empty`, `higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_localAssumptions`, `higham11_7_tridiagonalBranchPathLocalResiduals_singleton_of_terminalTailAssumptions`, `higham11_7_tridiagonalBranchPathLocalAssumptions_head`, `higham11_7_tridiagonalBranchPathLocalAssumptions_tail`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_head`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_tail`, `higham11_7_tridiagonalBranchPathLocalResiduals_head`, `higham11_7_tridiagonalBranchPathLocalResiduals_tail` | Ch11 | **new this session**; lifts the branch-local and terminal-tail adapters pointwise over a finite family of `1×1`/`2×2` tridiagonal branch choices with per-step dimensions, matrices, budgets, and tail scalars. The empty and singleton adapters expose the induction base and one-step entry points; the head/tail projections expose the elimination side for future induction. This is path-level scaffolding for the remaining mixed-pivot induction; it still leaves the global accumulation of those pointwise residuals open. |
| Thm 11.7 finite mixed-pivot last-terminal path assembly | `higham11_7_tridiagonalBranchPathLocalAssumptions_of_init_localAssumptions_last_terminalTailAssumptions`, `higham11_7_tridiagonalBranchPathLocalResiduals_of_init_localAssumptions_last_terminalTailAssumptions` | Ch11 | **new this session**; packages the concrete recursion shape where all initial branches carry ordinary local recursive assumptions and the final branch is discharged by the terminal-tail adapter, yielding both path-local assumptions and path-local residuals. |
| Thm 11.7 finite mixed-pivot path witness extraction | `higham11_7_tridiagonalBranchLocalResidual_exists_supported_witness`, `higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses`, `higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses`, `higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses_of_uniform_budgets`, `higham11_7_tridiagonalBranchPathLocalAssumptions_exists_supported_witnesses_of_uniform_budgets`, `higham11_7_tridiagonalBranchPathTerminalAssumptions_exists_supported_witnesses_of_uniform_budgets` | Ch11 | **new this session**; extracts explicit per-branch perturbation matrices from branch-local, finite-path residual, path-local-assumption, and terminal-tail-assumption packages, retaining the componentwise budget, leading-block support, and `∞`-norm bound needed by the later global accumulation theorem. Uniform-budget variants package supplied per-branch scalar comparisons into the extracted witnesses directly. |
| Thm 11.7 finite mixed-pivot residual equation witnesses | `higham11_7_TridiagonalBranchPathResidualWitnesses`, `higham11_7_tridiagonalBranchPathLocalResiduals_exists_residual_witnesses`, `higham11_7_tridiagonalBranchPathResidualWitnesses_supported`, `higham11_7_tridiagonalBranchPathSupportedWitnesses_bound`, `higham11_7_tridiagonalBranchPathSupportedWitnesses_leadingBlockSupport`, `higham11_7_tridiagonalBranchPathSupportedWitnesses_infNorm_bound`, `higham11_7_tridiagonalBranchPathResidualWitnesses_bound`, `higham11_7_tridiagonalBranchPathResidualWitnesses_leadingBlockSupport`, `higham11_7_tridiagonalBranchPathResidualWitnesses_infNorm_bound`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_leadingBlockSupport_family`, `higham11_7_tridiagonalConcretePathResidualWitnesses_leadingBlockSupport_family` | Ch11 | **new this session**; lifts the richer branch residual-witness predicate over finite paths and extracts witnesses that preserve each branch's scalar residual equation, not only the bound/support/norm data. The support bridge lets those equation-bearing witnesses feed the existing supported-witness lifted-sum aggregation theorems without re-extraction. The named bound/support/norm accessors keep downstream path-lift and solve-row proofs from unfolding the witness tuple or manually projecting support from residual witnesses, and the concrete prefix-span support-family adapters return exactly the `hEsupp` family consumed by the lifted first-trailing solve-row decomposition lemmas. |
| Thm 11.7 branch residual-equation accessors | `higham11_7_tridiagonalBranchLocalResidualWitness_one_equation`, `higham11_7_tridiagonalBranchLocalResidualWitness_two_equation`, `higham11_7_tridiagonalBranchLocalResidualWitness_one_equation_lifted`, `higham11_7_tridiagonalBranchLocalResidualWitness_two_equation_lifted` | Ch11 | **new this session**; exposes the scalar first-trailing residual equations carried by the 1×1 and 2×2 branch witnesses, and the corresponding equations after the local perturbation is lifted into a shared ambient matrix at the embedded first-trailing index. This gives the remaining path solve-equation induction named access to the local residual equalities without unfolding the witness predicate. |
| Thm 11.7 concrete path residual-witness branch accessors | `higham11_7_tridiagonalPathFirstTrailingIndex_one_lt_pivotSpan_succ`, `higham11_7_tridiagonalPathFirstTrailingIndex_two_lt_pivotSpan_succ`, `higham11_7_tridiagonalConcretePathResidualWitnesses_one`, `higham11_7_tridiagonalConcretePathResidualWitnesses_two` | Ch11 | **new this session**; proves that a concrete prefix-span branch's first trailing scalar embeds into the full `pathSpan+1` ambient for both accepted pivot sizes, and gives cast-safe branch accessors from an equation-bearing concrete path witness to the corresponding `1×1` or `2×2` branch-local witness. This is the path-level handoff needed to apply the lifted residual-equation accessors in the final solve-equation induction without unfolding dependent path predicates. |
| Thm 11.7 concrete path lifted residual-equation accessors | `higham11_7_tridiagonalPathFirstTrailingIndex_one`, `higham11_7_tridiagonalPathFirstTrailingIndex_two`, `higham11_7_tridiagonalPathFirstTrailingIndex_one_val_eq_branch_end`, `higham11_7_tridiagonalPathFirstTrailingIndex_two_val_eq_branch_end`, `higham11_7_tridiagonalPathFirstTrailingIndex_one_val_lt_one_val_of_lt`, `higham11_7_tridiagonalPathFirstTrailingIndex_one_val_lt_two_val_of_lt`, `higham11_7_tridiagonalPathFirstTrailingIndex_two_val_lt_one_val_of_lt`, `higham11_7_tridiagonalPathFirstTrailingIndex_two_val_lt_two_val_of_lt`, `higham11_7_tridiagonalPathFirstTrailingIndex`, `higham11_7_tridiagonalPathFirstTrailingIndex_of_one`, `higham11_7_tridiagonalPathFirstTrailingIndex_of_two`, `higham11_7_tridiagonalPathFirstTrailingIndex_val`, `higham11_7_tridiagonalPathFirstTrailingIndex_val_lt_of_lt`, `higham11_7_tridiagonalPathFirstTrailingIndex_injective`, `higham11_7_tridiagonalPathFirstTrailingIndex_pos`, `higham11_7_tridiagonalPathFirstTrailingIndex_ne_zero`, `higham11_7_tridiagonalPath_zero_ne_firstTrailingIndex`, `higham11_7_tridiagonalPathFirstTrailingIndex_val_le_pivotSpan`, `higham11_7_tridiagonalPathFirstTrailingIndex_last_val_eq_pivotSpan`, `higham11_7_tridiagonalPathFirstTrailingIndex_last_eq_finLast`, `higham11_7_tridiagonalPathFirstTrailingIndex_eq_finLast_iff`, `higham11_7_tridiagonalPathFirstTrailingIndex_val_eq_pivotSpan_iff`, `higham11_7_tridiagonalPathFirstTrailingIndex_ne_finLast_of_ne_last`, `higham11_7_tridiagonalPathFirstTrailingIndex_val_lt_pivotSpan_of_ne_last`, `higham11_7_tridiagonalPathFirstTrailingIndex_val_lt_pivotSpan_iff_ne_last`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_one`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_two`, `higham11_7_tridiagonalConcretePathResidualWitnesses_one_equation_lifted`, `higham11_7_tridiagonalConcretePathResidualWitnesses_two_equation_lifted` | Ch11 | **new this session**; specializes the branch lifted residual equations to concrete prefix-span paths and exposes the scalar first-trailing equations at full-ambient path indices for both accepted pivot sizes. The first-trailing value lemmas identify those concrete rows with the consumed-branch endpoints, the four comparison lemmas order the actual first-trailing `Fin` row values across all one/two branch combinations, the branch-uniform first-trailing index API packages those cases into an endpoint-valued injective map with positive and contained endpoint facts, the leading-row exclusion lemmas put row `0` in the complement of the endpoint set, the last-branch endpoint lemma identifies the final first-trailing row with `Fin.last`, the value iff and strict non-final lemmas make the final ambient row coverage unique at the level of natural row values, and the simp lemmas reduce lifted perturbations at those path indices back to the local first-trailing perturbation entry, removing another dependent-cast handoff from the remaining lifted solve-equation induction. |
| Thm 11.7 last-terminal residual-witness extraction | `higham11_7_tridiagonalBranchPathResidualWitnesses_exists_of_init_localAssumptions_last_terminalTailAssumptions`, `higham11_7_tridiagonalConcretePathResidualWitnesses_exists_of_init_localAssumptions_last_terminalTailAssumptions` | Ch11 | **new this session**; extracts equation-bearing residual witnesses directly from the initial-local/last-terminal path shape, including the concrete prefix-span full-ambient specialization. This is the witness data needed for the remaining lifted solve-equation induction and does **not** close the Theorem 11.7 row by itself. |
| Thm 11.7 solve-side interface bridge | `higham11_7_tridiagonal_backward_error_interface_of_solve_delta`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_nonneg`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm` | Ch11 | **new this session**; if the recursive tridiagonal analysis constructs the solve-side perturbation `ΔA₂` with the printed componentwise budget, the factorization-side perturbation `ΔA₁` can be filled by zero to produce the source-facing Theorem 11.7 interface shape; the `_nonneg` form derives `0 ≤ c*u*Amax` from separate nonnegativity of `c`, `u`, and `Amax`, and the `_infNorm` form specializes the budget to `c*u*‖A‖∞` |
| Thm 11.7 generic path row-coverage splitters | `higham11_7_tridiagonalPath_forall_of_firstTrailingIndex_and_complement`, `higham11_7_tridiagonalPath_forall_of_firstTrailingIndex_zero_and_complement`, `higham11_7_tridiagonalPath_forall_of_nonfinal_firstTrailingIndex_last_and_complement`, `higham11_7_tridiagonalPath_forall_of_nonfinal_firstTrailingIndex_last_zero_and_complement` | Ch11 | **new this session**; abstracts the final lifted `∀ i` row proof obligation over an arbitrary row predicate, with variants that isolate the leading row and terminal last row before falling through to the endpoint-complement case. These splitters let the remaining solve-equation proof combine branch endpoint rows, the terminal-tail base row, and non-endpoint rows without restating the long matrix-vector formula. |
| Thm 11.7 branch-uniform endpoint row dispatch | `higham11_7_tridiagonalPath_firstTrailingIndex_rows_of_one_two`, `higham11_7_tridiagonalPath_nonfinal_firstTrailingIndex_rows_of_one_two`, `higham11_7_tridiagonalPath_forall_of_one_two_nonfinal_firstTrailingIndex_last_and_complement`, `higham11_7_tridiagonalPath_forall_of_one_two_nonfinal_firstTrailingIndex_last_zero_and_complement` | Ch11 | **new this session**; turns separate `1×1` and `2×2` row proofs at the pivot-specific first-trailing indices into proofs at the branch-uniform endpoint map. The non-final version leaves the final branch available for the terminal-tail last-row proof, and the combined coverage variants package non-final one/two endpoint rows, the terminal last row, and optional leading-row handling into one row-predicate theorem for the remaining lifted solve equation. |
| Thm 11.7 second-pivot complement row classification | `higham11_7_tridiagonalPathSecondPivotIndex_two`, `higham11_7_tridiagonalPathSecondPivotIndex_two_val`, `higham11_7_tridiagonalPathSecondPivotIndex_two_ne_zero`, `higham11_7_tridiagonalPath_zero_ne_secondPivotIndex_two`, `higham11_7_tridiagonalPath_row_eq_zero_or_firstTrailingIndex_or_secondPivot`, `higham11_7_tridiagonalPath_complement_eq_secondPivot`, `higham11_7_tridiagonalPath_forall_of_zero_firstTrailingIndex_secondPivot`, `higham11_7_tridiagonalPath_forall_of_one_two_nonfinal_firstTrailingIndex_last_zero_secondPivot`, `higham11_7_tridiagonalPath_solve_rows_of_one_two_nonfinal_firstTrailingIndex_last_zero_secondPivot` | Ch11 | **new this session**; classifies every concrete mixed-path row as the leading row, a branch-uniform first-trailing endpoint, or the second pivot row of an accepted `2×2` branch. The solve-row splitter replaces the prior arbitrary non-leading/non-endpoint complement proof with concrete second-pivot row obligations; it does not close Theorem 11.7 yet because the branch-local/full-ambient second-pivot solve row remains to be proved. |
| Thm 11.7 second-pivot/first-trailing adjacency | `higham11_7_tridiagonalPathSecondPivotIndex_two_val_succ_eq_firstTrailingIndex`, `higham11_7_tridiagonalPathSecondPivotIndex_two_val_lt_firstTrailingIndex`, `higham11_7_tridiagonalPathSecondPivotIndex_two_ne_firstTrailingIndex` | Ch11 | **new this session**; records that an accepted `2×2` branch's second-pivot row is immediately before, strictly before, and distinct from the branch-uniform first-trailing row. This structural bridge prepares the remaining reduced base-plus-earlier second-pivot row handoff. |
| Thm 11.7 second-pivot lifted solve-row decomposition | `higham11_7_tridiagonalPathSecondPivotIndex_two_eq_pathLocalBlockIndex_cast`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathSecondPivot_two_row_of_lt`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_later_rows_sum_zero`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_later_rows_dot_sum_zero`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_current_family_rows_dot_eq_pathLocal`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_rows_dot_eq_prefix_sum`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_prefix_rows_dot_eq_before_add_current`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_rows_dot_eq_before_add_current`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_rows_dot_eq_before_dot_add_current_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_rows_dot_eq_before_dot_add_current_pathLocal_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_solve_row_eq_A_dot_add_before_dot_add_current_pathLocal_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalConcretePathResidualWitnesses_pathSecondPivot_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathSecondPivot_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq` | Ch11 | **new this session**; proves that at an accepted `2×2` branch's second-pivot row, later branch lifts vanish, the current lift reindexes to the branch-local second-pivot row, and the full ambient solve-row dot product splits into base `A`, earlier lifts, and the current branch-local contribution. The remaining Theorem 11.7 work is now the branch-local second-pivot row equation in this exposed base-plus-earlier-plus-current path-local form. |
| Thm 11.7 second-pivot complement solve-row bridge | `higham11_7_tridiagonalConcretePathResidualWitnesses_complement_full_solve_rows_of_pathSecondPivot_local_rows`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_complement_full_solve_rows_of_pathSecondPivot_local_rows` | Ch11 | **new this session**; composes the second-pivot row classification with the lifted solve-row decomposition, showing that concrete second-pivot local row equations discharge the older arbitrary non-leading/non-endpoint complement-row solve hypothesis for both residual-witness and supported-witness paths. |
| Thm 11.7 second-pivot endpoint solve-row bridge | `higham11_7_ConcretePathSecondPivotLocalSolveRows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_solve_rows` | Ch11 | **new this session**; names the second-pivot local-row handoff and feeds it through the common-roundoff coefficient-sum source endpoint, its uniform-coefficient specialization, and the scalar-budget endpoint with per-branch `u_loc`, replacing the final arbitrary complement-row hypothesis by concrete second-pivot local row equations together with the existing endpoint-local, terminal, and leading/base row bridges. |
| Thm 11.7 second-pivot reduced local-row bridge | `higham11_7_tridiagonalLeadingBlockSupport_row_dot_zero_of_lt`, `higham11_7_ConcretePathSecondPivotReducedSolveRows`, `higham11_7_tridiagonalConcretePathResidualWitnesses_pathSecondPivot_two_current_local_dot_zero`, `higham11_7_tridiagonalConcretePathResidualWitnesses_secondPivot_local_rows_of_reduced_rows`, `higham11_7_tridiagonalConcretePathResidualWitnesses_secondPivot_reduced_rows_of_local_rows`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathSecondPivot_two_current_local_dot_zero`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_secondPivot_local_rows_of_reduced_rows`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_secondPivot_reduced_rows_of_local_rows`, `higham11_7_tridiagonalConcretePathResidualWitnesses_complement_full_solve_rows_of_pathSecondPivot_reduced_rows`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_complement_full_solve_rows_of_pathSecondPivot_reduced_rows` | Ch11 | **new this session**; uses zero-prefix support at offset two to prove that the current local perturbation contributes zero on an accepted `2×2` branch's second-pivot row for both residual and supported path witnesses. The full base-plus-earlier-plus-current local row equation and the reduced base-plus-earlier row equation are now connected in both directions under the path witness support, and the reduced form discharges the old arbitrary complement-row solve obligation directly. |
| Thm 11.7 support-level second-pivot local/reduced bridge | `higham11_7_tridiagonalLeadingBlockSupport_pathSecondPivot_two_current_local_dot_zero`, `higham11_7_ConcretePathSecondPivotLocalSolveRows_of_reduced_rows_of_leadingBlockSupport`, `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_local_rows_of_leadingBlockSupport`, `higham11_7_ConcretePathSecondPivotReducedSolveRows_iff_local_rows_of_leadingBlockSupport` | Ch11 | **new this session**; factors the second-pivot current-local-dot-zero argument through the raw zero-prefix support predicate, independent of residual or supported path witnesses. This gives the remaining accepted-`2×2` solve-row proof a smaller handoff: once branch support is known, the reduced base-plus-earlier row and the full local row are equivalent without unfolding witness tuples. |
| Thm 11.7 local-block second-pivot combined-row adapter | `higham11_7_tridiagonalRowDot_eq_localBlock_rowDot_of_zero_outside`, `higham11_7_tridiagonalPathLocalBlockIndex_not_exists_iff_lt_prefixSpan`, `higham11_7_ConcretePathSecondPivotCombinedLocalBlockSolveRows`, `higham11_7_ConcretePathSecondPivotCombinedRowsZeroOutsideLocalBlock`, `higham11_7_ConcretePathSecondPivotCombinedRowsZeroBeforePrefix`, `higham11_7_ConcretePathSecondPivotCombinedRowsZeroOutsideLocalBlock_of_zeroBeforePrefix`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_zero_outside`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_zeroBeforePrefix` | Ch11 | **new this session**; reindexes a full row dot product to a branch-local block when the full row is zero outside that block, then specializes it to accepted `2×2` second-pivot rows. The branch-local block is proved to be the suffix beginning at the current prefix, so callers may supply a simpler zero-before-prefix condition; the combined `(A + earlier lifted sum)` handoff can now be proved from an explicitly local branch-row equation plus that prefix-zero condition, narrowing the remaining source obligation without assuming the full ambient row equation. |
| Thm 11.7 second-pivot prefix-zero decomposition | `higham11_7_ConcretePathSecondPivotBaseRowsZeroBeforePrefix`, `higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix`, `higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix_of_each`, `higham11_7_ConcretePathSecondPivotCombinedRowsZeroBeforePrefix_of_base_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedRowsZeroBeforePrefix_of_base_and_each_earlier_zero` | Ch11 | **new this session**; splits the combined second-pivot zero-before-prefix obligation into a base-matrix row-zero fact and an earlier-lift row-zero fact, with a pointwise earlier-lift variant that discharges the filtered sum. The remaining concrete path proof can now attack base tridiagonal/pivot zeros and earlier perturbation zeros separately before applying the local-block combined-row adapter. |
| Thm 11.7 decomposed local-block second-pivot adapter | `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_base_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_base_and_each_earlier_zero` | Ch11 | **new this session**; composes the local-block combined row adapter with the base/earlier prefix-zero decomposition. Callers can now supply the branch-local accepted `2×2` second-pivot row equation plus either a summed or pointwise earlier-lift zero proof, and receive the full ambient combined second-pivot handoff consumed by the existing source endpoints. |
| Thm 11.7 tridiagonal base-zero local-block adapter | `higham11_7_ConcretePathSecondPivotBaseRowsZeroBeforePrefix_of_isTridiagonal`, `higham11_7_ConcretePathSecondPivotBaseRowsZeroBeforePrefix_of_isSymTridiagonal`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isTridiagonal_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isTridiagonal_and_each_earlier_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isSymTridiagonal_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isSymTridiagonal_and_each_earlier_zero` | Ch11 | **new this session**; discharges the base-matrix zero-before-prefix side condition from ordinary or symmetric tridiagonality by using that an accepted `2×2` branch's second-pivot row is `prefix+1`; the local-block combined-row adapter now has source-shaped tridiagonal entry points, leaving only the branch-local row equation and earlier-lift prefix zeros for the general second-pivot handoff. |
| Thm 11.7 branch-matrix second-pivot local-block adapter | `higham11_7_ConcretePathSecondPivotBranchMatrixCombinedLocalBlockSolveRows`, `higham11_7_ConcretePathSecondPivotCombinedLocalBlockSolveRows_of_branchMatrix_rows`, `higham11_7_ConcretePathSecondPivotBranchMatrixCombinedLocalBlockSolveRows_of_localBlock_rows`, `higham11_7_ConcretePathSecondPivotBranchMatrixCombinedLocalBlockSolveRows_iff_localBlock_rows`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_rows_of_isTridiagonal_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_rows_of_isTridiagonal_and_each_earlier_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_rows_of_isSymTridiagonal_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_rows_of_isSymTridiagonal_and_each_earlier_zero` | Ch11 | **new this session**; rewrites the remaining accepted `2×2` second-pivot local-block handoff through the concrete branch matrix view `higham11_7_tridiagonalPathBranchMatrix`, proves equivalence with the existing local-block predicate, and composes that branch-matrix row equation with the tridiagonal base-zero adapters. Later callers can prove the row equation against the branch-local matrix API instead of rewriting global `A` indices by hand. |
| Thm 11.7 branch-matrix base-row second-pivot handoff | `higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows`, `higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnCurrentLocalBlock`, `higham11_7_ConcretePathSecondPivotBranchMatrixCombinedLocalBlockSolveRows_of_base_rows_and_earlier_local_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isTridiagonal_and_earlier_local_zero_and_each_earlier_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_local_zero_and_each_earlier_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isTridiagonal_and_earlier_full_row_zero`, and `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero` | Ch11 | **new this session**; separates the branch-matrix combined local-block equation into the bare accepted-`2×2` second-pivot branch row and a pointwise earlier-lift zero-on-current-local-block side condition, then composes those with the existing tridiagonal/symmetric prefix-zero adapters. The full-row-zero variants package one strong earlier-lift zero certificate into both local-block and prefix-zero side conditions for the branch-local row form. This records the remaining solve-side work explicitly and does not derive earlier-lift zeros from ordinary branch support. |
| Thm 11.7 full-base-row to branch-matrix second-pivot bridge | `higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_full_base_rows_of_base_zeroBeforePrefix`, `higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_full_base_rows_of_isTridiagonal`, `higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_full_base_rows_of_isSymTridiagonal` | Ch11 | **new this session**; reuses the generic local-block row-dot restriction to turn a full ambient second-pivot base row equation into the bare branch-matrix local row equation whenever the base row is zero before the branch prefix. The tridiagonal and symmetric-tridiagonal wrappers discharge that prefix-zero side condition, so callers can provide the accepted `2×2` second-pivot equation in the full ambient row form already used by initial-branch endpoints and still feed the branch-matrix handoff. |
| Thm 11.7 full-base-row second-pivot combined handoff | `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_earlier_local_zero_and_each_earlier_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isSymTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, and `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isSymTridiagonal_and_earlier_local_zero_and_each_earlier_zero` | Ch11 | **new this session**; composes the full ambient second-pivot base-row equation with the tridiagonal/symmetric branch-matrix base-row bridge and the explicit local/prefix earlier-lift zero conditions to produce the full combined second-pivot row handoff. This gives callers a source-shaped full-row entry point for non-initial accepted `2×2` branches without assuming the already-combined row equation. |
| Thm 11.7 full-row earlier-lift zero bridge | `higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnFullSecondPivotRow`, `higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnCurrentLocalBlock_of_fullSecondPivotRow`, `higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix_of_fullSecondPivotRow`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_earlier_full_row_zero`, and `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero` | Ch11 | **new this session**; packages one explicit full-row earlier-lift zero certificate into both side conditions required by the full-base-row second-pivot handoff. This does not derive those zeros from ordinary support; it gives the future non-initial accepted-`2×2` row proof a single honest zero-row handoff. |
| Thm 11.7 initial-only second-pivot earlier-lift vacuity | `higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnCurrentLocalBlock_of_two_only_at_zero`, `higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix_of_two_only_at_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isTridiagonal_and_two_only_at_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isSymTridiagonal_and_two_only_at_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_two_only_at_zero`, and `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isSymTridiagonal_and_two_only_at_zero` | Ch11 | **new this session**; when all accepted `2×2` branches occur at path index `0`, the strictly-earlier filtered families are empty. The new lemmas discharge both the local-block earlier-lift zero condition and the prefix-zero sum, then compose them with the branch-matrix and full-base-row bridges. This closes the initial-only second-pivot side-condition route while the general later-branch earlier-lift zero facts remain open. |
| Thm 11.7 global base-solve second-pivot adapters | `higham11_7_ConcretePathSecondPivotFullBaseRows_of_global_base_solve`, `higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_global_base_solve_of_isTridiagonal`, `higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_global_base_solve_of_isSymTridiagonal`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_earlier_local_zero_and_each_earlier_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_earlier_local_zero_and_each_earlier_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_earlier_full_row_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_two_only_at_zero`, and `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_two_only_at_zero` | Ch11 | **new this session**; converts a source-shaped global base solve equation `A*x_hat=b` into the accepted-`2×2` second-pivot full-row obligations, the branch-matrix local row handoff, and the existing tridiagonal/symmetric combined-row routes. This removes a caller-side row-family specialization step while still leaving the genuine non-initial earlier-lift zero certificates explicit. |
| Thm 11.7 global base-solve source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve`, and `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve` | Ch11 | **new this session**; lifts the global base-solve route to the coefficient-sum, uniform-coefficient, and per-branch roundoff source endpoints. Callers can now provide one all-row unperturbed solve equation plus the existing tridiagonal and earlier-lift zero side conditions instead of first specializing the accepted-`2×2` second-pivot full-row family. |
| Thm 11.7 global base-solve/pointwise-prefix source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_each_earlier_zero`, and `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_each_earlier_zero` | Ch11 | **new this session**; combines the source-shaped global base solve equation with pointwise earlier-lift zero-before-prefix facts for the coefficient-sum, uniform-coefficient, and per-branch roundoff source endpoints, including symmetric-tridiagonal source forms. This removes the caller-side full-base-row extraction, tridiagonal projection, and summed-prefix packaging steps while still leaving the genuine pointwise earlier-lift zero facts explicit. |
| Thm 11.7 global base-solve/full-row earlier-lift source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_earlier_full_row_zero`, and `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero` | Ch11 | **new this session**; combines the source-shaped global base solve equation with the single full-row earlier-lift zero certificate for the coefficient-sum, uniform-coefficient, and per-branch roundoff source endpoints, including symmetric-tridiagonal wrappers. This removes separate caller-side specialization of the base row family and separate packaging of full-row zero into local/prefix side conditions, while still leaving the genuine full-row earlier-lift zero certificate explicit. |
| Thm 11.7 reduced second-pivot combined-row adapter | `higham11_7_row_dot_add_filtered_family_sum_split`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows`, `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_combined_rows`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_reduced_rows`, `higham11_7_ConcretePathSecondPivotReducedSolveRows_iff_combined_rows` | Ch11 | **new this session**; names the equivalent combined `(A + earlier lifted sum)` form of the reduced second-pivot handoff and proves both directions with a filtered finite-family row-dot splitter. This lets later callers discharge the remaining second-pivot obligation from a single combined row equation instead of matching the split `A`-dot plus earlier-dot normal form. |
| Thm 11.7 combined-row second-pivot witness bridges | `higham11_7_tridiagonalConcretePathResidualWitnesses_secondPivot_local_rows_of_combined_rows`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_secondPivot_local_rows_of_combined_rows`, `higham11_7_tridiagonalConcretePathResidualWitnesses_complement_full_solve_rows_of_pathSecondPivot_combined_rows`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_complement_full_solve_rows_of_pathSecondPivot_combined_rows` | Ch11 | **new this session**; threads the combined reduced second-pivot row equation directly through residual-witness and supported-witness paths, yielding both the full local second-pivot handoff and the old non-leading/non-endpoint complement-row solve obligation without exposing the split normal form. |
| Thm 11.7 combined-row second-pivot source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_combined_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_combined_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_combined_solve_rows` | Ch11 | **new this session**; threads the combined second-pivot row handoff through the coefficient-sum, uniform-coefficient, and scalar-budget concrete prefix-span source endpoints by reducing to the already-proved reduced-row endpoints. This lets callers use the single combined `(A + earlier lifted sum)` row equation at accepted `2×2` second-pivot rows without manually invoking the reduced-row adapter. |
| Thm 11.7 decomposed branch-matrix second-pivot source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_earlier_full_row_zero`, and `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero` | Ch11 | **new this session**; pushes the branch-matrix base-row decomposition all the way to the coefficient-sum, uniform-coefficient, and scalar-budget source endpoints. Callers may now provide tridiagonality, a bare branch-matrix accepted-`2×2` second-pivot row equation, and explicit earlier-lift zero side conditions instead of manufacturing the already-combined second-pivot row handoff; the full-row-zero variants package one strong earlier-lift row-zero certificate into the two earlier-lift side conditions across all three budget forms while keeping that certificate explicit. |
| Thm 11.7 full-base-row second-pivot coefficient endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows` | Ch11 | **new this session**; composes the decomposed branch-matrix coefficient-sum endpoint with the full ambient row-to-branch-matrix base-row bridge. Callers can now supply accepted `2×2` second-pivot base solve equations in the full ambient row form while still keeping the explicit earlier-lift local and prefix-zero hypotheses visible. |
| Thm 11.7 full-base-row second-pivot uniform/scalar endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows` | Ch11 | **new this session**; adds the constant-coefficient and per-branch roundoff-budget full-row variants by composing the branch-matrix endpoints with the tridiagonal full-row-to-branch-matrix base-row bridge. This exposes the same source-shaped accepted `2×2` second-pivot base equations for uniform and scalar budgets without hiding the earlier-lift zero side conditions. |
| Thm 11.7 symmetric full-base-row second-pivot endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal` | Ch11 | **new this session**; exposes the coefficient-sum, uniform-coefficient, and scalar-budget full ambient second-pivot endpoint adapters with the source-shaped symmetric-tridiagonal matrix hypothesis, projecting it internally to the tridiagonal support condition while retaining the explicit second-pivot base-row and earlier-lift zero obligations. |
| Thm 11.7 pointwise-prefix full-base-row second-pivot endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_each_earlier_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_each_earlier_zero`, and `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_each_earlier_zero` | Ch11 | **new this session**; adds coefficient-sum, uniform-coefficient, and scalar-budget wrappers that accept pointwise earlier-lift zero-before-prefix facts and package them through `higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix_of_each` before applying the existing full-base-row endpoints. This removes a caller-side summed-prefix packaging step but still leaves the genuine earlier-lift zero facts as explicit hypotheses. |
| Thm 11.7 full-row earlier-lift coefficient endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero` | Ch11 | **new this session**; threads the single full-row earlier-lift zero certificate through the coefficient-sum full-base-row source endpoint, deriving both the local-block and prefix-zero side conditions internally. This narrows the non-initial accepted-`2×2` handoff without claiming the row-zero certificate is automatic. |
| Thm 11.7 full-row earlier-lift uniform/scalar endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_earlier_full_row_zero`, and `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero` | Ch11 | **new this session**; extends the single full-row earlier-lift zero certificate route to the constant-coefficient and per-branch roundoff-budget full-base-row source endpoints, deriving the local-block and prefix-zero side conditions internally while keeping the row-zero certificate explicit. |
| Thm 11.7 symmetric initial-only full-base-row source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_two_only_at_zero`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_two_only_at_zero`, and `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_two_only_at_zero` | Ch11 | **new this session**; source-shaped symmetric-tridiagonal wrappers for the initial-only full-base-row route, covering coefficient-sum, uniform-coefficient, and per-branch roundoff budgets without requiring callers to project `IsSymTridiagonal` to `IsTridiagonal` by hand. |
| Thm 11.7 combined-row second-pivot special cases | `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_no_two`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_all_one`, `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_base_rows_of_two_only_at_zero` | Ch11 | **new this session**; mirrors the reduced-row vacuity and initial-branch base-row routes for the combined second-pivot handoff, so no-`2×2`, all-`1×1`, and initial-only `2×2` paths can use the combined API directly. |
| Thm 11.7 initial second-pivot reduced-row bridge | `higham11_7_fin_sum_before_eq_zero_of_val_zero`, `higham11_7_fin_before_dot_eq_zero_of_val_zero`, `higham11_7_ConcretePathSecondPivotReducedSolveRow_of_val_zero`, `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_base_rows_of_two_only_at_zero` | Ch11 | **new this session**; proves that the strict-before lifted perturbation sum is empty at a branch whose path value is `0`, so an initial accepted `2×2` branch's reduced second-pivot row follows from the unperturbed base row equation. The predicate wrapper packages the case where every accepted `2×2` branch is the initial branch. |
| Thm 11.7 initial second-pivot coefficient endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_initial_secondPivot_base_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_initial_secondPivot_base_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_initial_secondPivot_base_rows` | Ch11 | **new this session**; threads the initial-second-pivot reduced-row bridge through the coefficient-sum, uniform-coefficient, and scalar-budget concrete prefix-span residual-witness endpoints. If every accepted `2×2` branch has path value `0`, callers can discharge the reduced second-pivot handoff using only the corresponding unperturbed base row equations. |
| Thm 11.7 reduced second-pivot source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_reduced_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_reduced_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_reduced_solve_rows` | Ch11 | **new this session**; threads the reduced second-pivot row assumption through the coefficient-sum, uniform-coefficient, and scalar-budget concrete prefix-span source endpoints, so these endpoints no longer require the branch-current local dot term. The remaining 11.7 solve-side handoff is the reduced base-plus-earlier second-pivot row equation itself. |
| Thm 11.7 no-second-pivot path row vacuity | `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_no_two`, `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_all_one`, `higham11_7_tridiagonalPath_no_secondPivot_of_all_one`, `higham11_7_tridiagonalPath_all_one_of_no_secondPivot`, `higham11_7_tridiagonalPath_no_secondPivot_iff_all_one`, `higham11_7_tridiagonalPath_complement_full_solve_rows_of_no_secondPivot`, `higham11_7_tridiagonalPath_complement_full_solve_rows_of_all_one` | Ch11 | **new this session**; proves that the reduced second-pivot handoff and non-leading/non-first-trailing complement solve rows are vacuous when the concrete mixed path has no accepted `2×2` branch, and packages the exact all-`1×1` row-coverage subcase through explicit adapters in both directions between no-second-pivot paths and all-`1×1` paths. |
| Thm 11.7 no-second-pivot source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_no_secondPivot`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_no_secondPivot`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_no_secondPivot` | Ch11 | **new this session**; feeds the no-`2×2` row-vacuity lemmas into the coefficient-sum, uniform-coefficient, and scalar-budget concrete prefix-span endpoints. In an all-`1×1` path, callers now supply only the nonfinal/final `1×1` first-trailing solve rows plus the leading base row; all `2×2` first-trailing and second-pivot obligations are discharged by contradiction. |
| Thm 11.7 all-`1×1` source endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_all_one`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_all_one`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_all_one` | Ch11 | **new this session**; exposes the all-`1×1` concrete prefix-span residual-witness endpoints directly in coefficient-sum, uniform-coefficient, and scalar-budget forms by deriving the no-second-pivot hypothesis from the all-one path proof. This removes the negative `2×2` branch precondition from source-facing callers in the all-`1×1` subcase. |
| Thm 11.7 terminal/leading row separation | `higham11_7_tridiagonalPath_finLast_ne_zero`, `higham11_7_tridiagonalPath_zero_ne_finLast` | Ch11 | **new this session**; proves that the ambient last row of a nonempty concrete path is distinct from the leading row, using the final first-trailing endpoint identification. This keeps the terminal-tail row and the leading-row complement case disjoint in the remaining lifted solve-equation split. |
| Thm 11.7 concrete lifted solve-row splitter | `higham11_7_tridiagonalPath_solve_rows_of_one_two_nonfinal_firstTrailingIndex_last_zero_and_complement`, `higham11_7_tridiagonalPath_solve_rows_of_one_two_nonfinal_firstTrailingIndex_last_zero_secondPivot` | Ch11 | **new this session**; specializes the generic row-coverage split to the actual lifted equation for `A + ∑ ΔA_lift`, so the remaining final `hsolve` can be supplied as non-final `1×1`/`2×2` endpoint rows, the terminal last row, the leading row, and either arbitrary non-leading/non-endpoint complement rows or the refined concrete `2×2` second-pivot rows. |
| Thm 11.7 entrywise infinity-norm bridge | `higham11_7_abs_entry_le_infNorm` | Ch11 | **new this session**; row-sum bridge showing every entry satisfies `|Aᵢⱼ| ≤ ‖A‖∞`, used to discharge local scalar `Amax` hypotheses from a norm budget |
| Thm 11.7 componentwise-to-infinity-norm bridge | `higham11_7_infNorm_le_card_mul_of_uniform_componentwise_bound`, `higham11_7_infNorm_le_card_mul_of_printed_componentwise_bound` | Ch11 | **new this session**; aggregates a uniform componentwise perturbation budget to an infinity-norm bound by row sums, with the printed `c*u*Amax` form exposed for the final normwise theorem |
| Thm 11.7 solve-side norm-bound packaging | `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_with_norm_bounds`, `higham11_7_tridiagonal_backward_error_interface_of_solve_delta_infNorm_with_norm_bounds`, `higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_sum_solve_delta_infNorm_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_uniform_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets`, `higham11_7_tridiagonal_backward_error_interface_of_supported_sum_solve_delta_infNorm_of_le_offsets_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_supported_uniform_sum_solve_delta_infNorm_of_le_offsets` | Ch11 | **new this session**; carries the recursive solve perturbation through the source-facing interface while also recording `‖ΔA₁‖∞` and `‖ΔA₂‖∞` bounds obtained from the componentwise budget, including the direct `Amax = ‖A‖∞` specialization; the finite sum bridges collapse already-embedded residual matrices without support hypotheses, including coefficient-majorant and uniform-coefficient variants, while the finite supported-sum bridges additionally preserve same-ambient support, including mixed-offset families, under printed coefficient budgets and then feed the result into the solve-side interface, with coefficient-majorant variants replacing `Σc_t` by a supplied printed constant `C` and uniform-coefficient variants exposing the common `k*c*u‖A‖∞` budget |
| Thm 11.7 embedded path solve-side aggregation | `higham11_7_TridiagonalBranchPathSupportedWitnesses`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_embedded_sum`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_embedded_sum_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_embedded_sum_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_embedded_sum_of_coeff_sum_le` | Ch11 | **new this session**; extracts the finite path-local residual witnesses, accepts an explicit same-ambient embedding with support/budget preservation plus the final summed solve equation, and feeds that data into the supported solve-delta source interface. The local-assumption and terminal-tail wrappers compose the branch/path adapters before extraction. This does not close Theorem 11.7 yet; the concrete full pivot path still has to provide the embedding data and summed solve equation. |
| Thm 11.7 local-to-ambient path lift | `higham11_7_tridiagonalLocalBlockIndex`, `higham11_7_tridiagonalLocalBlockIndex_val`, `higham11_7_tridiagonalLocalBlockIndex_injective`, `higham11_7_tridiagonalLocalBlockIndex_val_exists_iff`, `higham11_7_tridiagonalLocalBlockIndex_mem_range_iff`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_embedded_row_dot_eq_local`, `higham11_7_tridiagonalPathLocalBlockIndex_one_lt_pivotSpan_succ`, `higham11_7_tridiagonalPathLocalBlockIndex_two_lt_pivotSpan_succ`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_current_rows_dot_eq_local`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_current_rows_dot_eq_local`, `higham11_7_tridiagonalLiftLocalBlockPerturbation`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_embedded`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_row_lt_start`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_col_lt_start`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_start_add_dim_le_row`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_start_add_dim_le_col`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_row_lt_start_add_offset`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_col_lt_start_add_offset`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_one_row_of_lt`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_two_row_of_lt`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_one_col_of_lt`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_two_col_of_lt`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_later_rows_sum_zero`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_later_rows_sum_zero`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_later_cols_sum_zero`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_later_cols_sum_zero`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_later_rows_dot_sum_zero`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_later_rows_dot_sum_zero`, `higham11_7_fin_sum_eq_prefix_add_later`, `higham11_7_fin_sum_prefix_eq_before_add_current`, `higham11_7_fin_prefix_dot_eq_before_add_current`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_prefix_sum`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_prefix_sum`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_prefix_rows_dot_eq_before_add_current`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_prefix_rows_dot_eq_before_add_current`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_before_add_current`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_before_add_current`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_before_dot_add_current_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_before_dot_add_current_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_before_dot_add_current_pathLocal_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_before_dot_add_current_pathLocal_dot`, `higham11_7_row_dot_add_family_sum_split`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_solve_row_eq_A_dot_add_before_dot_add_current_pathLocal_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_solve_row_eq_A_dot_add_before_dot_add_current_pathLocal_dot`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalConcretePathResidualWitnesses_pathFirstTrailing_one_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalConcretePathResidualWitnesses_pathFirstTrailing_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathFirstTrailing_one_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathFirstTrailing_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, `higham11_7_tridiagonalPath_solve_rows_of_firstTrailingIndex_rows_and_complement`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_bound`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_leadingBlockSupport`, `higham11_7_tridiagonalLiftLocalBlockPerturbation_bound_leadingBlockSupport`, `higham11_7_tridiagonalBranchPathSupportedWitnesses_lift_to_ambient`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_of_coeff_sum_le` | Ch11 | **new this session**; gives the concrete same-ambient lift used by the embedded path bridge: a local branch perturbation is placed at a supplied row/column start offset, zero-filled elsewhere, retains its componentwise bound, shifts zero-prefix support by the start offset, agrees on embedded local entries, and now has direct zero lemmas for rows/columns outside the embedded block and for shifted leading-block rows/columns. The generic local block range and injectivity lemmas identify the embedded half-open interval `[start,start+m)`, the embedded row-dot lemma reindexes an ambient lifted row dot product back to the original local branch row dot product, and the path-specialized current-row endpoints do this directly for `1×1` and `2×2` first-trailing rows. The path-specialized row/column lemmas show a later branch lift vanishes on an earlier branch's first-trailing row or column, the filtered finite-sum variants eliminate all later-branch contributions at once, and the row dot-product variants eliminate the corresponding later-branch matrix-vector contribution. The prefix-sum decompositions rewrite the all-branch dot product at a first-trailing row to the prefix-only dot product, then split that prefix into earlier branches plus the current branch; composed endpoints expose that final before-plus-current form directly, the path-local current-family endpoints remove dependent casts from the current branch dot product, the solve-row split adds the base `A` row dot product, the residual-equation endpoints turn that separated path-local row equation back into the full ambient solve-row equation, and the supported/residual-witness variants derive the needed support family from the concrete path witness automatically. The solve-row coverage splitter reduces the remaining monolithic lifted `∀ i` equation to first-trailing endpoint rows plus their complement. The lifted-sum source wrapper uses this explicit lift directly, leaving only the scalar budget comparisons and final lifted solve equation for the concrete mixed pivot path. |
| Thm 11.7 terminal branch last-row bridge | `higham11_7_tridiagonalConcretePathResidualWitnesses_finLast_full_solve_row_of_last_pathLocal_rows`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_finLast_full_solve_row_of_last_pathLocal_rows` | Ch11 | **new this session**; case-splits the final branch size and rewrites the final first-trailing path index to `Fin.last`, turning either terminal `1×1` or terminal `2×2` path-local solve row into the full lifted ambient last-row equation. The supported-witness variant gives the same endpoint bridge to callers that only need support/budget data and supply the terminal row equation directly. |
| Thm 11.7 leading row lift-zero bridge | `higham11_7_tridiagonalConcretePathResidualWitnesses_zero_full_solve_row_of_base_row`, `higham11_7_tridiagonalConcretePathSupportedWitnesses_zero_full_solve_row_of_base_row` | Ch11 | **new this session**; uses the witness zero-prefix support family and positive branch offsets to show every lifted branch perturbation vanishes on ambient row `0`, reducing the leading lifted solve row to the unperturbed base row equation. The supported-witness variant mirrors the residual bridge without requiring equation-bearing branch witnesses. |
| Thm 11.7 local-to-global path budget comparisons | `higham11_7_tridiagonal_local_budget_le_global_of_coeff_roundoff_norm`, `higham11_7_tridiagonalBranchPath_local_budgets_le_global_of_coeff_roundoff_norm` | Ch11 | **new this session**; converts pointwise coefficient, roundoff, and local matrix norm comparisons into the exact budget hypothesis required by the lifted path solve aggregation theorem, i.e. `(c_bound+c_rec)u_loc‖A_loc‖∞ ≤ c_t u ‖A‖∞` for every branch. |
| Thm 11.7 path coefficient majorants | `higham11_7_tridiagonalBranchPath_uniform_coeff_majorant_of_component_bounds`, `higham11_7_tridiagonalBranchPath_uniform_coeff_add_majorant_of_component_bounds` | Ch11 | **new this session**; derives the endpoint's pointwise coefficient domination `c_bound t + c_rec t ≤ c` from uniform caps on the local-step and recursive-tail coefficient components, including the direct additive cap case. |
| Thm 11.7 lifted zero-offset path endpoints | `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le` | Ch11 | **new this session**; specializes the lifted path solve aggregation to common support offset `0`, removing the routine offset-lowering proof, and exposes local-assumption and terminal-tail entry points that match the concrete mixed-pivot path construction. The residual-witness variants extract equation-bearing branch witnesses and ask the final solve equation only for those witnesses, while using their supported projection for aggregation. The scheduled variants choose an existing zero-based start-offset schedule internally, including equation-bearing scheduled variants, leaving the lifted solve equation as the path-specific handoff. |
| Thm 11.7 lifted zero-offset scalar-budget endpoints | `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm` | Ch11 | **new this session**; composes the zero-offset lifted source endpoints with the path budget-comparison lemma, so a concrete pivot path can discharge budgets by supplying nonnegativity, coefficient domination, roundoff domination, and local-to-global matrix norm domination. The residual-witness variants keep the final solve-equation handoff equation-bearing while absorbing those scalar budget comparisons. The scheduled variants use the proved start-offset existence theorem, so callers provide the lifted solve equation only for scheduled starts; the scheduled residual-witness variants combine that schedule choice with the scalar budget comparisons. |
| Thm 11.7 mixed-path start-offset schedule | `higham11_7_tridiagonalBranchSupportOffset_pos`, `higham11_7_tridiagonalBranchSupportOffset_le_two`, `higham11_7_tridiagonalPathPivotSpan`, `higham11_7_tridiagonalPathPivotSpan_zero`, `higham11_7_tridiagonalPathPivotSpan_cons`, `higham11_7_tridiagonalPathPivotSpan_pos`, `higham11_7_tridiagonalPathPivotSpan_ge_length`, `higham11_7_tridiagonalPathPivotSpan_le_two_mul`, `higham11_7_TridiagonalPathStartOffsetsFrom`, `higham11_7_TridiagonalPathStartOffsets`, `higham11_7_tridiagonalPathStartOffsetsFrom_head`, `higham11_7_tridiagonalPathStartOffsetsFrom_succ`, `higham11_7_tridiagonalPathStartOffsetsFrom_succ_lt`, `higham11_7_tridiagonalPathStartOffsetsFrom_cons`, `higham11_7_tridiagonalPathStartOffsetsFrom_tail`, `higham11_7_tridiagonalPathStartOffsetsFrom_iff_head_tail`, `higham11_7_tridiagonalPathStartOffsetsFrom_exists`, `higham11_7_tridiagonalPathStartOffsetsFrom_base_le`, `higham11_7_tridiagonalPathStartOffsetsFrom_lt_base_add_pivotSpan`, `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_base_add_pivotSpan`, `higham11_7_tridiagonalPathStartOffsetsFrom_last_branch_end_eq`, `higham11_7_tridiagonalPathStartOffsets_head`, `higham11_7_tridiagonalPathStartOffsets_succ`, `higham11_7_tridiagonalPathStartOffsets_succ_lt`, `higham11_7_tridiagonalPathStartOffsets_tail`, `higham11_7_tridiagonalPathStartOffsets_iff_head_tail`, `higham11_7_tridiagonalPathStartOffsets_exists`, `higham11_7_tridiagonalPathStartOffsets_lt_pivotSpan`, `higham11_7_tridiagonalPathStartOffsets_branch_end_le_pivotSpan`, `higham11_7_tridiagonalPathStartOffsets_last_branch_end_eq` | Ch11 | **new this session**; defines the concrete offset recurrence for a mixed `1×1`/`2×2` tridiagonal pivot path, with branch span bounds, zero/cons/positive/lower/upper pivot-span lemmas, a base-offset variant, zero-based specialization, existence theorems, head/successor/tail projections, strict successor growth from positive branch spans, start-offset total-span bounds, branch-end containment bounds, last-branch endpoint equalities, cons constructors, and head-tail iff lemmas that make nonempty schedules composable by induction. |
| Thm 11.7 mixed-path schedule ordering | `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_of_lt`, `higham11_7_tridiagonalPathStartOffsetsFrom_lt_of_lt`, `higham11_7_tridiagonalPathStartOffsets_branch_end_le_of_lt`, `higham11_7_tridiagonalPathStartOffsets_lt_of_lt` | Ch11 | **new this session**; proves any earlier scheduled branch consumes its pivot block before any later branch starts, and that scheduled starts are strictly ordered by path index. |
| Thm 11.7 mixed-path schedule monotonicity | `higham11_7_tridiagonalPathStartOffsetsFrom_le_of_le`, `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_branch_end_of_le`, `higham11_7_tridiagonalPathStartOffsets_le_of_le`, `higham11_7_tridiagonalPathStartOffsets_branch_end_le_branch_end_of_le` | Ch11 | **new this session**; packages monotonicity of scheduled starts and consumed-branch endpoints for base-offset and zero-based mixed tridiagonal paths. |
| Thm 11.7 mixed-path schedule uniqueness | `higham11_7_tridiagonalPathStartOffsetsFrom_unique`, `higham11_7_tridiagonalPathStartOffsetsFrom_exists_unique`, `higham11_7_tridiagonalPathStartOffsets_unique`, `higham11_7_tridiagonalPathStartOffsets_exists_unique` | Ch11 | **new this session**; proves the base-offset and zero-based mixed-path start schedules are unique, and packages existence plus uniqueness for canonical schedule handoffs. |
| Thm 11.7 mixed-path schedule prefix spans | `higham11_7_tridiagonalPathPrefixSpan`, `higham11_7_tridiagonalPathPrefixSpan_zero`, `higham11_7_tridiagonalPathPrefixSpan_succ`, `higham11_7_tridiagonalPathStartOffsetsFrom_eq_base_add_prefixSpan`, `higham11_7_tridiagonalPathStartOffsetsFrom_base_add_prefixSpan`, `higham11_7_tridiagonalPathStartOffsets_eq_prefixSpan`, `higham11_7_tridiagonalPathStartOffsets_prefixSpan`, `higham11_7_tridiagonalPathPrefixSpan_last_add_branch_eq_pivotSpan` | Ch11 | **new this session**; identifies each scheduled branch start with the base plus the sum of earlier consumed pivot spans, proves the explicit prefix-span starts themselves are the canonical base-offset/zero-based schedules, and identifies the last explicit prefix endpoint with the full path span. |
| Thm 11.7 mixed-path prefix-span bounds and ordering | `higham11_7_tridiagonalPathPrefixSpan_lt_pivotSpan`, `higham11_7_tridiagonalPathPrefixSpan_branch_end_le_pivotSpan`, `higham11_7_tridiagonalPathPrefixSpan_branch_end_le_of_lt`, `higham11_7_tridiagonalPathPrefixSpan_lt_of_lt`, `higham11_7_tridiagonalPathPrefixSpan_le_of_le`, `higham11_7_tridiagonalPathPrefixSpan_branch_end_le_branch_end_of_le`, `higham11_7_tridiagonalPathPrefixSpan_branch_end_lt_branch_end_of_lt` | Ch11 | **new this session**; transfers containment, strict start ordering, monotone endpoint facts, and strict endpoint ordering from canonical schedules to explicit prefix spans, so later lifted-entry arguments can avoid carrying a separate `starts` witness. |
| Thm 11.7 concrete mixed-path tail dimensions | `higham11_7_tridiagonalPathTailDim`, `higham11_7_tridiagonalBranchAmbientDim_eq_tail_add_offset_succ`, `higham11_7_tridiagonalPathPrefixSpan_add_branchAmbientDim_tailDim_eq_pivotSpan_succ`, `higham11_7_tridiagonalPath_local_index_lt_pivotSpan_succ`, `higham11_7_tridiagonalPathLocalBlockIndex`, `higham11_7_tridiagonalPathLocalBlockIndex_val`, `higham11_7_tridiagonalPathTailDim_last_eq_zero`, `higham11_7_tridiagonalPathTailDim_head`, `higham11_7_tridiagonalPathTailDim_succ` | Ch11 | **new this session**; defines the remaining tail dimension after each concrete mixed-path branch, proves the branch-local block fits in the full `pathSpan+1` ambient at the prefix offset, exposes a path-local index embedding, proves the terminal branch has zero remaining tail, and gives the head/successor recurrence needed by path induction. |
| Thm 11.7 concrete mixed-path branch matrix view | `higham11_7_tridiagonalPathBranchMatrix`, `higham11_7_tridiagonalPathBranchMatrix_apply`, `higham11_7_tridiagonalPathLocalBlockIndex_injective`, `higham11_7_tridiagonalPathBranchMatrix_abs_entry_le_infNorm`, `higham11_7_tridiagonalPathBranchMatrix_infNorm_le_card_mul_global_infNorm`, `higham11_7_tridiagonalPathBranchMatrix_infNorm_le_global_infNorm` | Ch11 | **new this session**; restricts a full `pathSpan+1` ambient tridiagonal matrix to each branch-local block at its explicit prefix offset, proves local entries are bounded by the global `∞` norm, gives a coarse local-row-length norm bound for coefficient-absorbing budget routes, and proves the sharper principal-block `∞`-norm comparison needed by the concrete path endpoint. |
| Thm 11.7 concrete scheduled mixed-path endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm` | Ch11 | **new this session**; specializes the scheduled lifted path source endpoint to the canonical `pathSpan+1` ambient matrix, concrete tail dimensions, and prefix-offset branch matrices, discharging the local matrix-norm comparison via the principal-block bound while keeping the genuine path-local assumptions, coefficient/roundoff comparisons, and lifted solve equation explicit. |
| Thm 11.7 concrete prefix-span mixed-path endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_coeff_roundoff_norm` | Ch11 | **new this session**; replaces the arbitrary valid start schedule in the concrete full-ambient endpoint by the canonical prefix-span starts, using schedule uniqueness so the remaining solve equation is stated directly over the concrete path offsets. |
| Thm 11.7 concrete residual-witness mixed-path endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm` | Ch11 | **new this session**; specializes the residual-witness scheduled scalar-budget endpoints to the concrete `pathSpan+1` ambient matrix and then to canonical prefix-span starts, so the final lifted solve equation can be stated over equation-bearing path residual witnesses rather than arbitrary supported witnesses. |
| Thm 11.7 concrete residual-witness uniform endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm` | Ch11 | **new this session**; specializes the concrete residual-witness prefix endpoints to common roundoff, common coefficient budget `(k : ℝ) * c * u * ‖A‖∞`, and the initial-local/last-terminal path assembly interface. |
| Thm 11.7 concrete split-solve residual-witness endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_split_solve_rows` | Ch11 | **new this session**; composes the initial-local/last-terminal residual-witness uniform endpoint with the concrete row splitter, so callers prove the final lifted solve equation by separate non-final `1×1` endpoint rows, non-final `2×2` endpoint rows, the terminal last row, the leading row, and the non-leading/non-endpoint complement rows. |
| Thm 11.7 concrete scalar-budget split-solve residual-witness endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_split_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_split_solve_rows` | Ch11 | **new this session**; carries the same row-split solve handoff through the per-branch roundoff/coefficient endpoint and the common-roundoff coefficient-sum endpoint, so later mixed-path instantiations can retain nonuniform local budgets or a single unit roundoff while proving separate endpoint, terminal, leading, and complement row equations. |
| Thm 11.7 concrete endpoint-local residual-witness endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_local_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_local_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_local_solve_rows` | Ch11 | **new this session**; composes the split-solve endpoints with the residual-witness path row-lift lemmas, replacing the non-final endpoint full-row obligations by base-row, earlier-lift, and current path-local row equations for the active `1×1` or `2×2` branch in uniform-coefficient, scalar-budget, and coefficient-sum forms. |
| Thm 11.7 concrete terminal/base residual-witness endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_solve_rows`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_solve_rows` | Ch11 | **new this session**; composes the endpoint-local source endpoint with the terminal last-row bridge and leading row lift-zero bridge, so the remaining lifted solve handoff consists of non-final endpoint-local rows, final-branch endpoint-local rows, the unperturbed leading base row, and non-leading/non-endpoint complement rows in uniform-coefficient, scalar-budget, and coefficient-sum forms. |
| Thm 11.7 concrete last-terminal residual-witness nonuniform endpoints | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm` | Ch11 | **new this session**; composes the initial-local/last-terminal path assembly with the residual-witness prefix endpoint while preserving either per-branch roundoff and coefficient vectors or common roundoff with per-branch coefficients. |
| Thm 11.7 concrete prefix-span uniform-roundoff endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_coeff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_coeff_norm` | Ch11 | **new this session**; specializes the concrete prefix-span endpoint to the common unit roundoff `u`, removing the pointwise `u_loc` nonnegativity and domination handoff from both the local-assumption and terminal-tail routes. |
| Thm 11.7 concrete prefix-span uniform-coefficient endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_uniform_coeff_norm`, `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_uniform_coeff_norm` | Ch11 | **new this session**; specializes the concrete prefix-span endpoint to a common per-branch coefficient `c`, replacing the finite coefficient-sum handoff by the direct budget `(k : ℝ) * c * u * ‖A‖∞`. |
| Thm 11.7 concrete prefix-span last-terminal endpoint | `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_uniform_coeff_norm` | Ch11 | **new this session**; composes the last-terminal path assembly theorem with the concrete prefix-span uniform-roundoff/uniform-coefficient endpoint, so callers supply local assumptions for the initial branches and one terminal-tail assumption for the final branch instead of a pre-built path-local assumption. |
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
| §4.2 all-1×1 perturbation norm/scalar aggregation | `higham11_3_infNorm_le_of_componentwise_bound_nonneg`, `higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne_with_norm_bounds`, `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne_with_norm_bounds`, `higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne_of_uniform_envelope_bound`, `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne_of_uniform_envelope_bound` | Ch11 | **new this session**; any nonnegative entrywise all-1×1 envelope now induces the corresponding `∞`-norm perturbation bound, both raw-Schur and stored-symmetric source-facing all-1×1 packages carry those norm bounds for `ΔA₁` and `ΔA₂`, and a scalar envelope majorant `β` now yields componentwise `β` and norm `nβ` budgets directly. This remains an all-1×1-path dependency and does **not** close the mixed-pivot Theorem 11.3 row. |
| Thm 11.3 structured factorization-envelope bridge | `higham11_3_blockLDLTBackwardErrorBound`, `higham11_3_blockLDLTBackwardErrorBound_nonneg`, `higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError`, `higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_with_norm_bounds` | Ch11 | **new this session**; connects the shared `BlockLDLTBackwardError` structure to the Chapter 11 source-facing perturbation-witness interface with the printed first-order envelope `ε·\|L̂\|·\|D̂\|·\|L̂ᵀ\|`, using zero for the solve-side perturbation in this factorization-only bridge. The norm-bound variant also derives `∞`-norm bounds for both perturbation witnesses from the same structured envelope. This improves the interface plumbing but leaves the mixed-pivot floating-point induction and solve equation open. |
| Thm 11.3 printed first-order source envelope bridge | `higham11_3_printedFirstOrderBound`, `higham11_3_printedFirstOrderBound_nonneg`, `higham11_3_blockLDLTBackwardErrorBound_le_printedFirstOrderBound`, `higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_printed_first_order_bound_with_norm_bounds` | Ch11 | **new this session**; names the source first-order `(11.5)` envelope `p u (|A|+|L̂||D̂||L̂ᵀ|)` in permuted coordinates, proves its nonnegativity, shows the structured `ε|L̂||D̂||L̂ᵀ|` envelope is dominated when `ε≤pu`, and packages `BlockLDLTBackwardError` witnesses with componentwise and `∞`-norm bounds against that printed envelope. This still leaves the mixed-pivot fl induction and the higher-order term unmodeled. |
| Thm 11.3 structured product-entry/max-entry bridges | `higham11_3_blockLDLTBackwardErrorBound_eq_epsilon_mul_productEntry`, `higham11_3_blockLDLTBackwardErrorBound_le_of_productEntry_le`, `higham11_3_blockLDLTBackwardErrorBound_le_epsilon_mul_productMax`, `higham11_3_blockLDLTBackwardErrorBound_le_epsilon_mul_maxEntryNorm_absLDLTProduct`, `higham11_3_blockLDLTBackwardErrorBound_le_epsilon_mul_higham_product_bound`, `higham11_3_blockLDLTBackwardErrorBound_le_pu_higham_product_bound`, `higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_higham_product_bound`, `higham11_3_infNorm_le_card_mul_of_uniform_componentwise_bound`, `higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_higham_product_bound_with_norm_bounds`, `higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_pu_higham_product_bound_with_norm_bounds` | Ch11 | **new this session**; identifies the structured 11.3 envelope as `ε` times the existing `|L̂||D̂||L̂ᵀ|` product-entry API and transports product-entry, product-max, max-entry-norm, and Higham-style product-max bounds to the envelope. The final consumers combine a `BlockLDLTBackwardError` certificate with a Higham product-max bound to produce Chapter 11 perturbation witnesses with the corresponding scalar product budget, including induced `∞`-norm bounds in the norm variant; the source-scale variant additionally consumes `ε≤p*u` and yields the direct printed-scale scalar budget `(p*u)*(36*n*ρₙ*Amax)`. This is a normalization bridge toward the printed `p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)` form, not the remaining mixed-pivot induction. |
| §11.1 exact block-LDLᵀ step, eq (11.3) `s=1`: `∑ L·D·Lᵀ = A` | `oneByOne_step_factorization`, `higham11_3_oneByOne_step_factorization` | " | **new this session**; exact 1×1-pivot factorization identity (unit-lower-tri `L`, block-diag `D` with Schur complement) — the **exact base of Theorem 11.3's diagonal-pivoting recursion** (fl version adds `fl_oneByOne_schur_step_error`) |
| §11.1 exact block-LDLᵀ **inductive step**, eq (11.1)/(11.3) | `blockLDLT_assemble_step`, `higham11_3_blockLDLT_assemble_step` | " | **new this session**; trailing block factorized recursively (`L_S·D_S·L_Sᵀ = S`, IH) + 1×1 multipliers ⇒ assembled `∑ L·D·Lᵀ = A`; iterating gives the exact `PAPᵀ = LDLᵀ` recursion |
| §11.1 exact **full recursion**, eq (11.1)/(11.2): `∃ L D, ∑ L·D·Lᵀ = A` | `exact_blockLDLT_all_oneByOne`, `higham11_1_exact_blockLDLT_all_oneByOne` (+ `schurCompl`, `schurCompl_symm`, `AllOnePivots`) | " | **new this session**; symmetric `A` with all Schur-complement pivots nonzero ⇒ exact `LDLᵀ` (no-2×2-pivot case), by induction on `n` via `blockLDLT_assemble_step` — the exact factorization scaffold for Theorem 11.3 |
| Thm 11.4 constant, Higham [608,1997] eq (4.13): `(3+α²)(3+α)/(1−α²)² ≤ 36` | `bunch_kaufman_bound_const_le_36`, `higham11_4_bound_const_le_36`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_absLDLTProduct_entries` | " | **new this session**; the `36` in `‖\|L̂\|\|D̂\|\|L̂ᵀ\|‖_M ≤ 36nρₙ‖A‖_M` (α=(1+√17)/8); the handoff bridges turn pointwise eq-(4.14) estimates with the exact Higham coefficient into both the source-facing `36nρₙ` max-entry norm bound and the scalar max-entry product certificate consumed by the stability/solve wrappers |
| Thm 11.4 constant, Higham [608,1997] (A.3): `(3+α²)/(1−α²) ≤ 6` (`\|E\|\|E⁻¹\|\|E\| ≤ 6\|E\|`) | `bunch_kaufman_pivot_norm_const_le_six`, `higham11_4_pivot_norm_const_le_six` | " | **new this session** |
| §11.1.2 1×1-pivot growth constant `1/α < 2` (Higham [608,1997]) | `bunch_kaufman_recip_alpha_lt_two`, `higham11_4_recip_alpha_lt_two` | " | **new this session**; `g_ij ≤ α⁻¹·max < 2·max` |
| Alg 11.2 Bunch-Kaufman branch tests and 1×1 multiplier caps | `higham11_2_bunch_kaufman_noAction_eq_zero`, `higham11_2_bunch_kaufman_case1_tests`, `higham11_2_bunch_kaufman_case2_tests`, `higham11_2_bunch_kaufman_case3_tests`, `higham11_2_bunch_kaufman_case4_tests`, `higham11_2_bunch_kaufman_case1_pivot_ne_zero`, `higham11_2_bunch_kaufman_case1_multiplier_bound`, `higham11_4_bunch_kaufman_case1_schur_correction_bound`, `higham11_4_bunch_kaufman_case1_schur_growth`, `higham11_2_bunch_kaufman_case2_pivot_ne_zero`, `higham11_4_bunch_kaufman_case2_schur_correction_bound`, `higham11_4_bunch_kaufman_case2_schur_growth`, `higham11_4_bunch_kaufman_case2_pivot_entry_bound`, `higham11_4_bunch_kaufman_case2_pivot_entry_le_Amax`, `higham11_2_bunch_kaufman_case2_pivot_bound_of_row_max_le`, `higham11_2_bunch_kaufman_case2_pivot_ne_zero_of_row_max_le`, `higham11_2_bunch_kaufman_case2_multiplier_bound_of_row_max_le`, `higham11_2_bunch_kaufman_case1_or_case2_pivot_ne_zero_of_row_max_le`, `higham11_2_bunch_kaufman_case1_or_case2_multiplier_bound_of_row_max_le`, `higham11_2_bunch_kaufman_case3_pivot_ne_zero`, `higham11_2_bunch_kaufman_case3_multiplier_bound`, `higham11_4_bunch_kaufman_case3_schur_correction_bound`, `higham11_4_bunch_kaufman_case3_schur_growth` | Ch11 | **new this session**; exposes Algorithm 11.2's branch predicates as source-facing test extractors and proves that the accepted scalar pivot in cases (1) and (3) is nonzero, gives `|c/pivot|≤1/α` for entries bounded by the corresponding `ω` quantity, and yields the source one-step Schur-growth bound under an active-entry majorant. Case-(2) now has direct nonsingularity, correction-bound, Schur-growth, and local `D̂` pivot-entry cap proofs from the printed product test; its stronger scalar multiplier cap remains explicitly conditional on the extra `ωr≤ω1` side condition, and the case-(1)/(2) dispatch bridge packages that conditional shared `a11` scalar-pivot route. This is a local pivot-path ingredient toward the remaining `|L̂|` row-sum/entry caps in Theorem 11.4, not a global product-bound assumption. |
| Alg 11.2 case-(4) `2×2` pivot local bridge | `higham11_4_bunch_kaufman_case4_twoByTwo_absdet_lower`, `higham11_4_bunch_kaufman_case4_twoByTwo_det_ne_zero`, `higham11_4_bunch_kaufman_case4_twoByTwo_inverse_scaled_bounds`, `higham11_4_bunch_kaufman_case4_twoByTwo_schur_correction_bound`, `higham11_4_bunch_kaufman_case4_twoByTwo_schur_growth`, `higham11_4_bunch_kaufman_case4_twoByTwo_multiplier_row_sum_asymmetric_scaled_bound`, `higham11_4_bunch_kaufman_case4_twoByTwo_pivot_entry_bounds`, `higham11_4_bunch_kaufman_case4_twoByTwo_pivot_entries_le_Amax`, `higham11_4_bunch_kaufman_case4_twoByTwo_schur_growth_of_row_max_le`, `higham11_4_bunch_kaufman_case4_twoByTwo_multiplier_row_sum_le_six_of_row_max_le`, `higham11_4_bunch_kaufman_case4_twoByTwo_absdet_lower_of_row_max_le`, `higham11_4_bunch_kaufman_case4_twoByTwo_det_ne_zero_of_row_max_le` | Ch11 | **new this session**; Algorithm 11.2 case-(4)'s printed product tests now directly prove the `2×2` determinant lower bound, nonsingularity, scaled inverse-entry bounds, asymmetric scaled multiplier row-sum bound, natural-scale pivot-entry caps, a local `D̂` cap under stage `Amax` bounds, source correction bound `2ωr/(1−α)`, and one-step Schur-growth estimate `(1+2/(1−α))*Amax` from `|a11*arr|≤α²ω1²` and `|a1r|=ω1`, without a row-maximum dominance side condition. The older source-six `CE⁻¹` row-sum bridge still uses the stronger `ωr≤ω1` side condition to feed the complete-pivot inverse-block API; that hypothesis remains explicit because it is not implied by the bare branch predicate. |
| Thm 11.4 local 2×2 multiplier row caps | `higham11_4_twoByTwo_multiplier_row_bound_of_inverse_entries`, `higham11_4_twoByTwo_multiplier_row_sum_bound_of_inverse_entries`, `higham11_4_twoByTwo_multiplier_row_bound_of_block`, `higham11_4_twoByTwo_multiplier_row_sum_bound_of_block`, `higham11_4_twoByTwo_multiplier_row_sum_const_le_six`, `higham11_4_twoByTwo_multiplier_row_sum_le_six_of_inverse_entries`, `higham11_4_twoByTwo_multiplier_row_sum_le_six_of_block` | Ch11 | **new this session**; converts the printed inverse-entry estimate `|E⁻¹|≤K[[α,1],[1,α]]` with `K=1/((1−α²)μ₀)` into componentwise bounds `|(CE⁻¹)_j|≤1/(1−α)` and row-sum bound `≤2/(1−α)` for a trailing row `C` with entries bounded by the stage maximum `μ₀`, then instantiates the result for the actual symmetric 2×2 pivot block inverse. The source-alpha wrappers prove `2/(1−α)≤6` for `α=(1+√17)/8`, giving the local source-shaped row-sum cap `≤6`. This supplies the local 2×2 counterpart to the Algorithm 11.2 case-(1)/(3) scalar multiplier caps; the all-row pivot-path aggregation remains open. |
| Thm 11.4 max-entry product bridge, Higham [608,1997] eq (4.14) | `higham11_4_bunch_kaufman_stability_of_max_entry_product_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_max_entry_product_bound`, `higham11_4_bunch_kaufman_stability_of_higham_const_absLDLTProduct_entries`, `higham11_4_bunch_kaufman_stability_of_higham_const_product_entries`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_absLDLTProduct_entries`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_product_entries` | Ch11 | **new this session**; turns a scalar max-entry certificate for `\||L̂||D̂||L̂ᵀ|\|_M` into the existing pointwise stability surface, and transports a solve perturbation budget proportional to that product into the advertised `36nρₙ` normwise budget; the exact-coefficient direct wrappers combine the eq-(4.13) constant handoff with the stability and solve consumers, in both matrix-product and expanded double-sum entry notation. This does **not** prove eq (4.14); it makes eq (4.14) the exact next scalar target instead of a pointwise interface hypothesis. |
| Thm 11.4 row-sum stability consumers | `higham11_4_bunch_kaufman_stability_of_higham_const_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_stability_of_higham_const_uniform_entry_bounds`, `higham11_4_bunch_kaufman_stability_of_higham_const_row_sum_bounds` | Ch11 | **new this session**; exact-coefficient row-sum and uniform-entry product caps now feed the pointwise Bunch-Kaufman stability surface directly through the max-entry norm route, while deriving `0≤Dmax` from the nonempty absolute `D̂` entry cap. |
| Thm 11.4 row-sum solve consumers | `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_uniform_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_higham_const_row_sum_bounds` | Ch11 | **new this session**; the same exact-coefficient row-sum and uniform-entry product caps feed the solve-side Bunch-Kaufman normwise perturbation wrapper, converting a solve residual proportional to `‖|L̂||D̂||L̂ᵀ|‖_M` into the advertised `36nρₙ` budget. |
| Thm 11.4 loose row-sum/uniform-entry consumers | `higham11_4_bunch_kaufman_stability_of_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_stability_of_uniform_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_uniform_entry_bounds` | Ch11 | **new this session**; when row-sum or uniform-entry caps are already compared directly to the printed `36nρₙ‖A‖_M` budget, the loose routes now feed both the stability surface and solve-side normwise perturbation wrapper without first exposing an intermediate max-entry proof. |
| Thm 11.4 finite max-entry product norm | `higham11_4_bunchKaufmanProductEntry`, `higham11_4_absLDLTProduct`, `higham11_4_bunchKaufmanProductEntry_eq_absLDLTProduct`, `higham11_4_bunchKaufmanProductEntry_nonneg`, `higham11_4_bunchKaufmanProductMax`, `higham11_4_bunchKaufmanProductEntry_le_productMax`, `higham11_4_absLDLTProduct_entry_le_productMax`, `higham11_4_bunchKaufmanProductMax_nonneg`, `higham11_4_bunchKaufmanProductMax_le_iff`, `higham11_4_bunchKaufmanProductMax_le_iff_absLDLTProduct`, `higham11_4_bunchKaufmanProductMax_eq_maxEntryNorm_absLDLTProduct`, `higham11_4_absLDLTProduct_entry_le_maxEntryNorm`, `higham11_4_maxEntryNorm_absLDLTProduct_le_iff`, `higham11_4_maxEntryNorm_absLDLTProduct_le_iff_product_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_product_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_absLDLTProduct_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_maxEntryNorm_absLDLTProduct`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_absLDLTProduct_entries`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_product_entries`, `higham11_4_bunch_kaufman_stability_of_productMax_le`, `higham11_4_bunch_kaufman_stability_of_maxEntryNorm_absLDLTProduct_le`, `higham11_4_bunch_kaufman_solve_backward_error_of_productMax_le`, `higham11_4_bunch_kaufman_solve_backward_error_of_maxEntryNorm_absLDLTProduct_le` | Ch11 | **new this session**; defines the project matrix product `|L̂||D̂||L̂ᵀ|`, proves it is exactly the expanded double-sum entry form, defines the positive-dimension finite maximum `maxᵢⱼ (|L̂||D̂||L̂ᵀ|)ᵢⱼ`, identifies that finite maximum with the repository `maxEntryNorm` of `|L̂||D̂||L̂ᵀ|`, proves nonnegativity, the least-scalar property, and the direct equivalence between a `maxEntryNorm` bound and pointwise bounds in both expanded and matrix-product notation, packages pointwise/max-entry estimates into the scalar product-bound predicate including the exact Higham-coefficient handoff in both notations, and connects the source eq-(4.14) statement for this finite maximum directly to both the pointwise stability and solve-budget consumers. |
| Thm 11.4 row-sum/product majorant bridge | `higham11_4_bunchKaufmanProductEntry_le_row_sum_bounds`, `higham11_4_bunchKaufmanProductEntry_le_uniform_row_sum_bound`, `higham11_4_abs_row_sum_le_card_mul_of_uniform_entry_bound`, `higham11_4_abs_row_sum_le_card_mul_of_row_entry_bound`, `higham11_4_bunchKaufmanProductEntry_le_uniform_entry_bounds`, `higham11_4_bunchKaufmanProductEntry_le_row_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_row_sum_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_uniform_row_sum_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_uniform_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_row_sum_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_row_sum_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_uniform_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_row_sum_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_higham_const_row_sum_bounds` | Ch11 | **new this session**; proves the algebraic step from absolute-entry bounds on `D̂` plus row-sum bounds on `|L̂|` to the source product entries of `|L̂||D̂||L̂ᵀ|`, and packages the uniform-row, uniform-entry, row-dependent entry, and per-row row-sum versions into the `maxEntryNorm` target and scalar product certificate consumed by the existing 11.4 stability/solve wrappers, including the exact-coefficient route before the proved `≤36` handoff. Uniform `|L̂|≤Lmax` facts supply row sums as `n*Lmax`; row-dependent `|L̂ᵢⱼ|≤Lcapᵢ` facts supply row sums as `n*Lcapᵢ`. This still leaves the pivot-path proof of the required `|L̂|` and `D̂` caps open. |
| Thm 11.4 row-sum first-stage split bridge | `higham11_4_first_stage_recursive_product_split_of_row_sum_bounds`, `higham11_4_product_entries_of_first_stage_recursive_row_sum_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_row_sum_bounds`, `higham11_4_product_entries_of_first_stage_recursive_higham_const_row_sum_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_row_sum_bounds` | Ch11 | **new this session**; region-specific row-sum caps for `|L̂|`, a uniform absolute-entry cap for `D̂`, and first-stage/trailing scalar budget comparisons now produce the exact first-stage/trailing product-entry split consumed by the Higham [608] eqs. (4.11)--(4.14) aggregation, including loose `36` and exact-coefficient max-entry norm endpoints. This narrows the remaining concrete proof to row-sum, `D̂`, and regional scalar estimates along the pivot path. |
| Thm 11.4 row-sum first-stage scalar/consumer bridge | `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_row_sum_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_row_sum_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_row_sum_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_row_sum_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_sum_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_sum_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_sum_maxEntryNorm_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_sum_maxEntryNorm_bounds` | Ch11 | **new this session**; the row-sum/`D̂` first-stage/trailing split now packages directly into the scalar finite-product certificate and into both Bunch-Kaufman stability and solve consumers, for loose `36` shares and Higham's exact coefficient. This removes a caller-side max-entry detour; it does **not** prove the concrete pivot-path row-sum or `D̂` caps. |
| Thm 11.4 uniform row-sum first-stage/recursive adapters | `higham11_4_product_entries_of_first_stage_recursive_uniform_row_sum_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_uniform_row_sum_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_uniform_row_sum_bound`, `higham11_4_product_entries_of_first_stage_recursive_higham_const_uniform_row_sum_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_uniform_row_sum_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_row_sum_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_row_sum_maxEntryNorm_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_row_sum_maxEntryNorm_bound` | Ch11 | **new this session**; specializes the per-row first-stage/trailing split to a single uniform `|L̂|` row-sum cap, feeding product-entry, max-entry norm, scalar certificate, stability, and solve endpoints in both loose `36` and exact Higham-coefficient forms. This is an adapter for the remaining pivot-path proof; it still requires the concrete uniform row-sum cap, `D̂` cap, and regional budget comparisons. |
| Thm 11.4 uniform six-row-sum/growth-`D` first-stage wrappers | `higham11_4_first_stage_recursive_uniform_six_rho_budget`, `higham11_4_product_entries_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_growth_D_maxEntryNorm_bound` | Ch11 | **new this session**; source-shaped consumers for Higham [608] eqs. (4.11)--(4.14) once the remaining pivot-path caps have been proved: a uniform `|L̂|` row-sum cap `≤6` and a growth-scaled `D̂` entry cap `≤ρₙ‖A‖_M` now feed the product-entry, max-entry norm, scalar certificate, stability, and solve routes directly, discharging the loose first-stage/trailing budget arithmetic internally. |
| Thm 11.4 stage-growth `D̂` cap handoff | `higham11_4_growth_scaled_D_bound_of_le`, `higham11_4_product_entries_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_maxEntryNorm_bound` | Ch11 | **new this session**; relaxes a pivot-stage `D̂` entry cap `|D̂ₖₗ|≤ρ_stage‖A‖_M` to the final source growth factor using an explicit `ρ_stage≤ρₙ` certificate, then feeds the same product-entry, max-entry norm, scalar, stability, and solve consumers. This is a real pivot-path handoff for the remaining 11.4 proof and does not assume the growth recursion itself. |
| Thm 11.4 exact-budget uniform row-sum first-stage/recursive adapters | `higham11_4_product_entries_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets_maxEntryNorm` | Ch11 | **new this session**; specializes the exact-coefficient uniform row-sum first-stage/trailing split to the displayed Higham local share and recursive Schur-complement share. The remaining pivot-path proof can target a concrete uniform row-sum product comparison directly, without introducing arbitrary `localB`/`recB` scalar handoffs. |
| Thm 11.4 row-entry first-stage/recursive adapters | `higham11_4_product_entries_of_first_stage_recursive_row_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_row_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_row_entry_bounds`, `higham11_4_product_entries_of_first_stage_recursive_higham_const_row_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_row_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_row_entry_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_row_entry_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_row_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_entry_maxEntryNorm_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_maxEntryNorm_bounds` | Ch11 | **new this session**; derives the first-stage/trailing row-sum caps from row-dependent entry caps `|L̂ᵣₖ|≤Lcap r` as `n*Lcap r`, then feeds product-entry, max-entry norm, scalar certificate, stability, and solve endpoints in loose and exact-coefficient forms. This lets the remaining pivot-path proof use row-local entry estimates from the block bounds without first forcing a global uniform `Lmax`; concrete `L̂`, `D̂`, and regional scalar budget estimates remain open. |
| Thm 11.4 exact-budget row-entry first-stage/recursive adapters | `higham11_4_product_entries_of_first_stage_recursive_higham_const_row_entry_exact_budgets`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_row_entry_exact_budgets`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_row_entry_exact_budgets`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_row_entry_exact_budgets`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_exact_budgets`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_exact_budgets_maxEntryNorm` | Ch11 | **new this session**; specializes the row-dependent entry first-stage/trailing route to the displayed Higham local share and recursive Schur-complement share. This is the direct adapter for pivot-path proofs that naturally produce row-local entry caps rather than a global uniform `Lmax`, while the concrete `L̂`, `D̂`, and regional comparison proofs remain open. |
| Thm 11.4 uniform-entry first-stage/recursive adapters | `higham11_4_product_entries_of_first_stage_recursive_uniform_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_uniform_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_uniform_entry_bounds`, `higham11_4_product_entries_of_first_stage_recursive_higham_const_uniform_entry_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_uniform_entry_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_entry_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_entry_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_uniform_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_entry_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_entry_maxEntryNorm_bound`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_entry_maxEntryNorm_bound` | Ch11 | **new this session**; derives the first-stage/trailing uniform row-sum cap from a uniform entry cap `|L̂ᵢⱼ|≤Lmax` as `n*Lmax`, then feeds the same product-entry, max-entry norm, scalar certificate, stability, and solve endpoints in loose and exact-coefficient forms. This removes another caller-side row-sum handoff; the concrete pivot-path proof still has to supply the uniform `L̂` and `D̂` caps plus regional budget comparisons. |
| Thm 11.4 exact-budget uniform-entry first-stage/recursive adapters | `higham11_4_product_entries_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets_maxEntryNorm` | Ch11 | **new this session**; specializes the exact-coefficient uniform-entry first-stage/trailing split to the displayed Higham local share and recursive Schur-complement share. The remaining pivot-path proof can now target the concrete regional product comparisons directly, without introducing arbitrary `localB`/`recB` scalar handoffs. |
| Thm 11.4 product-entry nonnegativity adapters | `higham11_4_bunchKaufmanProductEntry_le_row_sum_bounds_entry_nonneg`, `higham11_4_bunchKaufmanProductEntry_le_uniform_row_sum_bound_entry_nonneg`, `higham11_4_bunchKaufmanProductEntry_le_uniform_entry_bounds_entry_nonneg`, `higham11_4_bunchKaufmanProductEntry_le_row_entry_bounds_entry_nonneg` | Ch11 | **new this session**; lower-level row-sum, uniform-row, uniform-entry, and row-dependent-entry product-entry adapters now derive `0≤Dmax` from the nonempty absolute `D̂` entry cap, matching the existing scalar and max-entry norm wrappers. |
| Thm 11.4 loose max-entry product cap nonnegativity wrappers | `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_row_sum_bound_entry_nonneg`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_uniform_entry_bounds_entry_nonneg` | Ch11 | **new this session**; the loose `maxEntryNorm` row-sum and uniform-entry routes now derive `0≤Dmax` from the nonempty uniform absolute `D̂` entry cap, matching the loose scalar product-certificate wrappers. |
| Thm 11.4 max-entry product cap nonnegativity wrappers | `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_row_sum_bound_entry_nonneg`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_uniform_entry_bounds_entry_nonneg`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_higham_const_row_sum_bounds_entry_nonneg` | Ch11 | **new this session**; the exact-coefficient max-entry norm routes now derive `0≤Dmax` from the nonempty uniform absolute `D̂` entry cap, matching the scalar product-certificate wrappers and removing a separate positivity handoff for uniform-row, uniform-entry, and per-row row-sum paths. |
| Thm 11.4 first-stage/recursive product aggregation | `higham11_4_first_stage_recursive_product_bound`, `higham11_4_product_entries_of_first_stage_recursive_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_bounds`, `higham11_4_first_stage_recursive_product_bound_of_higham_const`, `higham11_4_product_entries_of_first_stage_recursive_higham_const_bounds`, `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_bounds` | Ch11 | **new this session**; formalizes the scalar handoff implicit in Higham [608, 1997], eqs. (4.11)--(4.14): one local first-stage product share plus a recursive Schur-complement product share bounded by `36(n-s)ρₙ‖A‖_M` fits inside the printed `36nρₙ‖A‖_M` budget, and the resulting entrywise split packages directly into the scalar max-entry product certificate. The exact-coefficient variants let callers supply Higham's `(3+α²)(3+α)/(1−α²)^2` bound first and use the proved eq-(4.13) `≤36` handoff only at the final source-facing step. This does not prove the concrete first-stage or recursive split hypotheses; it removes the remaining scalar aggregation once those pivot-path bounds are supplied. |
| Thm 11.4 first-stage/recursive max-entry norm bridge | `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_bounds`, `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_bounds` | Ch11 | **new this session**; the loose and exact-coefficient first-stage/trailing product splits now also package directly into the source-shaped `maxEntryNorm` target for `|L̂||D̂||L̂ᵀ|`, not just the scalar finite-product certificate. |
| Thm 11.4 first-stage/recursive stability/solve consumers | `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_bounds`, `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_maxEntryNorm_bounds`, `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_maxEntryNorm_bounds` | Ch11 | **new this session**; the loose and exact-coefficient first-stage/trailing product split now feeds both the pointwise Bunch-Kaufman stability surface and the solve-side normwise perturbation wrapper directly, including solve hypotheses stated against the repository `maxEntryNorm` of `|L̂||D̂||L̂ᵀ|`, so the remaining pivot-path proof can target the concrete local/trailing split hypotheses. |
| α bounds `1/2 < α ≤ 5/7`, `α² = (α+1)/4` | `bunch_parlett_alpha_gt_half`, `bunch_parlett_alpha_le_5_7`, `bunch_parlett_alpha_sq` | " | **new this session**; supporting the Thm 11.4 constants |
| Eq (11.6) example factorization A = LDLᵀ (partial pivoting) | `higham11_6_partialPivotExample_factorization` | Ch11 | exact `fin_cases` algebra, ε≠0 |
| §11.3 skew-symmetric diag zero | `skewSymmetric_diag_zero`, `higham11_16_skew_diag_zero` | " | Aᵀ=−A ⇒ Aᵢᵢ=0 |
| §11.3 / Alg 11.9 skew 2×2 multiplier bound `|c/a₂₁| ≤ 1` | `skew_twoByTwo_multiplier_bound`, `higham11_9_skew_multiplier_bound` | " | **new this session**; from `|c| ≤ |a₂₁|` (pivot is max) — honest content behind `higham11_9_skew_L_entry_bound_interface` |
| §11.3 / Alg 11.9 skew Schur entry bound `|s| ≤ 3M` | `skew_twoByTwo_schur_entry_bound`, `higham11_9_skew_schur_entry_bound` | " | **new this session**; `s = a_ij − (a_{i2}/a₂₁)a_{j1} + (a_{i1}/a₂₁)a_{j2}` (printed formula); establishes `higham11_9_skewSchurEntryBound` |
| §11.2 Aasen recurrence eq (11.12) from `A=LH` | `higham11_12_aasen_diagonal_equation_of_product` | Ch11 | **new this session**; exact-arithmetic: unit-lower-tri `L` ⇒ `A i i = ∑_{j<i} L i j·H j i + H i i` |
| §11.2 Aasen recurrence eq (11.13) from `A=LH` | `higham11_13_aasen_subdiagonal_equation_of_product` | Ch11 | **new this session**; `k=i+1` ⇒ `A k i = ∑_{j≤i} L k j·H j i + H k i` — the Aasen recurrence structure (exact), toward Thm 11.8 |
| §11.2 Aasen band structure `H j i = 0` (`j>i+1`), from `H=TLᵀ` | `higham11_10_aasenH_band` | Ch11 | **new this session**; `T` tridiagonal + `L` lower-tri ⇒ `H` banded |
| §11.2 Aasen recurrence eq (11.14) next-column update from `A=LH` | `higham11_14_aasen_next_column_of_product` | Ch11 | **new this session**; `L k next = (A k i − ∑_{j≤i} L k j·H j i)/H next i` (`next=i+1`, `k≥i+2`, `H next i≠0`) — completes the exact Aasen recurrence trio (11.12)–(11.14) |
| §11.2 Aasen exact recurrences from `AasenSpec` | `higham11_8_AasenSpec_identity_aasenH_product_eq`, `higham11_8_AasenSpec_identity_aasenH_band`, `higham11_8_AasenSpec_identity_aasenH_exact_recurrences`, `higham11_8_AasenSpec_identity_exact_recurrences_of_H_eq` | Ch11 | **new this session**; an identity-permutation `AasenSpec` now supplies `A=L(TLᵀ)`, the bandedness of `H=T Lᵀ`, and the exact recurrence predicates (11.12), (11.13), and (11.14), with only the nonzero subdiagonal `H next i` pivots left explicit. The `H_eq` wrapper feeds source-prefix endpoints that carry a named `H` matrix. |
| §11.2 Aasen subdiagonal pivot bridge | `higham11_8_AasenSpec_identity_aasenH_subdiagonal_eq_T`, `higham11_8_AasenSpec_identity_aasenH_exact_recurrences_of_T_subdiagonal_ne_zero`, `higham11_8_AasenSpec_identity_H_subdiagonal_eq_T_of_H_eq`, `higham11_8_AasenSpec_identity_exact_recurrences_of_H_eq_T_subdiagonal_ne_zero` | Ch11 | **new this session**; for `H=T Lᵀ` under `AasenSpec`, proves `H next i = T next i` on the source subdiagonal (`next=i+1`), so exact-recurrence wrappers can ask for the concrete tridiagonal subdiagonal nonzero hypothesis `T next i≠0` instead of a separate `H` pivot nonzero handoff. |
| §11.2 AasenSpec source-prefix split-entry endpoint | `higham11_8_AasenSpec_identity_source_prefix_split_entry_budgets_printed_gamma_validity`, `higham11_8_AasenSpec_identity_source_prefix_split_entry_budgets_printed_gamma_validity_of_unit_roundoff_bound`, `higham11_8_AasenSpec_identity_source_prefix_split_entry_budgets_printed_gamma_validity_of_u_le_cap` | Ch11 | **new this session**; feeds identity-permutation `AasenSpec` plus `H=T Lᵀ` into the source-prefix split-entry printed normwise endpoint, deriving `A=LTLᵀ`, the exact Aasen next-column recurrence, and the required nonzero `H` subdiagonal pivots from the concrete `T next i≠0` hypothesis. The unit-roundoff and displayed-cap aliases also derive the printed `gammaValid (15n+25)` guard from source-shaped smallness assumptions. The concrete `T_hat` comparison and factor/solve split-budget inequalities remain explicit, so this is dependency progress and does not close Theorem 11.8. |
| §11.2 Aasen recurrence eq (11.14) scalar fl update | `higham11_14_fl_aasen_next_column_update_rel_error`, `higham11_14_fl_aasen_next_column_update_abs_error`, `higham11_14_fl_aasen_next_column_update_sum_abs_error`, `higham11_14_fl_aasen_next_column_update_abs_error_of_exact_recurrence` | Ch11 | **new this session**; proves `fl(fl(a-s)/h) = ((a-s)/h)(1+θ)`, `|θ| ≤ γ₂`, additive form `exact + Δ`, finite-sum specialization for `Aki − ∑_{j≤i}LkjHji`, and the exact-recurrence bridge `fl update = L k next + Δ`, `|Δ| ≤ γ₂|L k next|`; first local fl ingredient for the Aasen next-column update |
| §11.2 Aasen recurrence eq (11.14) rounded prefix-sum formation | `higham11_14_fl_aasenPrefixDot`, `higham11_14_fl_aasen_prefix_dot_abs_error`, `higham11_14_fl_aasenSourcePrefixDot`, `higham11_14_fl_aasen_source_prefix_dot_abs_error`, `higham11_14_fl_aasen_next_column_update_formed_sum_abs_error_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_formed_sum_single_abs_error_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_formed_sum_abs_sub_bound_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_source_prefix_abs_sub_bound_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_update_source_prefix_column_component_bound_of_exact_recurrence`, `higham11_14_fl_aasen_next_column_source_prefix_Lhat_column_relative_bound_of_exact_recurrence`, `higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence` | Ch11 | **new this session**; masks the prefix `j≤i` into a fixed-length rounded dot product and proves its `γ_n` additive residual, also proves the tighter source-length prefix-dot residual with `γ_{i+1}` (`next.val = i.val+1`), combines source-prefix formation with the exact-recurrence update bridge, packages the formed-sum update as `L k next + Δ`, exposes direct componentwise inequalities, lifts the source-prefix scalar budget over the updated entries of the next column, packages one updated column as a relative `L_hat` factor bound, and dispatches those per-successor-column bounds to a global relative-factor hypothesis consumed by the Aasen factorization-product theorem |
| §11.2 Aasen solve chain eq (11.15), outer triangular solves | `higham11_15_fl_aasen_outer_triangular_solves_backward_error` | Ch11 | **new this session**; packages existing Chapter 8 forward/back substitution backward-error theorems for the two outer solves `Lz=Pb` and `Lᵀw=y` |
| §11.2 Aasen solve chain eq (11.15), middle tridiagonal solve | `higham11_15_fl_aasen_middle_tridiagonal_solve_backward_error` | Ch11 | **new this session**; consumes the Chapter 9 equation-(9.20) tridiagonal LU perturbation model for `T`, uses the actual rounded triangular solves, and returns `(T+ΔT)ŷ=z` with the equation-(9.22) `f(γ_n)|L̂||Û|` componentwise bound |
| §11.2 Aasen solve chain eq (11.15), rounded component package | `higham11_15_fl_aasen_solve_chain_backward_error_components` | Ch11 | **new this session**; composes the outer triangular-solve and middle tridiagonal-solve bridges into a single computed chain `ẑ,q̂,ŷ,ŵ,x̂` exposing all three perturbed equations |
| §11.2 Aasen solve chain eq (11.15), algebraic source collapse | `higham11_15_aasenChainDeltaA`, `higham11_15_aasenTripleTerm_abs_bound`, `higham11_15_aasenTripleTerm_abs_bound_gamma`, `higham11_15_aasenChainDeltaA_abs_bound_of_entrywise`, `higham11_15_aasenChainDeltaABound`, `higham11_15_aasenChainDeltaA_abs_bound_gamma`, `higham11_15_aasen_chain_source_backward_error_of_components` | Ch11 | **new this session**; collapses `(L+ΔL)(T+ΔT)(U+ΔU)` against `LTU=A` to obtain a single source equation `(A+ΔA)w=rhs`; also proves the scalar seven-term triple-product bound, its collected outer-`γ`/middle-budget specialization, the summation bridge, and the closed componentwise `higham11_15_aasenChainDeltaABound` for the collapsed perturbation |
| §11.2 Aasen solve chain eq (11.15), closed-budget norm aggregation | `higham11_15_aasenChainDeltaABound_nonneg`, `higham11_15_aasenMiddleSolveBudget_nonneg`, `higham11_15_aasenMiddleSolveBudget_infNorm_le`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_absLU`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_norm_bound`, `higham11_15_absLU_infNorm_le_of_componentwise_T_bound`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_colDiagDom_LUFactSpec`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_rowDiagDom_LUFactSpec`, `higham11_15_aasenChainDeltaABound_infNorm_le`, `higham11_15_infNorm_le_of_aasenChainDeltaABound` | Ch11 | **new this session**; proves the closed chain and middle tridiagonal-solve budgets are nonnegative, aggregates the middle budget both to `f(γ_n)‖L_T‖∞‖U_T‖∞` and directly to `f(γ_n)‖|L_T||U_T|‖∞`, provides relative factor-product and abs-LU norm forms, converts componentwise `|L_T||U_T|≤κ|T̂|` into the corresponding norm bound, and instantiates the concrete column- and row-dominant tridiagonal LUFactSpec `3|T̂|` Chapter 9 bounds; the closed chain's two scalar triple-product sums are aggregated into the normwise bound `(2γ+γ²)‖L‖∞‖T‖∞‖U‖∞ + (1+2γ+γ²)‖L‖∞‖BT‖∞‖U‖∞`, then transferred to any perturbation dominated componentwise by `higham11_15_aasenChainDeltaABound` |
| Thm 11.8 checkerboard middle determinant-inequality adapter | `higham11_15_absLU_componentwise_T_bound_of_checkerboard_principalBlock_inequalities`, `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_checkerboard_principalBlock_inequalities`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_zero_relative_T_hat_checkerboard_principalBlock_inequalities`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_checkerboard_principalBlock_inequalities_entry_bound_nonneg` | Ch11 | **new this session**; exposes the Chapter 9 checkerboard total-nonnegative coefficient-one `|L_T||U_T|=|T̂|` route with determinant-inequality hypotheses rather than pre-proved positive leading principal blocks, packages it directly into the Aasen middle-solve norm budget `f(γ_n)‖T̂‖∞`, and lifts that source-facing middle handoff into both the generic zero-relative source-norm-cap endpoint and the inverse-scale Aasen-entry source-prefix exact-radius endpoint. This is still a dependency bridge; the concrete Aasen `T̂` checkerboard certificate remains open. |
| Thm 11.8 summed Aasen budget norm aggregation | `higham11_8_infNorm_le_of_sum_aasenChainDeltaABounds`, `higham11_8_aasenNormwiseBackwardBound_of_sum_aasenChainDeltaABounds` | Ch11 | **new this session**; if a source perturbation is bounded componentwise by the sum of two closed Aasen chain budgets, its `∞`-norm is bounded by the sum of the corresponding two-term normwise budgets; the new predicate bridge turns that scalar norm budget directly into the printed Theorem 11.8 normwise target, avoiding an entrywise `η|T̂|` comparison when a normwise scalar comparison is available |
| Thm 11.8 scalar norm-budget reducer | `higham11_8_aasen_factor_solve_coeff_le_of_parts`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds`, `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds`, `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_gamma_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_middle_factor_product_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_absLU_norm_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_absLU_componentwise_T_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff`, `higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff_parts`, `higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff` | Ch11 | **new this session**; reduces the scalar norm-budget hypothesis for the factorization+solve wrapper to primitive `∞`-norm factor bounds for `L`, `Lᵀ`, `L̂`, `L̂ᵀ`, `T`, the factor `BT`, and the middle solve budget, plus one printed-coefficient inequality; the relative-factor reducers derive the `L̂` and `L̂ᵀ` norm constants as `(1+γ_factor)` times the source-factor constants from `|L̂-L|≤γ_factor|L|`, with either a monolithic coefficient inequality or four gamma-share obligations; the coefficient splitters let later work prove the four factorization/solve contributions separately, either as raw scalar pieces or as shares of the printed `(n−1)^2γ_{15n+25}` coefficient; the direct column/row-dominant variants accept the same four terms as one scalar sum; the middle-route reducers discharge the middle budget either from a separate factor product, the more concrete abs-LU norm or componentwise `|T̂|` bound, or directly from the column- or row-dominant tridiagonal LUFactSpec `3f(γ_n)` specializations |
| Thm 11.8 relative `T_hat` fallback scalar norm-budget reducers | `higham11_8_aasen_factor_solve_norm_budget_of_relative_T_hat_error`, `higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_relative_T_hat_error` | Ch11 | **new this session**; a supplied relative middle-factor error `|T_hat-T|≤κBT|T_hat|` now directly instantiates the concrete factorization-side budget `κBT|T_hat|` and feeds the scalar norm-budget route, including the generated relative-`L_hat` outer-factor variant. This fallback uses the proved `‖T‖∞≤(1+κBT)‖T_hat‖∞` cap, so it is useful for non-exact-radius norm budgeting but does **not** close the sharper source route requiring `κT=1` or a direct `‖T‖∞≤‖T_hat‖∞`/entrywise `|T|≤|T_hat|` fact. |
| Thm 11.8 relative `T_hat` source-prefix fallback endpoints | `higham11_8_source_prefix_concrete_majorants_of_relative_T_hat`, `higham11_8_source_prefix_concrete_majorants_gamma_n_of_relative_T_hat` | Ch11 | **new this session**; short aliases for the generated wrappers `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants_of_relative_T_hat_error` and `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_n_of_relative_T_hat_error`. Lifts the relative-`T_hat` fallback into the generated source-prefix Aasen endpoint. The generic wrapper derives `‖T‖∞≤(1+κBT)‖T_hat‖∞` from `|T_hat-T|≤κBT|T_hat|` and charges the first scalar product coefficient with `1+κBT`; the `γ_n` wrapper uses the printed `gammaValid (15n+25)` guard to fill the local prefix/update/solve validity hypotheses. This is still a dependency bridge: it avoids a separate `T`-norm handoff for fallback bounds but does not prove the sharper coefficient-one `T` comparison required by the selected source theorem. |
| Thm 11.8 Aasen outer-factor `(n-1)` majorant | `higham11_8_sum_abs_le_card_pred_mul_of_one_zero`, `higham11_8_aasen_outer_factor_row_col_sum_majorants_of_entry_bound`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound`, `higham11_8_aasen_outer_factor_scaled_entry_cap`, `higham11_8_one_plus_mul_le_one_of_le_inv_one_plus`, `higham11_8_aasen_outer_factor_scaled_entry_cap_of_le_inv_one_plus`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_scaled_unit`, `higham11_8_nonneg_of_uniform_abs_entry_bound`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus_of_entry_bound`, `higham11_8_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`, `higham11_8_outer_factor_caps_of_aasen_entry_bound_inv_one_plus_of_entry_bound`, `higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus`, `higham11_8_aasen_base_square_bounds_of_entry_bound_inv_one_plus_of_entry_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_checkerboard_middle_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_componentwise_T_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_of_T_norm_cap_entry_bound_nonneg`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap_checkerboard_middle`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_scaled_unit_of_T_norm_cap`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_componentwise_T`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_T_norm_cap` | Ch11 | **new this session**; proves that Aasen's exact outer factor structure (strict upper-zero entries plus first-column zeros below the first row) turns a uniform exact-factor entry bound into row and column sum majorants with `(n-1)` entries, then feeds those majorants to the relative outer-factor norm caps required by the exact-radius route. The normalized scalar helper reduces the row/column scale comparison to `(1+γ)κ≤1`, and the inverse-scale wrapper discharges that normalized cap from the source-style hypothesis `κ≤1/(1+γ)`; the unscaled and base-square wrappers derive the exact outer-factor caps and `(n-1)^2` product caps consumed by exact-radius routes. The source-prefix endpoints consume the sharper cap directly in both the entrywise `|T|≤|T̂|` middle route and the direct `‖T‖∞≤‖T̂‖∞` route, either with a supplied middle product estimate or with the checkerboard LU specialization, replacing the crude `n`-entry fallback once the concrete source entry bound and scalar comparison are supplied; both the checkerboard and direct-middle endpoints now accept the source-style inverse-scale entry estimate directly, and the matching normalized endpoint wrappers derive their own `0≤κ` side condition from the entry bound. The lower-level inverse-scale and normalized cap/base-square helpers can also derive `0≤κ` from the same nonempty uniform absolute entry bound. |
| Thm 11.8 AasenSpec inverse-entry cap helpers | `higham11_8_relative_outer_factor_caps_of_AasenSpec_inverse_entry_bound`, `higham11_8_aasen_base_square_bounds_of_AasenSpec_inverse_entry_bound` | Ch11 | **new this session**; specializes the `AasenSpec` product-size helpers to the source-style direct hypothesis `|Lᵢⱼ|≤1/(1+γ)`, eliminating the auxiliary `κ` and `κ≤1/(1+γ)` handoff before the exact-radius Aasen outer-factor norm and base-square caps are consumed. |
| Thm 11.8 AasenSpec inverse-entry source-prefix endpoints | `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_checkerboard_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; specializes the identity-permutation `AasenSpec` exact-product endpoints to the direct source-style inverse exact outer-factor entry estimate `|Lᵢⱼ|≤1/(1+γ_n)`. These wrappers remove the auxiliary `κLentry` and scalar comparison hypotheses from both direct-middle and checkerboard-middle source-prefix routes while still leaving the concrete `T_hat` comparison/product-size facts as open Theorem 11.8 inputs. |
| Thm 11.8 AasenSpec printed-smallness source endpoints | the corresponding `_of_unit_roundoff_bound` and `_of_u_le_cap` wrappers for `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_checkerboard_endpoint_of_inverse_entry_bound`, and `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; gives the four closest `AasenSpec` exact-product inverse-entry source endpoints source-shaped smallness guards. Callers may now supply either `(15n+25)fp.u<1` or `fp.u≤Ucap`, `(15n+25)Ucap<1` directly; the genuine entry cap, `T_hat` comparison, and checkerboard/product-size hypotheses remain explicit. |
| Thm 11.8 scalar coefficient product-cap helpers | `higham9_14_f_mono_nonneg`, `higham11_gamma_add_le`, `higham11_8_two_gamma_plus_sq_mul_le_of_le`, `higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_le`, `higham11_8_two_gamma_plus_sq_mul_le_of_majorants`, `higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants`, `higham11_8_higham9_14_f_gamma_le_gamma_4n`, `higham11_8_three_higham9_14_f_gamma_le_gamma_12n`, `higham11_8_two_gamma_plus_sq_le_gamma_2n`, `higham11_8_one_plus_two_gamma_plus_sq_mul_gamma_le_gamma_3n`, `higham11_8_one_plus_two_gamma_plus_sq_mul_higham9_14_f_gamma_le_gamma_6n`, `higham11_8_one_plus_two_gamma_plus_sq_mul_three_higham9_14_f_gamma_le_gamma_14n`, `higham11_8_gamma_2n_plus_3n_plus_2n_plus_6n_le_gamma_15n25`, `higham11_8_triple_product_square_bound_of_middle_le_one`, `higham11_8_aasen_product_square_bounds_of_base_le_one`, `higham11_8_aasen_factor_solve_coeff_le_of_product_square_bounds`, `higham11_8_aasen_relative_coeff_le_of_gamma_product_square_bounds`, `higham11_8_aasen_relative_coeff_le_of_gamma_base_square_bounds`, `higham11_8_aasen_relative_coeff_le_of_gamma_base_square_exact_radius`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_bounds`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_concrete_product_majorants`, `higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_concrete_product_majorants` | Ch9/Ch11 | **new this session**; factors the four gamma-share coefficient comparisons through reusable product caps, larger gamma/product majorants, exact product-square caps for the printed `(n−1)^2` prefactor, and monotonicity/absorption of Chapter 9's tridiagonal LU polynomial `f(u)=4u+3u²+u³`, including direct absorptions for `2γ_n+γ_n²`, `(1+2γ_n+γ_n²)γ_n`, `f(γ_n)`, `(1+2γ_n+γ_n²)f(γ_n)`, `3f(γ_n)`, and `(1+2γ_n+γ_n²)3f(γ_n)`; the exact-product discharge now allocates the concrete `T_hat` route to `γ_{2n}+γ_{3n}+γ_{2n}+γ_{6n}≤γ_{15n+25}` from square bounds and `κBT≤γ_n`, the reduced base-square interface derives the four exact-product caps from the two base square caps plus `κT≤1` and `κmidLU≤1`, and the exact-radius specialization uses the printed `γ_{15n+25}` directly, so later work can prove product-size bounds and scaled gamma-share bounds separately before invoking the existing four-share splitter, discharge the same product-majorant route with one aggregate printed-coefficient inequality, or instantiate the product caps with the exact products from the relative Aasen norm budget in either aggregate or reduced aggregate form; the product-majorant reducers also transport the concrete middle term `f(γ_solve)κmidLU` through a larger `γ_mid_cap` |
| Thm 11.8 printed gamma-validity guard | `higham11_8_gammaValid_15n25_of_unit_roundoff_bound`, `higham11_8_gammaValid_15n25_of_u_le_cap`, `higham11_8_gammaValid_n_two_prefix_of_u_le_cap` | Ch11 | **new this session**; turns the source smallness condition `(15n+25)u<1`, or a displayed cap `u≤Ucap` with `(15n+25)Ucap<1`, into the repository `gammaValid fp (15*n+25)` hypothesis and the local `gammaValid n`, `gammaValid 2`, and prefix-dot validity side conditions used by the Aasen wrappers. This discharges only the gamma-validity guard plumbing; the concrete Aasen product-size and `T_hat` comparison facts remain open. |
| Thm 11.8 printed-radius smallness source endpoints | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma_validity_of_unit_roundoff_bound`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets_printed_gamma_validity_of_u_le_cap`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma_validity_of_unit_roundoff_bound`, and `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets_printed_gamma_validity_of_u_le_cap` | Ch11 | **new this session**; lifts the printed gamma-validity guard into the supplied and source-prefix split-entry normwise endpoints, so callers can provide either the direct source smallness condition `(15n+25)fp.u<1` or a displayed cap `fp.u≤Ucap`, `(15n+25)Ucap<1` rather than manually constructing `gammaValid fp (15*n+25)`. |
| Thm 11.8 Aasen factorization product residual budget | `higham11_8_aasenFactorizationProductBudget`, `higham11_8_aasen_factorization_product_abs_bound_of_entrywise_factor_bounds`, `higham11_8_aasen_factorization_product_abs_bound_gamma`, `higham11_8_aasen_factorization_product_abs_bound_of_source_prefix_updates` | Ch11 | **new this session**; from exact `A=LTLᵀ` and entrywise factor budgets `|L̂−L|≤BL`, `|T̂−T|≤BT`, proves the product residual `|L̂T̂L̂ᵀ−A|` is bounded by an explicit seven-term double-sum budget; specializes relative `|L̂−L|≤γ|L|` and middle `|T̂−T|≤BT` budgets to the closed `higham11_15_aasenChainDeltaABound`; now also instantiates the relative `L_hat` factor hypothesis from the source-prefix rounded recurrence bridge, so the factorization-product residual can be consumed from the modeled next-column updates plus the remaining concrete `T_hat` budget |
| §11.2 Aasen solve chain eq (11.15), rounded source backward-error wrapper | `higham11_15_aasenMiddleSolveBudget`, `higham11_15_fl_aasen_solve_chain_source_backward_error_of_delta_bound`, `higham11_15_fl_aasen_solve_chain_source_backward_error` | Ch11 | **new this session**; instantiates the rounded component package and algebraic collapse, first under an explicit componentwise budget and then with the closed `higham11_15_aasenChainDeltaABound` generated from the outer `γ_n` solve bounds and the middle `f(γ_n)|L_T||U_T|` budget |
| Thm 11.8 factorization + solve-chain source wrapper | `higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals`, `higham11_8_fl_aasen_factor_solve_source_backward_error` | Ch11 | **new this session**; combines a factorization residual `A_fact−A` with a solve-chain residual `ΔS` into one source perturbation `ΔA`, then instantiates this for rounded Aasen solves with computed factors `L̂,T̂`, yielding `(A+ΔA)ŵ=Pᵀb` with componentwise budget `B_factor+B_solve` |
| §11.2 Aasen solve chain eq (11.15), exact unpermuted algebra | `higham11_15_aasenSolveChain_identity_solve_of_product` | Ch11 | **new this session**; if `A = L T Lᵀ` and the exact chain `Lz=b`, `Ty=z`, `Lᵀw=y`, `x=w` holds (identity permutation), then `A x = b`; this is the algebraic base for later rounded solve-chain perturbation |
| Thm 11.8 norm bridge: componentwise perturbation ⇒ `∞`-norm bound | `higham11_8_infNorm_le_card_mul_of_uniform_componentwise_bound`, `higham11_8_aasenNormwiseBackwardBound_of_uniform_componentwise_bound`, `higham11_8_infNorm_le_mul_of_componentwise_T_bound`, `higham11_8_infNorm_T_hat_sub_T_le_mul_of_relative_error`, `higham11_8_infNorm_scaled_abs_T_hat_le`, `higham11_8_abs_T_le_one_plus_gamma_T_hat_of_relative_error`, `higham11_8_infNorm_T_le_one_plus_gamma_T_hat_of_relative_error`, `higham11_8_infNorm_factor_le_of_relative_entry_bound`, `higham11_8_infNorm_factorTranspose_le_of_relative_entry_bound`, `higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound`, `higham11_8_componentwise_T_bound_add_of_parts`, `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound`, `higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound_coeff_le` | Ch11 | **new this session**; if `|ΔAᵢⱼ| ≤ β`, then `‖ΔA‖∞ ≤ nβ`; if `|ΔAᵢⱼ| ≤ η|T̂ᵢⱼ|`, then `‖ΔA‖∞ ≤ η‖T̂‖∞`; a supplied source-style `|T̂−T|≤γ|T̂|` now directly yields both `‖T̂−T‖∞≤γ‖T̂‖∞` and the concrete envelope norm `‖γ|T̂|‖∞≤γ‖T̂‖∞`, while the exact factor itself gets only the weaker entrywise/norm consequences `|Tᵢⱼ|≤(1+γ)|T̂ᵢⱼ|` and `‖T‖∞≤(1+γ)‖T̂‖∞`; relative factor perturbations `|L_hat-L|≤γ|L|` give `(1+γ)` bounds for `L_hat` and its transpose; all bridge into the printed `(n−1)^2γ_{15n+25}‖T̂‖∞` target once the scalar budget is available; the closed solve-chain budget `higham11_15_aasenChainDeltaABound` now feeds the same printed normwise predicate under an entrywise comparison to `η|T̂|`; the splitter combines separate factorization and solve-chain entrywise comparisons `η_factor|T̂|` and `η_solve|T̂|` when `η_factor+η_solve≤η`; the coefficient adapter accepts `η ≤ (n−1)^2γ_{15n+25}` and multiplies by `‖T̂‖∞` internally |
| Thm 11.8 zero-relative `T_hat` cap | `higham11_8_abs_T_le_T_hat_of_zero_relative_error`, `higham11_8_infNorm_T_le_T_hat_of_zero_relative_error`, `higham11_8_zero_relative_T_hat_error_of_eq`, `higham11_8_abs_T_le_T_hat_of_eq`, `higham11_8_infNorm_T_le_T_hat_of_eq` | Ch11 | **new this session**; specializes the relative `|T̂−T|≤γ|T̂|` diagnostics at `γ=0`, recovering the coefficient-one entrywise and `∞`-norm exact-`T` caps required by exact middle-matrix routes when the computed and exact tridiagonal factors coincide componentwise. The equality adapters derive the zero-relative budget and both caps directly from pointwise `T_hat = T`, removing a small caller-side handoff for exact-middle routes. |
| Thm 11.8 zero-relative `T_hat` source-constant endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_constants_of_zero_relative_T_hat` | Ch11 | **new this session**; specializes the supplied exact-radius source-constant route so a zero relative `T_hat - T` comparison supplies both the `γ_n` factorization budget and the direct `‖T‖∞≤‖T_hat‖∞` cap, removing two separate middle-factor handoffs from that endpoint. |
| Thm 11.8 zero-relative `T_hat` supplied checkerboard endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle` | Ch11 | **new this session**; specializes the supplied checkerboard-middle route with relative exact outer-factor caps so the zero relative `T_hat - T` comparison supplies both the concrete `γ_n` middle-factor budget and the direct exact-`T` norm cap. |
| Thm 11.8 zero-relative `T_hat` source-prefix checkerboard endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_relative_norm_caps_of_zero_relative_T_hat_checkerboard_middle` | Ch11 | **new this session**; specializes the source-prefix checkerboard-middle route with relative exact outer-factor caps so the zero relative `T_hat - T` comparison supplies the middle-factor budget and exact-`T` norm cap while the relative `L_hat` hypothesis is generated from the rounded Aasen recurrence model. |
| Thm 11.8 zero-relative `T_hat` source-prefix direct norm-cap endpoint | `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_zero_relative_T_hat`, `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_T_hat_eq_T` | Ch11 | **new this session**; generic direct-middle source-prefix wrapper turning zero relative `T_hat - T` into the `γ_n` factorization-side middle budget and exact `T`-norm cap under supplied outer factor norm caps and a supplied `|L_T||U_T|≤|T_hat|` product estimate. The equality variant derives that zero-relative handoff directly from pointwise `T_hat = T`. |
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
| Thm 11.8 `AasenSpec` product-size wrappers | `higham11_8_aasen_outer_factor_row_col_sum_majorants_of_AasenSpec_entry_bound`, `higham11_8_relative_outer_factor_caps_of_AasenSpec_entry_bound_scaled_unit`, `higham11_8_relative_outer_factor_caps_of_AasenSpec_entry_bound_inv_one_plus`, `higham11_8_aasen_base_square_bounds_of_AasenSpec_entry_bound_scaled_unit`, `higham11_8_aasen_base_square_bounds_of_AasenSpec_entry_bound_inv_one_plus` | Ch11 | **new this session**; source-facing wrappers unpack `AasenSpec`'s lower-triangular and first-column-zero fields, so a concrete uniform exact outer-factor entry cap plus either normalized `(1+γ)κ≤1` or source-style `κ≤1/(1+γ)` scalar comparison now directly yields the row/column majorants, relative norm caps, and exact-product base-square caps required by the `T_hat` exact-radius route. |
| Thm 11.8 `AasenSpec` exact-product wrappers | `higham11_8_AasenSpec_permuted_product_eq`, `higham11_8_AasenSpec_product_eq_of_identity_perm` | Ch11 | **new this session**; exposes the exact `PAPᵀ=LTLᵀ` product carried by `AasenSpec`, plus the identity-permutation specialization in the unpermuted `A=LTLᵀ` form consumed by the source-prefix backward-error endpoints. |
| Thm 11.8 `AasenSpec` identity zero-relative checkerboard endpoint | `higham11_8_AasenSpec_identity_source_prefix_zero_relative_checkerboard_endpoint` | Ch11 | **new this session**; feeds an identity-permutation `AasenSpec` directly into the zero-relative `T_hat` source-prefix checkerboard endpoint, discharging the exact product and `L` zero-pattern hypotheses while leaving the concrete recurrence, entry-cap, `T_hat`, LU-certificate, and gamma-validity assumptions explicit. |
| Thm 11.8 `AasenSpec` identity zero-relative direct-middle endpoint | `higham11_8_AasenSpec_identity_source_prefix_zero_relative_direct_middle_endpoint` | Ch11 | **new this session**; feeds an identity-permutation `AasenSpec` into the zero-relative source-prefix direct-middle endpoint, discharging the exact product and `L` zero-pattern hypotheses while keeping the supplied `|L_T||U_T|≤|T_hat|` middle-product estimate, recurrence, entry cap, `T_hat`, and gamma-validity assumptions explicit. |
| Thm 11.8 `AasenSpec` identity zero-relative inverse-entry endpoints | `higham11_8_AasenSpec_identity_source_prefix_zero_relative_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_zero_relative_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; source-style inverse-entry specializations of the zero-relative endpoints, setting `κLentry=1/(1+γ_n)` directly for both the supplied direct-middle and checkerboard determinant-inequality routes while keeping the zero-relative `T_hat` comparison explicit. |
| Thm 11.8 `AasenSpec` zero-relative printed-smallness endpoints | the corresponding `_of_unit_roundoff_bound` and `_of_u_le_cap` wrappers for `higham11_8_AasenSpec_identity_source_prefix_zero_relative_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_zero_relative_checkerboard_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, and `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; gives the zero-relative inverse-entry endpoints source-shaped smallness guards in both ordinary and normalized scaled-unit forms. Callers may supply either `(15n+25)fp.u<1` or a displayed cap `fp.u≤Ucap`, `(15n+25)Ucap<1`; the genuine zero-relative `T_hat` comparison, middle product/checkerboard LU, recurrence, and inverse exact outer-factor entry hypotheses remain explicit. |
| Thm 11.8 `AasenSpec` identity `T_hat=T` endpoints | `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_direct_middle_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_checkerboard_endpoint` | Ch11 | **new this session**; exact-middle equality wrappers for the identity-permutation `AasenSpec` source-prefix endpoints, deriving the zero-relative `T_hat-T` handoff from pointwise equality for both the supplied direct middle product and checkerboard determinant-inequality routes. |
| Thm 11.8 `AasenSpec` identity `T_hat=T` inverse-entry endpoints | `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; source-style inverse-entry specializations of the exact-middle equality endpoints, setting `κLentry=1/(1+γ_n)` directly for both the supplied direct-middle and checkerboard determinant-inequality routes while keeping the concrete middle-product/checkerboard hypotheses explicit. |
| Thm 11.8 `AasenSpec` identity normalized zero-relative endpoints | `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_direct_middle_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_checkerboard_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_direct_middle_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_checkerboard_endpoint` | Ch11 | **new this session**; exposes the normalized `(1+γ_n)κ≤1` Aasen entry-cap route through the identity-permutation `AasenSpec` interface for both supplied direct-middle and checkerboard-middle paths, plus pointwise `T_hat=T` adapters that derive the zero-relative handoff. |
| Thm 11.8 `AasenSpec` identity normalized zero-relative inverse-entry endpoints | `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; source-style inverse-entry specializations of the normalized zero-relative endpoints, deriving `(1+γ_n)κ≤1` at `κ=1/(1+γ_n)` from gamma nonnegativity for both direct-middle and checkerboard determinant-inequality routes. |
| Thm 11.8 `AasenSpec` identity normalized `T_hat=T` inverse-entry endpoints | `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; source-style inverse-entry specializations of the normalized exact-middle equality endpoints, deriving `(1+γ_n)/(1+γ_n)≤1` from gamma nonnegativity and setting `κLentry=1/(1+γ_n)` for both the supplied direct-middle and checkerboard determinant-inequality routes. |
| Thm 11.8 `AasenSpec` exact-`T_hat` printed-smallness endpoints | the corresponding `_of_unit_roundoff_bound` and `_of_u_le_cap` wrappers for `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_checkerboard_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, and `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; gives the exact-middle equality inverse-entry endpoints the same source-shaped smallness guards as the nonzero-relative and split-entry Aasen routes. Callers may supply either `(15n+25)fp.u<1` or a displayed cap `fp.u≤Ucap`, `(15n+25)Ucap<1`; the genuine `T_hat=T`, middle product/checkerboard LU, recurrence, and inverse exact outer-factor entry hypotheses remain explicit. |
| Thm 11.8 `AasenSpec` identity normalized componentwise/`T`-norm endpoints | `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_direct_middle_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_direct_middle_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_checkerboard_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_checkerboard_endpoint` | Ch11 | **new this session**; exposes the normalized `(1+γ_n)κ≤1` Aasen entry-cap route through the identity-permutation `AasenSpec` interface for the nonzero-relative direct-middle and checkerboard-middle endpoints, with either entrywise `|T|≤|T_hat|` or a supplied exact `T` norm cap. |
| Thm 11.8 `AasenSpec` identity normalized componentwise/`T`-norm inverse-entry endpoints | `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; source-style inverse-entry specializations of the normalized nonzero-relative Aasen endpoints, setting `κLentry=1/(1+γ_n)` and deriving the normalized scalar cap from gamma nonnegativity for both direct-middle and checkerboard routes. |
| Thm 11.8 `AasenSpec` normalized componentwise/`T`-norm printed-smallness endpoints | the corresponding `_of_unit_roundoff_bound` and `_of_u_le_cap` wrappers for `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`, `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound`, and `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound` | Ch11 | **new this session**; gives the normalized nonzero-relative inverse-entry endpoints the same source-shaped smallness guards as the ordinary, zero-relative, and exact-middle routes. Callers may supply either `(15n+25)fp.u<1` or a displayed cap `fp.u≤Ucap`, `(15n+25)Ucap<1`; the genuine `T_hat` comparison, exact-`T` or componentwise-`T` cap, middle product/checkerboard LU, recurrence, and inverse exact outer-factor entry hypotheses remain explicit. |
| Thm 11.8 `AasenSpec` identity direct-middle `T`-norm endpoint | `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_direct_middle_endpoint` | Ch11 | **new this session**; feeds an identity-permutation `AasenSpec` into the nonzero-relative source-prefix direct-middle endpoint with a supplied exact-`T` norm cap, discharging the exact product and `L` zero-pattern hypotheses while leaving the recurrence, relative `T_hat` comparison, middle product, entry cap, and gamma-validity assumptions explicit. |
| Thm 11.8 `AasenSpec` identity checkerboard `T`-norm endpoint | `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_checkerboard_endpoint` | Ch11 | **new this session**; feeds an identity-permutation `AasenSpec` into the nonzero-relative source-prefix checkerboard-middle endpoint with a supplied exact-`T` norm cap, discharging the exact product and `L` zero-pattern hypotheses while leaving the recurrence, relative `T_hat` comparison, checkerboard LU certificate, entry cap, and gamma-validity assumptions explicit. |
| Thm 11.8 `AasenSpec` identity componentwise-`T` endpoints | `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_direct_middle_endpoint`, `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_checkerboard_endpoint` | Ch11 | **new this session**; feeds an identity-permutation `AasenSpec` into the nonzero-relative source-prefix endpoints with entrywise `|T|≤|T_hat|`, discharging the exact product and `L` zero-pattern hypotheses for both a supplied direct middle product and the checkerboard LU middle certificate. |
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
| Theorem 11.3 | block LDLᵀ backward error: `P(A+ΔA₁)Pᵀ = L̂D̂L̂ᵀ`, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` (eq 11.5) | `higham11_3_block_ldlt_backward_error_interface` (assumes the whole conclusion) | **substantially advanced (all-1×1 case)**: proved the exact recursion (`exact_blockLDLT_all_oneByOne`), the component stage bounds, packaged all-index one-stage envelope with nonnegativity, raw-Schur recursive all-1×1 envelope, stored-symmetric rounded Schur bridge, storage-defect one-stage bridge, recursive stored-symmetric all-1×1 envelope (`fl_blockLDLT_stored_all_oneByOne_bound`, `higham11_3_fl_blockLDLT_stored_all_oneByOne_bound`), source-facing all-1×1 perturbation packages (`higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne`, `higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne`), norm-bound and scalar-budget consumers for both all-1×1 packages, `BlockLDLTBackwardError`-to-source-interface bridges for the structured factorization envelope including the `∞`-norm-bound variant, the printed first-order source envelope `p u (|A|+|L̂||D̂||L̂ᵀ|)` bridge, product-entry/max-entry normalization bridges for the structured envelope, and scalar product-bound perturbation consumers with and without `∞`-norm aggregation, including the direct `ε≤p*u` source-scale product-budget consumer. NOTE: (11.5) for 2×2 pivots = **Problem 11.5 (benchmark-reserved)** → stays a hypothesis. | extend the induction to mixed 1×1/2×2 pivots while keeping the 2×2 solve bound as a hypothesis, then relate the accumulated envelope to the printed `p(n)u(|A|+Pᵀ|L̂||D̂||L̂ᵀ|P)+O(u²)` form |
| Theorem 11.4 | Bunch–Kaufman normwise stability `(A+ΔA)x̂=b`, `‖ΔA‖_M ≤ p(n)ρₙu‖A‖_M+O(u²)` via `‖|L̂||D̂||L̂ᵀ|‖_M ≤ 36nρₙ‖A‖_M` | `higham11_4_bunch_kaufman_stability` / `..._solve_backward_error_interface` (assume); scalar max-product, finite-max, matrix-product/max-entry-norm, row-sum/product, first-stage/recursive, exact-budget, and stage-growth `D̂` adapters now reduce the consumers to the source-style eq. (4.14) scalar certificate | proof now available (Higham [608,1997] §4.3, eqs. 4.11–4.14, appendix A). Constants, branch-test accessors, scalar case-(1)/(3) multiplier/correction/growth caps, direct case-(2) nonsingularity/correction/growth and local `D̂` pivot cap, conditional case-(2) multiplier caps, local 2×2 `CE⁻¹` row caps, finite product-norm consumers, and growth recursions are proved. Case-(4) now has direct determinant lower-bound, nonsingularity, scaled inverse-entry, asymmetric scaled multiplier row-sum, natural-scale pivot-entry caps, local `D̂` cap, correction, and one-step Schur-growth certificates from the printed product tests; the older source-six row-sum bridge remains conditional on `ωr≤ω1`. Remaining: concrete pivot-path first-stage/trailing split, all-row `|L̂|` aggregation, global `D̂` caps, and path data needed by the aggregate row-sum/product caps (or a direct product-entry proof), then instantiate the exact-coefficient (4.14) estimate. | prove per-row or uniform global `|D̂|`, full `|L̂|` row-sum caps, or row-dependent `|L̂|` entry caps from the scalar-branch and direct case-(4) Schur-growth bridges, conditional case-(2) multiplier bridge where its side condition is available, local 2×2 asymmetric scaled row-sum bridge, local 2×2 `CE⁻¹` source-row cap `≤6`, per-pivot `\|E\|\|E⁻¹\|\|E\|` bounds, and Schur-recursion stage maxima; then feed the relevant `higham11_4_bunchKaufmanMaxEntryProductBound...` exact-coefficient wrapper |
| Theorem 11.7 | Bunch tridiagonal normwise stability, `(A+ΔA₂)x̂=b`, `|ΔAᵢ| ≤ c·u·‖A‖` | `higham11_7_tridiagonal_backward_error_interface` (assumes); Algorithm 11.6 branch tests, the accepted `2×2` pivot determinant lower bound/nonsingularity, inverse-entry bounds, the atomic rounded scalar Schur update, a `Fin 1` trailing-block one-stage printed-budget handoff, the ambient `Fin 3` first-stage embedding, the dimension-generic `Fin (n+3)` local-recursion embedding, trailing-block support packaging, support-preserving perturbation addition, offset-generic zero-prefix base/add packaging including printed-coefficient variants, mixed-depth accumulation, and the offset-two bridge, first local+recursive residual accumulation with printed coefficient addition, the recursive trailing-subproblem perturbation lift, recursive scalar residual composition, zero-prefix support shifting under recursive lifts, leading-support versions of the subproblem and recursive-residual accumulators, the norm-bound version of the leading-support recursive-residual accumulator, the solve-side `ΔA₂` bridge into the source-facing interface with separate nonnegative and direct inf-norm budget forms, the entrywise `|Aᵢⱼ|≤‖A‖∞` bridge for local `Amax` hypotheses, componentwise-to-∞-norm aggregation, source-side norm-bound packaging, finite support-sum aggregation including mixed-offset printed variants, finite supported solve-delta aggregation into the source interface, the trailing-subproblem offset/injectivity bookkeeping for the `2×2` tridiagonal step, matching offset-one lift/support plus scalar and matrix-entry local-recursive norm-bound packages for the `1×1` tridiagonal step, the branch-indexed local assumptions/residual adapter, the terminal-tail branch adapter, finite mixed-pivot path-local adapter, embedded path solve-delta aggregation adapters, the concrete local-to-ambient lift package including local block index range/injectivity, ambient row-dot reindexing, current first-trailing row-dot reindexing, outside-block, shifted-leading-block, earlier first-trailing row/column zero lemmas, later-branch filtered sum-zero variants, row dot-product zero variants, full-sum-to-prefix reductions, prefix-to-current splits, composed before-plus-current reductions at first-trailing rows, separated earlier-plus-current dot-product endpoints, cast-free path-local current-family row-dot reindexing, earlier-plus-current path-local current-dot endpoints, first-trailing solve-row additive decompositions, and residual-equation-to-full-solve-row endpoints, branch residual-equation accessors at local and lifted first-trailing entries, concrete path first-trailing embedding bounds, branch-size residual-witness accessors, lifted residual equations at full-ambient first-trailing indices, and concrete lifted-entry simplifiers for those indices, generic local-to-global budget comparison lemmas, zero-offset lifted source endpoints, zero-offset scalar-budget source endpoints, mixed-path start-offset schedule interface, concrete scheduled/prefix path endpoints, uniform-roundoff prefix endpoints, uniform-coefficient prefix endpoints, concrete last-terminal prefix endpoint, terminal/base lifted solve-row endpoints, second-pivot complement row classification, second-pivot lifted solve-row decomposition, second-pivot complement solve-row bridges, the second-pivot reduced local-row bridge, the local-block combined-row adapter, the prefix-zero decomposition, the decomposed local-block combined-row adapter, the tridiagonal base-zero local-block adapter, the branch-matrix local-block adapter, the branch-matrix base-row/local-earlier-zero handoff, the full-base-row-to-branch-matrix base-row bridge, the global base-solve second-pivot adapters, the global base-solve source endpoints, the coefficient-sum/uniform/scalar full-base-row source endpoints, the initial-only full-base-row source endpoints including symmetric-tridiagonal source wrappers, and the initial-only earlier-lift vacuity route including the full-row earlier-lift zero specialization are now proved | tridiagonal block-LDLᵀ fl analysis | prove the bare accepted `2×2` second-pivot row equation for non-initial accepted branches, the general earlier-lift zero-on-current-local-block condition, and the general earlier-lift zero-before-prefix facts, then instantiate the existing endpoint row bridges and remaining concrete coefficient majorants |

2026-07-10 update: the global base-solve pointwise-prefix source endpoints now
compose the all-row base solve with pointwise earlier-lift zero-before-prefix
facts for the coefficient-sum, uniform-coefficient, and per-branch roundoff
routes, including symmetric-tridiagonal source forms. This removes the
caller-side full-base-row extraction, tridiagonal projection, and summed-prefix
packaging, but the genuine pointwise earlier-lift zero facts remain open.

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
The branch residual witness increment adds
`higham11_7_TridiagonalBranchLocalResidualWitness` and
`higham11_7_tridiagonalBranchLocalResidual_exists_residual_witness`, preserving
the local scalar residual equation together with the perturbation bounds for a
specific branch witness.
A follow-up 2026-07-09 increment adds
`higham11_7_tridiagonalBranchLocalResidualWitness_supported` and
`higham11_7_tridiagonalBranchPathResidualWitnesses_supported`, so
equation-bearing residual witnesses can be fed back into the existing
supported-witness aggregation route without losing the equation data.
A later 2026-07-09 increment adds
`higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`,
so the zero-offset lifted endpoint can consume the residual-equation witnesses
directly and no longer asks the final solve equation for arbitrary supported
witnesses.
The follow-up local/terminal wrapper increment adds
`higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`
and
`higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`,
so the residual-witness handoff is available from both main path assumption
interfaces.
A later 2026-07-09 increment adds the corresponding scalar-budget comparison
endpoints ending in `_residual_witnesses_coeff_roundoff_norm`, so the
equation-bearing solve handoff can also consume the coefficient, roundoff, and
local matrix-norm majorants directly.
A further 2026-07-09 increment adds scheduled coefficient-majorant
residual-witness endpoints, so callers can use any valid start-offset schedule
and still state the solve-equation handoff on equation-bearing residual
witnesses.
A subsequent 2026-07-09 increment adds scheduled scalar-budget
residual-witness endpoints, combining that schedule choice with the coefficient,
roundoff, and local matrix-norm comparisons needed by the concrete mixed path.
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
The latest 2026-07-09 path assembly increment adds
`higham11_7_tridiagonalBranchPathLocalAssumptions_of_init_localAssumptions_last_terminalTailAssumptions`
and
`higham11_7_tridiagonalBranchPathLocalResiduals_of_init_localAssumptions_last_terminalTailAssumptions`,
packaging the concrete recursion shape where every initial branch is local and
only the final branch uses the terminal-tail adapter.
The path witness extraction increment adds
`higham11_7_tridiagonalBranchLocalResidual_exists_supported_witness` and
`higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses`, so
the next aggregation proof can consume explicit per-branch perturbation matrices
with their componentwise, support, and norm budgets.
A residual equation-witness extraction increment adds
`higham11_7_TridiagonalBranchPathResidualWitnesses` and
`higham11_7_tridiagonalBranchPathLocalResiduals_exists_residual_witnesses`, so
future solve-equation assembly can keep each extracted perturbation tied to its
local scalar residual equation.
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
A path coefficient-majorant increment adds
`higham11_7_tridiagonalBranchPath_uniform_coeff_majorant_of_component_bounds`
and
`higham11_7_tridiagonalBranchPath_uniform_coeff_add_majorant_of_component_bounds`,
so the remaining concrete coefficient handoff can be reduced to uniform caps on
the local-step and recursive-tail coefficient components.
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
The schedule-monotonicity increment adds
`higham11_7_tridiagonalPathStartOffsetsFrom_le_of_le`,
`higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_branch_end_of_le`,
`higham11_7_tridiagonalPathStartOffsets_le_of_le`, and
`higham11_7_tridiagonalPathStartOffsets_branch_end_le_branch_end_of_le`,
exposing non-strict start and endpoint ordering for later lifted-entry
arguments.
The schedule-uniqueness increment adds
`higham11_7_tridiagonalPathStartOffsetsFrom_unique`,
`higham11_7_tridiagonalPathStartOffsetsFrom_exists_unique`,
`higham11_7_tridiagonalPathStartOffsets_unique`, and
`higham11_7_tridiagonalPathStartOffsets_exists_unique`, so later concrete path
proofs can identify any supplied schedule with the canonical recurrence.
The schedule-prefix increment adds `higham11_7_tridiagonalPathPrefixSpan`, its
zero and successor split lemmas, the base-offset and zero-based start equality
theorems, and
`higham11_7_tridiagonalPathPrefixSpan_last_add_branch_eq_pivotSpan`, exposing
the explicit prefix-sum form of the canonical mixed-path schedule.
The prefix-span bounds increment adds the corresponding direct prefix-span
containment, branch-end containment, strict ordering, and monotone endpoint
facts, so downstream concrete path proofs can reason from prefix spans without
first materializing a start-offset schedule.
The concrete tail-dimension increment adds
`higham11_7_tridiagonalPathTailDim`,
`higham11_7_tridiagonalPathPrefixSpan_add_branchAmbientDim_tailDim_eq_pivotSpan_succ`,
`higham11_7_tridiagonalPathLocalBlockIndex`, and the terminal
`higham11_7_tridiagonalPathTailDim_last_eq_zero` fact, tying each prefix branch
to the full `pathSpan+1` tridiagonal ambient expected by the lifted local-block
proofs.
The tail-dimension recurrence increment adds
`higham11_7_tridiagonalPathTailDim_head` and
`higham11_7_tridiagonalPathTailDim_succ`, aligning the concrete full-path
tail-dimension function with the head/tail split used by path induction.
The concrete branch-matrix increment adds
`higham11_7_tridiagonalPathBranchMatrix` and its entry/norm bounds, giving the
path-local assumption interface a canonical local matrix extracted from a full
`pathSpan+1` ambient matrix.
The concrete scheduled endpoint increment adds
`higham11_7_tridiagonalPathLocalBlockIndex_injective`,
`higham11_7_tridiagonalPathBranchMatrix_infNorm_le_global_infNorm`, and the two
`...concrete_path_...scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`
source endpoints, so the finite path theorem now uses the canonical branch
matrices directly and no longer requires a separate local-norm hypothesis.
The prefix-span endpoint increment adds the matching
`...concrete_path_...prefix_lifted_sum_zero_offset_of_coeff_roundoff_norm`
endpoints, eliminating the arbitrary schedule quantifier from the remaining
lifted solve equation by rewriting every valid schedule to the concrete prefix
span.
A residual-witness concrete endpoint increment adds scheduled and prefix-span
variants ending in `_residual_witnesses_coeff_roundoff_norm`, so the concrete
mixed path can keep the final lifted solve equation attached to the branch
residual equations instead of arbitrary supported witnesses.
A follow-up residual-witness uniform endpoint increment adds
`_residual_witnesses_coeff_norm`, `_residual_witnesses_uniform_coeff_norm`, and
the initial-local/last-terminal uniform-coefficient variant, matching the
existing supported-witness concrete specialization stack while preserving the
residual equations.
A nonuniform last-terminal residual-witness increment adds
`_residual_witnesses_coeff_roundoff_norm` and
`_residual_witnesses_coeff_norm` variants for the initial-local/terminal-last
path, so callers do not have to collapse coefficients to a common scalar before
using that assembly theorem.
The uniform-roundoff endpoint increment adds the corresponding
`...concrete_path_...prefix_lifted_sum_zero_offset_of_coeff_norm` endpoints,
specializing every local branch budget to the global unit roundoff `u`.
The uniform-coefficient endpoint increment adds the direct
`...concrete_path_...prefix_lifted_sum_zero_offset_of_uniform_coeff_norm`
endpoints, using `(k : ℝ) * c` as the final coefficient budget when every
branch has the same printed coefficient majorant.
A concrete last-terminal endpoint increment adds
`higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_uniform_coeff_norm`,
combining the last-terminal path assembly theorem with the concrete prefix-span
uniform coefficient endpoint.
A residual-witness extraction increment adds
`higham11_7_tridiagonalBranchPathResidualWitnesses_exists_of_init_localAssumptions_last_terminalTailAssumptions`
and
`higham11_7_tridiagonalConcretePathResidualWitnesses_exists_of_init_localAssumptions_last_terminalTailAssumptions`,
so the remaining path induction can obtain equation-bearing perturbation
witnesses directly from the initial-local/terminal-last branch hypotheses.
The remaining Theorem 11.7 work is still instantiating those adapters over the
full mixed pivot path, proving the concrete coefficient majorants, and proving
the final lifted solve equation.

| Theorem 11.8 | Aasen componentwise backward error + `‖ΔA‖_∞ ≤ (n−1)²γ_{15n+25}‖T̂‖_∞` | `higham11_8_aasen_backward_error_interface` (assumes) | remaining: **fl** analysis of the Aasen recurrences + solve chain (11.15). The **exact-arithmetic** recurrence identities (11.12), (11.13), (11.14) are proved; scalar and finite-sum fl additive error forms of (11.14), including the exact-recurrence bridge to `L k next`, are proved; rounded prefix-dot formation residuals in both ambient `γ_n` and source-length `γ_{i+1}` forms are proved; source-prefix formed-update componentwise and column-lift bounds are proved; the source-prefix column budget is packaged into the relative `L_hat` factor hypothesis for one next-column update and then dispatched to the global relative-factor hypothesis; that source-prefix global bridge now feeds the factorization-product residual directly, leaving the concrete `T_hat` budget as the factorization side's remaining modeled input; the factorization-product residual is bounded by an explicit seven-term budget from entrywise `L̂`/`T̂` factor budgets and by the closed `higham11_15_aasenChainDeltaABound` under relative outer-factor bounds; the exact unpermuted solve-chain algebra is proved; the two outer triangular solves in (11.15) are connected to existing backward-error theorems; the middle tridiagonal solve is connected to Chapter 9's equation-(9.20)--(9.22) source perturbation model; the middle budget is now proved nonnegative and norm-aggregated both to `f(γ_n)‖L_T‖∞‖U_T‖∞` and to the more concrete `f(γ_n)‖|L_T||U_T|‖∞`, with a column-dominant LUFactSpec specialization giving `3f(γ_n)‖T̂‖∞`; the rounded solve-chain components are packaged together; the algebraic collapse to `(A+ΔA)w=rhs` is proved and instantiated with the closed `higham11_15_aasenChainDeltaABound`; factorization and solve-chain residuals are combined into a single `(A+ΔA)ŵ=Pᵀb` source equation with summed componentwise budget; the closed chain budget is aggregated into a two-term normwise triple-product bound; a perturbation dominated by the sum of the factorization and solve-chain closed budgets now receives both the summed normwise budget and the printed normwise predicate when a scalar norm budget is supplied; the scalar norm-budget comparison can now be reduced to primitive factor norm bounds and split into four scalar coefficient pieces, and the rounded/source-prefix source wrappers consume that reduced form directly, including variants where the middle budget is discharged from a relative tridiagonal LU factor-product or abs-LU norm bound; the componentwise/closed-chain ⇒ printed `∞`-norm bridges are proved; the rounded solve-chain source equation is packaged with the printed normwise predicate, and the rounded factorization+solve source equation is packaged with that predicate under an explicit entrywise `η|T̂|` comparison, the scalar norm-budget comparison, separate factor/solve entrywise comparisons whose coefficients add to `η`, or a concrete `T_hat` abs-LU/product-majorant route with exact product majorants, square-product gamma discharge, reduced supplied/source-prefix base-square interfaces, exact-radius endpoints for the source-prefix generated `L_hat` case, `γ_n` exact-radius endpoints (`..._gamma_base_square_exact_radius_gamma_n`) that derive the local `gammaValid n`, `gammaValid 2`, and source-prefix `gammaValid next.val` side conditions from the printed `gammaValid (15n+25)` hypothesis, source-constant endpoints (`..._gamma_base_square_exact_radius_source_constants`) that substitute `κT=1`, `κBT=γ_n`, and `κmidLU=1` directly, factor-cap square helpers (`higham11_8_product_square_bound_of_factor_caps`, `higham11_8_aasen_base_square_bounds_of_factor_caps`), the supplied direct-`T` relative-cap checkerboard endpoint `..._relative_norm_caps_of_T_norm_cap_checkerboard_middle`, the source-prefix factor-cap endpoint `..._gamma_base_square_exact_radius_source_factor_caps`, the direct matrix-norm cap endpoint `..._gamma_base_square_exact_radius_source_norm_caps`, the componentwise-`T` variant `..._source_norm_caps_of_componentwise_T` using `higham11_8_infNorm_le_of_componentwise_abs_bound`, the checkerboard-middle variant `..._source_norm_caps_of_componentwise_T_checkerboard_middle` using `higham11_15_absLU_componentwise_T_bound_of_checkerboard_LUFactSpec`, the source-prefix relative-norm-caps variants `..._relative_norm_caps_of_componentwise_T_checkerboard_middle` and `..._relative_norm_caps_of_T_norm_cap_checkerboard_middle` deriving unscaled exact outer-factor caps from relative caps, the row-sum-caps variants `..._row_sum_caps_of_componentwise_T_checkerboard_middle` and `..._row_sum_caps_of_T_norm_cap_checkerboard_middle` deriving those relative caps from scaled row/column sums, the row/column majorant bridge (`higham11_8_relative_outer_factor_caps_of_row_col_sum_majorants`) deriving relative caps from unscaled sum majorants plus scalar scale comparisons, the entrywise-majorant adapter (`higham11_8_relative_outer_factor_caps_of_entrywise_majorant`) deriving both row and column majorants from a uniform exact-factor entry bound, the Aasen-structure adapter (`higham11_8_relative_outer_factor_caps_of_aasen_entry_bound`) deriving the sharper `(n-1)` row/column majorants from strict-upper and first-column zeros plus that uniform entry bound, the normalized scale bridge (`higham11_8_aasen_outer_factor_scaled_entry_cap`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_scaled_unit`) and inverse-scale bridge (`higham11_8_one_plus_mul_le_one_of_le_inv_one_plus`, `higham11_8_relative_outer_factor_caps_of_aasen_entry_bound_inv_one_plus`) reduce the Aasen cap side condition to the source-style `κ≤1/(1+γ)`, source-prefix Aasen-structure checkerboard endpoints consuming either that sharper cap or the normalized `(1+γ_n)κ≤1` condition directly, source-prefix entrywise-majorant checkerboard endpoints deriving the exact-radius route's outer-factor caps directly from the uniform exact-factor entry bound, and relative `T_hat` comparison bridges that turn a supplied `|T̂−T|≤γ|T̂|` into the `BT_factor` norm budget plus diagnostic `(1+γ)` exact-`T` entrywise and norm caps. | prove the remaining source/product-size facts feeding the exact-product `T_hat` route: the concrete uniform exact outer-factor entry bound, plus either entrywise `|T|≤|T̂|` or direct `‖T‖∞≤‖T̂‖∞` (the relative error bridge gives only `|Tᵢⱼ|≤(1+γ)|T̂ᵢⱼ|` and `‖T‖∞≤(1+γ)‖T̂‖∞`), a checkerboard total-nonnegative LU certificate for the coefficient-one middle product `|L_T||U_T|≤|T̂|` (or a direct entrywise proof), the concrete source fact `|T̂−T|≤γ_n|T̂|`, and the printed `gammaValid (15n+25)`; the scalar `κT`, `κmidLU`, `κBT` side conditions, relative and unscaled exact outer-factor caps, direct `T`-norm replacement plumbing, local prefix/update/solve gamma-validity conditions, normalized/source-style inverse Aasen entry-cap and base-square handoffs, entrywise outer-factor majorant handoff, and norm/entrywise consequences of a supplied relative `T_hat` perturbation are now discharged by wrappers |

2026-07-10 update: `higham11_8_AasenSpec_identity_aasenH_exact_recurrences`
and `higham11_8_AasenSpec_identity_exact_recurrences_of_H_eq` derive the exact
Aasen recurrence predicates (11.12), (11.13), and (11.14) from an
identity-permutation `AasenSpec` plus `H=T Lᵀ`, keeping only the nonzero
subdiagonal `H next i` pivots explicit. This removes one exact-recurrence
handoff for source-prefix endpoints but does not prove the remaining concrete
`T_hat` comparison, checkerboard/product-size, or entry-cap facts.
A follow-up 2026-07-10 increment proves `H next i = T next i` for
`H=T Lᵀ` on the source subdiagonal and adds recurrence wrappers whose nonzero
pivot hypothesis is the concrete `T next i≠0` condition. This removes the
separate `H`-pivot handoff but still does not prove the `T_hat` comparison or
middle-product certificate.
The latest 2026-07-10 increment feeds those `AasenSpec` recurrence/product/pivot
bridges into the source-prefix split-entry printed endpoint through
`higham11_8_AasenSpec_identity_source_prefix_split_entry_budgets_printed_gamma_validity`.
The remaining Theorem 11.8 work is still the concrete `T_hat` comparison,
outer-factor entry cap, middle-product certificate, and split-budget
inequalities.
A follow-up 2026-07-10 increment adds source-smallness aliases for that
`AasenSpec` split-entry endpoint, deriving the printed `gammaValid (15n+25)`
guard from either `(15n+25)fp.u<1` or `fp.u≤Ucap`,
`(15n+25)Ucap<1`.

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
A further 2026-07-09 increment adds the determinant-inequality checkerboard
middle adapters
`higham11_15_absLU_componentwise_T_bound_of_checkerboard_principalBlock_inequalities`
and
`higham11_15_aasenMiddleSolveBudget_infNorm_le_of_checkerboard_principalBlock_inequalities`,
so the coefficient-one `|L_T||U_T|≤|T̂|` middle route can consume the same
source-facing determinant-inequality hypotheses exposed by Chapter 9, without a
separate positive-leading-minor handoff.
A follow-up endpoint increment adds
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_checkerboard_principalBlock_inequalities_entry_bound_nonneg`,
so the zero-relative, source-prefix exact-radius route can use those
determinant-inequality hypotheses directly instead of asking callers for a
separate `|L_T||U_T|≤|T_hat|` middle-product estimate.
A companion increment adds
`higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_zero_relative_T_hat_checkerboard_principalBlock_inequalities`,
the same determinant-inequality handoff for the lower-level route where the
outer-factor norm caps are supplied directly.
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
A follow-up 2026-07-09 increment adds the matching direct max-entry-norm solve
forms
`higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_maxEntryNorm_bounds`
and
`higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_maxEntryNorm_bounds`,
so a downstream triangular-solve analysis can state its perturbation budget
against `maxEntryNorm hn (|L̂||D̂||L̂ᵀ|)` without first rewriting through the
finite product certificate.
A further 2026-07-09 increment adds
`higham11_4_first_stage_recursive_product_split_of_row_sum_bounds` and its
loose/exact product-entry and max-entry-norm endpoints, so regional row-sum
caps for `|L̂|` plus a uniform `D̂` entry cap can be fed directly into the
first-stage/trailing split used by the eq-(4.11)--(4.14) aggregation.
A 2026-07-10 increment adds
`higham11_4_first_stage_recursive_uniform_six_rho_budget`,
`higham11_4_product_entries_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
`higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
`higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
`higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
`higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`, and
`higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_growth_D_maxEntryNorm_bound`,
so the source-shaped caps `∑ |L̂ᵢₖ| ≤ 6` and `|D̂ₖₗ| ≤ ρₙ‖A‖_M` feed the
loose first-stage/recursive product-entry, max-entry, stability, and solve
routes without exposing separate regional budget hypotheses.

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
  - 2026-07-09 Theorem 11.7 tridiagonal branch residual witness increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_TridiagonalBranchLocalResidualWitness` and
    `higham11_7_tridiagonalBranchLocalResidual_exists_residual_witness`
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
  - 2026-07-09 Theorem 11.7 finite mixed-pivot last-terminal path assembly increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathLocalAssumptions_of_init_localAssumptions_last_terminalTailAssumptions` and
    `higham11_7_tridiagonalBranchPathLocalResiduals_of_init_localAssumptions_last_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot path witness extraction increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchLocalResidual_exists_supported_witness` and
    `higham11_7_tridiagonalBranchPathLocalResiduals_exists_supported_witnesses`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 finite mixed-pivot residual equation-witness increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_TridiagonalBranchPathResidualWitnesses` and
    `higham11_7_tridiagonalBranchPathLocalResiduals_exists_residual_witnesses`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 residual witness support bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchLocalResidualWitness_supported` and
    `higham11_7_tridiagonalBranchPathResidualWitnesses_supported`
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
  - 2026-07-09 Theorem 11.7 local-to-ambient outside-block zero increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_row_lt_start`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_col_lt_start`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_start_add_dim_le_row`, and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_start_add_dim_le_col`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 local-to-global path budget comparison increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_local_budget_le_global_of_coeff_roundoff_norm` and
    `higham11_7_tridiagonalBranchPath_local_budgets_le_global_of_coeff_roundoff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path coefficient majorant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPath_uniform_coeff_majorant_of_component_bounds` and
    `higham11_7_tridiagonalBranchPath_uniform_coeff_add_majorant_of_component_bounds`
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
  - 2026-07-09 Theorem 11.7 residual-witness lifted zero-offset endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 residual-witness local/terminal endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`
    and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`
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
  - 2026-07-09 Theorem 11.7 residual-witness scalar-budget endpoints increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`
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
  - 2026-07-09 Theorem 11.7 scheduled residual-witness zero-offset endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_sum_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 scheduled residual-witness scalar-budget endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_residuals_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, and
    `higham11_7_tridiagonal_backward_error_interface_of_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`
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
  - 2026-07-09 Theorem 11.7 mixed-path schedule monotonicity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathStartOffsetsFrom_le_of_le`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_branch_end_le_branch_end_of_le`,
    `higham11_7_tridiagonalPathStartOffsets_le_of_le`, and
    `higham11_7_tridiagonalPathStartOffsets_branch_end_le_branch_end_of_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 mixed-path schedule prefix-span increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathPrefixSpan`,
    `higham11_7_tridiagonalPathPrefixSpan_zero`,
    `higham11_7_tridiagonalPathPrefixSpan_succ`,
    `higham11_7_tridiagonalPathStartOffsetsFrom_eq_base_add_prefixSpan`,
    `higham11_7_tridiagonalPathStartOffsets_eq_prefixSpan`, and
    `higham11_7_tridiagonalPathPrefixSpan_last_add_branch_eq_pivotSpan`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 mixed-path prefix-span bounds/order increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathPrefixSpan_lt_pivotSpan`,
    `higham11_7_tridiagonalPathPrefixSpan_branch_end_le_pivotSpan`,
    `higham11_7_tridiagonalPathPrefixSpan_branch_end_le_of_lt`,
    `higham11_7_tridiagonalPathPrefixSpan_lt_of_lt`,
    `higham11_7_tridiagonalPathPrefixSpan_le_of_le`, and
    `higham11_7_tridiagonalPathPrefixSpan_branch_end_le_branch_end_of_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete mixed-path tail-dimension increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathTailDim`,
    `higham11_7_tridiagonalBranchAmbientDim_eq_tail_add_offset_succ`,
    `higham11_7_tridiagonalPathPrefixSpan_add_branchAmbientDim_tailDim_eq_pivotSpan_succ`,
    `higham11_7_tridiagonalPath_local_index_lt_pivotSpan_succ`,
    `higham11_7_tridiagonalPathLocalBlockIndex`,
    `higham11_7_tridiagonalPathLocalBlockIndex_val`, and
    `higham11_7_tridiagonalPathTailDim_last_eq_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`
    except `higham11_7_tridiagonalBranchAmbientDim_eq_tail_add_offset_succ`,
    which reports `[propext]`.
  - 2026-07-09 Theorem 11.7 concrete mixed-path tail-dimension recurrence increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathTailDim_head` and
    `higham11_7_tridiagonalPathTailDim_succ`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete mixed-path branch-matrix view increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathBranchMatrix`,
    `higham11_7_tridiagonalPathBranchMatrix_apply`,
    `higham11_7_tridiagonalPathBranchMatrix_abs_entry_le_infNorm`, and
    `higham11_7_tridiagonalPathBranchMatrix_infNorm_le_card_mul_global_infNorm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete scheduled mixed-path endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathLocalBlockIndex_injective`,
    `higham11_7_tridiagonalPathBranchMatrix_infNorm_le_global_infNorm`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`, and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_coeff_roundoff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete prefix-span mixed-path endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_coeff_roundoff_norm` and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_coeff_roundoff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete residual-witness scheduled/prefix endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_scheduled_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`, and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete residual-witness uniform endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm`, and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete last-terminal residual-witness nonuniform endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm` and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete prefix-span uniform-roundoff endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_coeff_norm` and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_coeff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete prefix-span uniform-coefficient endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_local_assumptions_prefix_lifted_sum_zero_offset_of_uniform_coeff_norm` and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_terminal_assumptions_prefix_lifted_sum_zero_offset_of_uniform_coeff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete prefix-span last-terminal endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_uniform_coeff_norm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 last-terminal residual-witness extraction increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathResidualWitnesses_exists_of_init_localAssumptions_last_terminalTailAssumptions` and
    `higham11_7_tridiagonalConcretePathResidualWitnesses_exists_of_init_localAssumptions_last_terminalTailAssumptions`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 branch residual-equation accessor increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchLocalResidualWitness_one_equation`,
    `higham11_7_tridiagonalBranchLocalResidualWitness_two_equation`,
    `higham11_7_tridiagonalBranchLocalResidualWitness_one_equation_lifted`, and
    `higham11_7_tridiagonalBranchLocalResidualWitness_two_equation_lifted`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete path branch residual-witness accessor increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_one_lt_pivotSpan_succ`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_two_lt_pivotSpan_succ`,
    `higham11_7_tridiagonalConcretePathResidualWitnesses_one`, and
    `higham11_7_tridiagonalConcretePathResidualWitnesses_two`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete path lifted residual-equation accessor increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_one`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_two`,
    `higham11_7_tridiagonalConcretePathResidualWitnesses_one_equation_lifted`, and
    `higham11_7_tridiagonalConcretePathResidualWitnesses_two_equation_lifted`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete path lifted first-trailing simplifier increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_one` and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_two`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path lift ordering zero increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_row_lt_start_add_offset`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_of_col_lt_start_add_offset`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_one_row_of_lt`,
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_two_row_of_lt`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path lift column ordering zero increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_one_col_of_lt`
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_apply_pathFirstTrailing_two_col_of_lt`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path lift later-branch sum-zero increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_later_rows_sum_zero`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_later_rows_sum_zero`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_later_cols_sum_zero`,
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_later_cols_sum_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path lift later-branch dot-zero increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_later_rows_dot_sum_zero`
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_later_rows_dot_sum_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path lift full-to-prefix dot increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fin_sum_eq_prefix_add_later`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_prefix_sum`,
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_prefix_sum`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path lift prefix-to-current dot increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fin_sum_prefix_eq_before_add_current`,
    `higham11_7_fin_prefix_dot_eq_before_add_current`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_prefix_rows_dot_eq_before_add_current`,
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_prefix_rows_dot_eq_before_add_current`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path lift full-to-current dot increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_before_add_current`
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_before_add_current`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 local block index range increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLocalBlockIndex_injective`,
    `higham11_7_tridiagonalLocalBlockIndex_val_exists_iff`, and
    `higham11_7_tridiagonalLocalBlockIndex_mem_range_iff`
    → elaborate; theorem axioms `[propext, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 local block row-dot reindexing increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_embedded_row_dot_eq_local`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path current-row dot reindexing increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathLocalBlockIndex_one_lt_pivotSpan_succ`,
    `higham11_7_tridiagonalPathLocalBlockIndex_two_lt_pivotSpan_succ`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_current_rows_dot_eq_local`,
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_current_rows_dot_eq_local`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path before-plus-current dot split increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_before_dot_add_current_dot`
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_before_dot_add_current_dot`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path current-family dot reindexing increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathLocalBlockIndex_rows_dot_eq_local`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_one_eq_pathLocalBlockIndex_cast`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_two_eq_pathLocalBlockIndex_cast`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_current_family_rows_dot_eq_pathLocal`,
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_current_family_rows_dot_eq_pathLocal`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path local-current dot split increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_rows_dot_eq_before_dot_add_current_pathLocal_dot`
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_rows_dot_eq_before_dot_add_current_pathLocal_dot`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path solve-row additive split increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_row_dot_add_family_sum_split`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_solve_row_eq_A_dot_add_before_dot_add_current_pathLocal_dot`,
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_solve_row_eq_A_dot_add_before_dot_add_current_pathLocal_dot`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path solve-row residual-equation lift increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_one_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`
    and
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathFirstTrailing_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 path witness accessor increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalBranchPathSupportedWitnesses_leadingBlockSupport`,
    `higham11_7_tridiagonalBranchPathResidualWitnesses_leadingBlockSupport`,
    `higham11_7_tridiagonalBranchPathSupportedWitnesses_infNorm_bound`, and
    `higham11_7_tridiagonalBranchPathResidualWitnesses_infNorm_bound`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete witness support-family increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_leadingBlockSupport_family`
    and
    `higham11_7_tridiagonalConcretePathResidualWitnesses_leadingBlockSupport_family`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 residual-witness solve-row lift increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathResidualWitnesses_pathFirstTrailing_one_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`
    and
    `higham11_7_tridiagonalConcretePathResidualWitnesses_pathFirstTrailing_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 supported-witness solve-row lift increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathFirstTrailing_one_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`
    and
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathFirstTrailing_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`
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
  - 2026-07-09 Theorem 11.7 mixed-path canonical prefix schedule increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathStartOffsetsFrom_base_add_prefixSpan` and
    `higham11_7_tridiagonalPathStartOffsets_prefixSpan`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 branch endpoint normalization increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathPrefixSpan_branch_end_lt_branch_end_of_lt`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_one_val_eq_branch_end`, and
    `higham11_7_tridiagonalPathFirstTrailingIndex_two_val_eq_branch_end`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 first-trailing row ordering increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_one_val_lt_one_val_of_lt`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_one_val_lt_two_val_of_lt`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_two_val_lt_one_val_of_lt`, and
    `higham11_7_tridiagonalPathFirstTrailingIndex_two_val_lt_two_val_of_lt`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 branch-uniform first-trailing index increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_val`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_val_lt_of_lt`, and
    `higham11_7_tridiagonalPathFirstTrailingIndex_injective`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 first-trailing boundary increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_pos`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_val_le_pivotSpan`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_last_val_eq_pivotSpan`, and
    `higham11_7_tridiagonalPathFirstTrailingIndex_last_eq_finLast`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 first-trailing leading-row exclusion increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_ne_zero` and
    `higham11_7_tridiagonalPath_zero_ne_firstTrailingIndex`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 first-trailing last-row uniqueness increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_eq_finLast_iff` and
    `higham11_7_tridiagonalPathFirstTrailingIndex_ne_finLast_of_ne_last`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 first-trailing strict non-final endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathFirstTrailingIndex_val_eq_pivotSpan_iff`,
    `higham11_7_tridiagonalPathFirstTrailingIndex_val_lt_pivotSpan_of_ne_last`, and
    `higham11_7_tridiagonalPathFirstTrailingIndex_val_lt_pivotSpan_iff_ne_last`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 generic path row-coverage splitter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_forall_of_firstTrailingIndex_and_complement`,
    `higham11_7_tridiagonalPath_forall_of_firstTrailingIndex_zero_and_complement`,
    `higham11_7_tridiagonalPath_forall_of_nonfinal_firstTrailingIndex_last_and_complement`, and
    `higham11_7_tridiagonalPath_forall_of_nonfinal_firstTrailingIndex_last_zero_and_complement`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 branch-uniform endpoint row dispatch increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_firstTrailingIndex_rows_of_one_two` and
    `higham11_7_tridiagonalPath_nonfinal_firstTrailingIndex_rows_of_one_two`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 combined endpoint row coverage increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_forall_of_one_two_nonfinal_firstTrailingIndex_last_and_complement`
    and
    `higham11_7_tridiagonalPath_forall_of_one_two_nonfinal_firstTrailingIndex_last_zero_and_complement`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 terminal/leading row separation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_finLast_ne_zero` and
    `higham11_7_tridiagonalPath_zero_ne_finLast`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 concrete lifted solve-row splitter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_solve_rows_of_one_two_nonfinal_firstTrailingIndex_last_zero_and_complement`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.7 lifted solve-row coverage increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_solve_rows_of_firstTrailingIndex_rows_and_complement`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 split-solve residual-witness endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_split_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 endpoint-local residual-witness endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_local_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 scalar-budget endpoint-local residual-witness endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_local_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 terminal last-row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathResidualWitnesses_finLast_full_solve_row_of_last_pathLocal_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 leading row lift-zero bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathResidualWitnesses_zero_full_solve_row_of_base_row`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 supported terminal/leading row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_finLast_full_solve_row_of_last_pathLocal_rows`
    and
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_zero_full_solve_row_of_base_row`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 terminal/base residual-witness endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 scalar-budget terminal/base residual-witness endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 coefficient-sum terminal/base residual-witness endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot complement row classification increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathSecondPivotIndex_two`,
    `higham11_7_tridiagonalPath_row_eq_zero_or_firstTrailingIndex_or_secondPivot`,
    `higham11_7_tridiagonalPath_complement_eq_secondPivot`,
    `higham11_7_tridiagonalPath_forall_of_one_two_nonfinal_firstTrailingIndex_last_zero_secondPivot`, and
    `higham11_7_tridiagonalPath_solve_rows_of_one_two_nonfinal_firstTrailingIndex_last_zero_secondPivot`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot/first-trailing adjacency increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathSecondPivotIndex_two_val_succ_eq_firstTrailingIndex`,
    `higham11_7_tridiagonalPathSecondPivotIndex_two_val_lt_firstTrailingIndex`, and
    `higham11_7_tridiagonalPathSecondPivotIndex_two_ne_firstTrailingIndex`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot lifted solve-row decomposition increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_current_family_rows_dot_eq_pathLocal`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_solve_row_eq_A_dot_add_before_dot_add_current_pathLocal_dot`,
    `higham11_7_tridiagonalLiftLocalBlockPerturbation_pathSecondPivot_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`,
    `higham11_7_tridiagonalConcretePathResidualWitnesses_pathSecondPivot_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`, and
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathSecondPivot_two_full_solve_row_of_A_dot_add_before_dot_add_current_pathLocal_dot_eq`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot complement solve-row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathResidualWitnesses_complement_full_solve_rows_of_pathSecondPivot_local_rows`
    and
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_complement_full_solve_rows_of_pathSecondPivot_local_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot endpoint solve-row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot uniform endpoint solve-row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot scalar-budget endpoint solve-row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot reduced local-row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_row_dot_zero_of_lt`,
    `higham11_7_tridiagonalConcretePathResidualWitnesses_pathSecondPivot_two_current_local_dot_zero`, and
    `higham11_7_tridiagonalConcretePathResidualWitnesses_secondPivot_local_rows_of_reduced_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 reduced second-pivot combined-row adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_row_dot_add_filtered_family_sum_split`,
    `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_combined_rows`,
    `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_reduced_rows`, and
    `higham11_7_ConcretePathSecondPivotReducedSolveRows_iff_combined_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 combined-row second-pivot witness bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathResidualWitnesses_secondPivot_local_rows_of_combined_rows`,
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_secondPivot_local_rows_of_combined_rows`,
    `higham11_7_tridiagonalConcretePathResidualWitnesses_complement_full_solve_rows_of_pathSecondPivot_combined_rows`, and
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_complement_full_solve_rows_of_pathSecondPivot_combined_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 combined-row second-pivot coefficient endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_combined_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 combined-row second-pivot uniform/scalar endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_combined_solve_rows` and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_combined_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 decomposed branch-matrix second-pivot endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows`
    → elaborate; representative coefficient-sum and scalar-budget endpoint axioms
    `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 branch-matrix full-row-zero source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_earlier_full_row_zero` and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 full-base-row second-pivot coefficient endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 full-base-row second-pivot uniform/scalar endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows` and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 symmetric full-base-row second-pivot endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 pointwise-prefix full-base-row second-pivot endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_each_earlier_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_each_earlier_zero`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 combined-row second-pivot special-case increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_no_two`,
    `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_all_one`, and
    `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_base_rows_of_two_only_at_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 supported reduced second-pivot complement bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_pathSecondPivot_two_current_local_dot_zero`,
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_secondPivot_local_rows_of_reduced_rows`,
    `higham11_7_tridiagonalConcretePathResidualWitnesses_complement_full_solve_rows_of_pathSecondPivot_reduced_rows`, and
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_complement_full_solve_rows_of_pathSecondPivot_reduced_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 coefficient-sum reduced second-pivot endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_reduced_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 uniform reduced second-pivot endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_reduced_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 scalar-budget reduced second-pivot endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_reduced_solve_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 no-second-pivot row-vacuity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_no_two`,
    `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_all_one`, and
    `higham11_7_tridiagonalPath_complement_full_solve_rows_of_no_secondPivot`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 no-second-pivot source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_no_secondPivot`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_no_secondPivot`, and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_no_secondPivot`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 all-one no-second-pivot adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_no_secondPivot_of_all_one`
    → elaborate; no axioms, and
    `higham11_7_tridiagonalPath_complement_full_solve_rows_of_all_one`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 initial second-pivot reduced-row bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_fin_sum_before_eq_zero_of_val_zero`,
    `higham11_7_fin_before_dot_eq_zero_of_val_zero`,
    `higham11_7_ConcretePathSecondPivotReducedSolveRow_of_val_zero`, and
    `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_base_rows_of_two_only_at_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 initial second-pivot coefficient endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_initial_secondPivot_base_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 initial second-pivot uniform-coefficient endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_initial_secondPivot_base_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 initial second-pivot scalar-budget endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_initial_secondPivot_base_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot local/reduced equivalence increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalConcretePathResidualWitnesses_secondPivot_reduced_rows_of_local_rows`
    and
    `higham11_7_tridiagonalConcretePathSupportedWitnesses_secondPivot_reduced_rows_of_local_rows`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 support-level second-pivot local/reduced bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalLeadingBlockSupport_pathSecondPivot_two_current_local_dot_zero`,
    `higham11_7_ConcretePathSecondPivotLocalSolveRows_of_reduced_rows_of_leadingBlockSupport`,
    `higham11_7_ConcretePathSecondPivotReducedSolveRows_of_local_rows_of_leadingBlockSupport`, and
    `higham11_7_ConcretePathSecondPivotReducedSolveRows_iff_local_rows_of_leadingBlockSupport`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 local-block second-pivot combined-row adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalRowDot_eq_localBlock_rowDot_of_zero_outside` and
    `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_zero_outside`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 prefix-zero second-pivot combined-row adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPathLocalBlockIndex_not_exists_iff_lt_prefixSpan`,
    `higham11_7_ConcretePathSecondPivotCombinedRowsZeroOutsideLocalBlock_of_zeroBeforePrefix`, and
    `higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_zeroBeforePrefix`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 second-pivot prefix-zero decomposition increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix_of_each`,
    `higham11_7_ConcretePathSecondPivotCombinedRowsZeroBeforePrefix_of_base_and_earlier_sum_zero`, and
    `higham11_7_ConcretePathSecondPivotCombinedRowsZeroBeforePrefix_of_base_and_each_earlier_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 decomposed local-block second-pivot adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of `_root_`-qualified
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_base_and_earlier_sum_zero` and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_base_and_each_earlier_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 tridiagonal base-zero local-block adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused `_root_`-qualified lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBaseRowsZeroBeforePrefix_of_isTridiagonal`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBaseRowsZeroBeforePrefix_of_isSymTridiagonal`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isTridiagonal_and_earlier_sum_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isTridiagonal_and_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isSymTridiagonal_and_earlier_sum_zero`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_localBlock_rows_of_isSymTridiagonal_and_each_earlier_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 branch-matrix second-pivot local-block adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused `_root_`-qualified lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedLocalBlockSolveRows_of_branchMatrix_rows`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixCombinedLocalBlockSolveRows_iff_localBlock_rows`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_rows_of_isTridiagonal_and_earlier_sum_zero`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_rows_of_isSymTridiagonal_and_each_earlier_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 branch-matrix base-row second-pivot handoff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnCurrentLocalBlock`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixCombinedLocalBlockSolveRows_of_base_rows_and_earlier_local_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_local_zero_and_each_earlier_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 branch-matrix base-row full-row-zero bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isTridiagonal_and_earlier_full_row_zero` and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 full-base-row to branch-matrix second-pivot bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_full_base_rows_of_base_zeroBeforePrefix`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_full_base_rows_of_isTridiagonal`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_full_base_rows_of_isSymTridiagonal`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 full-base-row second-pivot combined handoff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_earlier_local_zero_and_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isSymTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isSymTridiagonal_and_earlier_local_zero_and_each_earlier_zero`
    → elaborate; representative theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 initial-only earlier-lift vacuity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnCurrentLocalBlock_of_two_only_at_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix_of_two_only_at_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_branchMatrix_base_rows_of_isTridiagonal_and_two_only_at_zero`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_two_only_at_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 initial-only full-row earlier-lift vacuity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnFullSecondPivotRow_of_two_only_at_zero` and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_two_only_at_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 full-row earlier-lift zero bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnFullSecondPivotRow`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotEarlierLiftRowsZeroOnCurrentLocalBlock_of_fullSecondPivotRow`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotEarlierLiftRowsSumZeroBeforePrefix_of_fullSecondPivotRow`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isTridiagonal_and_earlier_full_row_zero`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 full-row earlier-lift coefficient endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_earlier_full_row_zero` and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 full-row earlier-lift uniform/scalar endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_earlier_full_row_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 initial-only full-base-row source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_two_only_at_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_two_only_at_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_two_only_at_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 symmetric initial-only full-base-row source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_two_only_at_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_two_only_at_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_full_base_rows_of_isSymTridiagonal_and_two_only_at_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 all-one/no-second-pivot equivalence increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonalPath_all_one_of_no_secondPivot` and
    `higham11_7_tridiagonalPath_no_secondPivot_iff_all_one`
    → elaborate; no extra axioms beyond theorem dependencies.
  - 2026-07-10 Theorem 11.7 all-one source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_all_one`,
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_all_one`, and
    `higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_all_one`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 global base-solve second-pivot adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotFullBaseRows_of_global_base_solve`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_global_base_solve_of_isTridiagonal`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotBranchMatrixBaseLocalBlockSolveRows_of_global_base_solve_of_isSymTridiagonal`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_earlier_local_zero_and_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_earlier_local_zero_and_earlier_sum_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_earlier_local_zero_and_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isTridiagonal_and_two_only_at_zero`, and
    `LeanFpAnalysis.FP.higham11_7_ConcretePathSecondPivotCombinedSolveRows_of_global_base_solve_of_isSymTridiagonal_and_two_only_at_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 global base-solve source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 global base-solve/full-row earlier-lift source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_earlier_full_row_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_earlier_full_row_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 global base-solve/pointwise-prefix source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_each_earlier_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_each_earlier_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 symmetric global base-solve/pointwise-prefix source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_each_earlier_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_each_earlier_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_global_base_solve_of_isSymTridiagonal_and_each_earlier_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.7 branch-matrix full-row-zero budget endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_uniform_coeff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`,
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_earlier_full_row_zero`, and
    `LeanFpAnalysis.FP.higham11_7_tridiagonal_backward_error_interface_of_concrete_path_init_localAssumptions_last_terminal_prefix_lifted_sum_zero_offset_of_residual_witnesses_coeff_roundoff_norm_of_endpoint_terminal_base_secondPivot_branchMatrix_base_rows_of_isSymTridiagonal_and_earlier_full_row_zero`
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
  - 2026-07-10 Theorem 11.3 all-1×1 scalar-budget consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_stored_all_oneByOne_of_uniform_envelope_bound` and
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_all_oneByOne_of_uniform_envelope_bound`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.3 structured factorization-envelope bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound`,
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_nonneg`, and
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.3 structured factorization-envelope norm aggregation increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_with_norm_bounds`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.3 printed first-order source-envelope bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_3_printedFirstOrderBound`,
    `LeanFpAnalysis.FP.higham11_3_printedFirstOrderBound_nonneg`,
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_le_printedFirstOrderBound`, and
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_printed_first_order_bound_with_norm_bounds`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.3 structured product-entry/max-entry bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_eq_epsilon_mul_productEntry`,
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_le_of_productEntry_le`,
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_le_epsilon_mul_productMax`,
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_le_epsilon_mul_maxEntryNorm_absLDLTProduct`, and
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_le_epsilon_mul_higham_product_bound`,
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_higham_product_bound`,
    `LeanFpAnalysis.FP.higham11_3_infNorm_le_card_mul_of_uniform_componentwise_bound`, and
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_higham_product_bound_with_norm_bounds`
    → elaborate; representative theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.3 source-scale product-budget bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_3_blockLDLTBackwardErrorBound_le_pu_higham_product_bound` and
    `LeanFpAnalysis.FP.higham11_3_block_ldlt_backward_error_interface_of_BlockLDLTBackwardError_of_pu_higham_product_bound_with_norm_bounds`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
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
  - 2026-07-10 Theorem 11.8 zero-relative `T_hat` equality adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_zero_relative_T_hat_error_of_eq`,
    `higham11_8_abs_T_le_T_hat_of_eq`, and
    `higham11_8_infNorm_T_le_T_hat_of_eq`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 source-prefix direct norm-cap equality endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_T_hat_eq_T`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` product-size wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_aasen_outer_factor_row_col_sum_majorants_of_AasenSpec_entry_bound`,
    `higham11_8_relative_outer_factor_caps_of_AasenSpec_entry_bound_inv_one_plus`, and
    `higham11_8_aasen_base_square_bounds_of_AasenSpec_entry_bound_inv_one_plus`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` exact-product wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_permuted_product_eq` and
    `higham11_8_AasenSpec_product_eq_of_identity_perm`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity zero-relative checkerboard endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_zero_relative_checkerboard_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity zero-relative direct-middle endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_zero_relative_direct_middle_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` zero-relative inverse-entry endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_zero_relative_direct_middle_endpoint_of_inverse_entry_bound` and
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_zero_relative_checkerboard_endpoint_of_inverse_entry_bound`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity direct-middle `T`-norm endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_direct_middle_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity checkerboard `T`-norm endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_checkerboard_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity componentwise-`T` endpoints increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_direct_middle_endpoint` and
    `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_checkerboard_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity `T_hat=T` endpoints increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_direct_middle_endpoint` and
    `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_checkerboard_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity normalized zero-relative endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_direct_middle_endpoint`,
    `higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_checkerboard_endpoint`,
    `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_direct_middle_endpoint`, and
    `higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_checkerboard_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` normalized zero-relative inverse-entry endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound` and
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_zero_relative_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` identity normalized componentwise/`T`-norm endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_direct_middle_endpoint`,
    `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_direct_middle_endpoint`,
    `higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_checkerboard_endpoint`, and
    `higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_checkerboard_endpoint`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` normalized componentwise/`T`-norm inverse-entry endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_componentwise_T_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound`, and
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` inverse-entry cap helper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_relative_outer_factor_caps_of_AasenSpec_inverse_entry_bound` and
    `LeanFpAnalysis.FP.higham11_8_aasen_base_square_bounds_of_AasenSpec_inverse_entry_bound`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` inverse-entry source-prefix endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_componentwise_T_direct_middle_endpoint_of_inverse_entry_bound`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_direct_middle_endpoint_of_inverse_entry_bound`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_norm_cap_checkerboard_endpoint_of_inverse_entry_bound`, and
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_componentwise_T_checkerboard_endpoint_of_inverse_entry_bound`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` exact-`T_hat` inverse-entry endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_direct_middle_endpoint_of_inverse_entry_bound` and
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_checkerboard_endpoint_of_inverse_entry_bound`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` normalized exact-`T_hat` inverse-entry endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_direct_middle_endpoint_of_inverse_entry_bound` and
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_T_hat_eq_T_scaled_unit_checkerboard_endpoint_of_inverse_entry_bound`
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 exact-`T_hat` smallness-alias increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of the eight `_of_unit_roundoff_bound` and
    `_of_u_le_cap` aliases for the direct/checkerboard exact-`T_hat`
    inverse-entry endpoints, including the normalized scaled-unit variants
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 zero-relative smallness-alias increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of the eight `_of_unit_roundoff_bound` and
    `_of_u_le_cap` aliases for the direct/checkerboard zero-relative
    inverse-entry endpoints, including the normalized scaled-unit variants
    → elaborate; declaration axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 normalized componentwise/`T`-norm smallness-alias increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of the eight `_of_unit_roundoff_bound` and
    `_of_u_le_cap` aliases for the normalized direct/checkerboard
    componentwise-`T` and `T`-norm inverse-entry endpoints → elaborate;
    declaration axioms `[propext, Classical.choice, Quot.sound]`.
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
  - 2026-07-09 Theorem 11.8 checkerboard determinant-inequality middle adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_15_absLU_componentwise_T_bound_of_checkerboard_principalBlock_inequalities`
    and
    `higham11_15_aasenMiddleSolveBudget_infNorm_le_of_checkerboard_principalBlock_inequalities`
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
  - 2026-07-09 Theorem 11.8 source-prefix determinant-inequality zero-relative endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_source_norm_caps_of_zero_relative_T_hat_checkerboard_principalBlock_inequalities`
    and
    `higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_base_square_exact_radius_aasen_outer_factor_entry_bound_inv_one_plus_of_zero_relative_T_hat_checkerboard_principalBlock_inequalities_entry_bound_nonneg`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 printed-radius smallness source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of the supplied and source-prefix
    `_printed_gamma_validity_of_unit_roundoff_bound` and `_printed_gamma_validity_of_u_le_cap`
    endpoint wrappers → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` printed-smallness source endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of the four `AasenSpec` inverse-entry endpoint
    `_of_unit_roundoff_bound` and `_of_u_le_cap` wrappers → elaborate;
    axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 relative `T_hat` source-prefix fallback endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of the short aliases
    `higham11_8_source_prefix_concrete_majorants_of_relative_T_hat` and
    `higham11_8_source_prefix_concrete_majorants_gamma_n_of_relative_T_hat`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` exact-recurrence bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_aasenH_product_eq`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_aasenH_band`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_aasenH_exact_recurrences`,
    and `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_exact_recurrences_of_H_eq`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` subdiagonal pivot bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_aasenH_subdiagonal_eq_T`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_aasenH_exact_recurrences_of_T_subdiagonal_ne_zero`,
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_H_subdiagonal_eq_T_of_H_eq`,
    and `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_exact_recurrences_of_H_eq_T_subdiagonal_ne_zero`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` source-prefix split-entry endpoint increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_split_entry_budgets_printed_gamma_validity`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.8 `AasenSpec` source-prefix split-entry smallness-alias increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom checks of
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_split_entry_budgets_printed_gamma_validity_of_unit_roundoff_bound`
    and
    `LeanFpAnalysis.FP.higham11_8_AasenSpec_identity_source_prefix_split_entry_budgets_printed_gamma_validity_of_u_le_cap`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
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
  - 2026-07-09 Theorem 11.4 first-stage/recursive max-entry solve consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_maxEntryNorm_bounds`
    and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_maxEntryNorm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 row-sum first-stage split bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_first_stage_recursive_product_split_of_row_sum_bounds`,
    `higham11_4_product_entries_of_first_stage_recursive_row_sum_bounds`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_row_sum_bounds`,
    `higham11_4_product_entries_of_first_stage_recursive_higham_const_row_sum_bounds`, and
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_row_sum_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-09 Theorem 11.4 row-sum first-stage scalar/consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_row_sum_bounds`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_row_sum_bounds`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_row_sum_bounds`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_row_sum_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_sum_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_sum_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_sum_maxEntryNorm_bounds`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_sum_maxEntryNorm_bounds`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 uniform row-sum first-stage/recursive adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_product_entries_of_first_stage_recursive_uniform_row_sum_bound`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_row_sum_bound`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_row_sum_bound`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_row_sum_maxEntryNorm_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 exact-budget uniform row-sum first-stage/recursive adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_product_entries_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_row_sum_exact_budgets_maxEntryNorm`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 uniform-entry first-stage/recursive adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_product_entries_of_first_stage_recursive_uniform_entry_bounds`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_entry_bounds`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_entry_bounds`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_entry_maxEntryNorm_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 exact-budget uniform-entry first-stage/recursive adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_product_entries_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_uniform_entry_exact_budgets_maxEntryNorm`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 row-entry first-stage/recursive adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_abs_row_sum_le_card_mul_of_row_entry_bound`,
    `higham11_4_bunchKaufmanProductEntry_le_row_entry_bounds`,
    `higham11_4_bunchKaufmanProductEntry_le_row_entry_bounds_entry_nonneg`,
    `higham11_4_product_entries_of_first_stage_recursive_row_entry_bounds`, and
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_row_entry_bounds`
    → elaborate; representative axiom checks for the row-entry product bridge and exact-coefficient
    scalar certificate report `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 row-entry first-stage/recursive consumer increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_row_entry_bounds`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_row_entry_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_entry_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_bounds`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_row_entry_maxEntryNorm_bounds`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_maxEntryNorm_bounds`
    → elaborate; representative axiom checks for the row-entry stability bridge and exact-coefficient
    max-entry solve bridge report `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 exact-budget row-entry first-stage/recursive adapter increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_product_entries_of_first_stage_recursive_higham_const_row_entry_exact_budgets`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_higham_const_row_entry_exact_budgets`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_higham_const_row_entry_exact_budgets`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_higham_const_row_entry_exact_budgets`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_exact_budgets`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_higham_const_row_entry_exact_budgets_maxEntryNorm`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 uniform six-row-sum/growth-`D` first-stage wrapper increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully`;
    `git diff --check` → pass; placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_first_stage_recursive_uniform_six_rho_budget`,
    `higham11_4_product_entries_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_growth_D_bound`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_growth_D_maxEntryNorm_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 stage-growth `D̂` cap handoff increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `higham11_4_growth_scaled_D_bound_of_le`,
    `higham11_4_product_entries_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`,
    `higham11_4_maxEntryNorm_absLDLTProduct_le_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`,
    `higham11_4_bunchKaufmanMaxEntryProductBound_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`,
    `higham11_4_bunch_kaufman_stability_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`,
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_bound`, and
    `higham11_4_bunch_kaufman_solve_backward_error_of_first_stage_recursive_uniform_six_row_sum_stage_growth_D_maxEntryNorm_bound`
    → elaborate; axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Algorithm 11.2 branch-test and multiplier-cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_noAction_eq_zero`,
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case1_tests`,
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case2_tests`,
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case3_tests`,
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case4_tests`,
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case1_multiplier_bound`, and
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case3_multiplier_bound`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Algorithm 11.2 scalar pivot nonsingularity increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case1_pivot_ne_zero` and
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case3_pivot_ne_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Algorithm 11.2 case-(2) row-maximum bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case2_pivot_bound_of_row_max_le`,
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case2_pivot_ne_zero_of_row_max_le`, and
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case2_multiplier_bound_of_row_max_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Algorithm 11.2 case-(2) source growth increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case2_pivot_ne_zero`,
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case2_schur_correction_bound`, and
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case2_schur_growth`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Algorithm 11.2 scalar-branch growth increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case1_schur_correction_bound`,
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case1_schur_growth`,
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case3_schur_correction_bound`, and
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case3_schur_growth`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Algorithm 11.2 case-(1)/(2) scalar dispatch increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case1_or_case2_pivot_ne_zero_of_row_max_le` and
    `LeanFpAnalysis.FP.higham11_2_bunch_kaufman_case1_or_case2_multiplier_bound_of_row_max_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 local 2×2 multiplier-row cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_twoByTwo_multiplier_row_bound_of_inverse_entries`,
    `LeanFpAnalysis.FP.higham11_4_twoByTwo_multiplier_row_sum_bound_of_inverse_entries`,
    `LeanFpAnalysis.FP.higham11_4_twoByTwo_multiplier_row_bound_of_block`, and
    `LeanFpAnalysis.FP.higham11_4_twoByTwo_multiplier_row_sum_bound_of_block`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 local 2×2 source-six row cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → pass;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_twoByTwo_multiplier_row_sum_const_le_six`,
    `LeanFpAnalysis.FP.higham11_4_twoByTwo_multiplier_row_sum_le_six_of_inverse_entries`, and
    `LeanFpAnalysis.FP.higham11_4_twoByTwo_multiplier_row_sum_le_six_of_block`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(4) local bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_schur_growth_of_row_max_le` and
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_multiplier_row_sum_le_six_of_row_max_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(4) determinant bridge increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_absdet_lower_of_row_max_le` and
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_det_ne_zero_of_row_max_le`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(4) direct determinant increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` → `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_absdet_lower` and
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_det_ne_zero`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(4) scaled inverse increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder scan of `HighamChapter11.lean` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_inverse_scaled_bounds`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(4) direct Schur-growth increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder and tab scans of `HighamChapter11.lean` / `higham_ch11.md` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_schur_correction_bound` and
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_schur_growth`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(4) asymmetric scaled row-sum increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder and tab scans of `HighamChapter11.lean` / `higham_ch11.md` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_multiplier_row_sum_asymmetric_scaled_bound`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(4) pivot-entry cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder and tab scans of `HighamChapter11.lean` / `higham_ch11.md` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case4_twoByTwo_pivot_entries_le_Amax`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
  - 2026-07-10 Theorem 11.4 Algorithm 11.2 case-(2) pivot-entry cap increment:
    `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` → pass;
    `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11` →
    `Build completed successfully (3054 jobs)`;
    `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean docs/source_coverage/higham_ch11.md` → pass;
    placeholder and tab scans of `HighamChapter11.lean` / `higham_ch11.md` → clean;
    focused lookup/axiom check of fully-qualified
    `LeanFpAnalysis.FP.higham11_4_bunch_kaufman_case2_pivot_entry_le_Amax`
    → elaborate; theorem axioms `[propext, Classical.choice, Quot.sound]`.
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
