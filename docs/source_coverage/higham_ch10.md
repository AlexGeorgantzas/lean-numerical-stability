# Higham Chapter 10 Formalization Report — "Cholesky Factorization"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 10, "Cholesky Factorization" (printed pp. 195–208).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch10.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Planning documents consulted: blueprint, Split 2 section of `split_primary_contracts.md`, `chapter_index.md`.
- Selected-scope gate: PASS. All 14 primary labels, eqs (10.1)–(10.30), and the
  benchmark-reserved Problems are accounted for. Lemma 10.11 is covered in both halves
  (pivot-order preservation and quantitative norm change); see the note under its row
  for the honest-form modeling of the O(‖E‖²) term.

Primary Lean module: `LeanFpAnalysis/FP/Algorithms/HighamChapter10.lean`
(chapter-label surface); reusable proofs in `LeanFpAnalysis/FP/Algorithms/Cholesky/*`.

## Completed selected targets (primary labels)
| Source label | Lean declaration(s) | Notes |
|---|---|---|
| Theorem 10.1 (SPD Cholesky existence+uniqueness) | `higham10_1_cholesky_existence`, `higham10_1_cholesky_uniqueness`, `higham10_1_cholesky_to_ldlt` | eqs (10.1)–(10.3); LDLᵀ rewrite |
| Algorithm 10.2 (Cholesky factorization) | `higham10_2_*` + Cholesky spec modules | kij/sdot forms; solve interface |
| Theorem 10.3 (backward error) | `higham10_3_cholesky_backward_error`, `higham10_3_fl_cholesky_*` | eqs (10.4)(10.5) |
| Theorem 10.4 (solve backward error) | `higham10_4_cholesky_solve_backward_error`, `higham10_4_fl_cholesky_solve_backward_error` | eqs (10.6)(10.7) |
| Theorem 10.5 (Demmel) | `higham10_5_demmel_bound`, `higham10_5_fl_cholesky_demmel_bound`, `higham10_5_demmel_bound_colNorm` | eq (10.8) |
| Theorem 10.6 (Demmel–Wilkinson, scaled error) | `higham10_6_scaled_forward_error*`, `higham10_6_perturbed_solve_forward_error`, `higham10_6_fl_scaled_forward_error*` | eqs (10.9)(10.10) |
| Theorem 10.7 (Demmel, success/failure) | `higham10_7_success_*`, `higham10_7_failure_*`, `higham10_7_fl_cholesky_success*`, `higham10_7_normwise_backward_error*` | λ_min(H) criterion |
| Theorem 10.8 (Sun, sensitivity) | `higham10_8_sun_normwise_perturbation`, `higham10_8_sun_componentwise_perturbation` | |
| Theorem 10.9 (PSD Cholesky existence + pivoted form) | `higham10_9_psd_cholesky_existence`, `higham10_9_spd_pivoted_cholesky_full_rank`, `higham10_9_van_der_sluis`, `higham10_9_*cond_bound` | eq (10.11) |
| Lemma 10.10 (Schur-complement perturbation) | `higham10_10_schur_complement_perturbation` | eqs (10.14)(10.15)(10.16); honest entrywise O(‖E‖²) |
| Lemma 10.11 (cp perturbation) | pivot half: `higham10_11_cp_pivot_sequence_stable` (wraps `cpPivot_sequence_stable_small`); quantitative half: `higham10_11_schur_perturbation_leadingBlock`, `higham10_11_schur_perturbation_opNorm2`, `higham10_11_firstOrder_eq_WtW`, `higham10_11_firstOrder_opNorm2`, `higham10_11_leadingBlockPerturbation_opNorm2` | eq (10.17). Pivot-order preservation: no-ties (gap δ / floor ρ / cap c through r stages) ⇒ ∃ε₀>0 s.t. every A+E within ε₀ picks the same pivot sequence (literal source form). Quantitative: worst-case E=γ·[[I,0],[0,0]] gives S(A+E)=S(A)+γ·WᵀW+R with `opNorm2Le R (poly·γ²·m)`, i.e. the O(‖E‖²) error is controlled in the source's operator 2-norm. See note. |
| Lemma 10.12 (‖A₁₁⁻¹A₁₂‖ bound) | `higham10_12_w_norm_bound_from_cond`, `higham10_12_psd_w_action_bound`, `higham10_12_w_action_norm_bound` | eq (10.18) |
| Lemma 10.13 (Frobenius cp bound) | `higham10_13_complete_pivoting_w_bound`, `higham10_13_pivoted_w_frobenius_bound` | eqs (10.19)(10.20): ‖W‖²_F ≤ (n−r)(4ʳ−1)/3 |
| Theorem 10.14 (PSD backward error) | `higham10_14_psd_cholesky_backward_error`, `higham10_14_fl_psd_cholesky_backward_error` | eqs (10.21)–(10.25) |

## Equations
(10.1)–(10.30) accounted for. Reusable-object equations formalized as defs/theorems:
(10.12) `higham10_12_outerProductResidual`; (10.13) `higham10_13_completePivotingInequality`;
(10.14)/(10.15) `higham10_14_schurComplement`; (10.16) inside `higham10_10_*`;
(10.17) `higham10_11_schur_perturbation_leadingBlock` (worst-case E);
(10.18) counterexample matrix `higham10_18_matrix` / `higham10_18_w_arbitrarily_large`;
(10.20) Kahan-matrix family; (10.26)(10.27)(10.28) termination criteria
`higham10_26_nonpositivePivotCriterion`, `higham10_27_*`, `higham10_28_relativeDiagonalStopCriterion`;
(10.29)(10.30) §10.4 positive-definite-symmetric-part `higham10_29_*`, `higham10_30_complexPositiveDefiniteForm`.

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| §10.1 epigraphs, motivating prose | quotations, motivation | editorial |
| §10.5 Notes and References, §10.5.1 LAPACK | historical / software pointers | non-mathematical |
| "‖W‖ typically < 10 in practice" and similar | empirical observation | empirical, no formalizable subclaim |

## Benchmark-reserved (identifiers only — NOT formalized as chapter work)
Problems 10.1–10.12 and Appendix A solutions 10.1–10.11 are benchmark-reserved.
Some independent, reusable SPD/growth lemmas carry `higham10_problem_10_*` names
(pre-existing); they wrap general SPD facts and are not transcriptions of the
exercise tasks.

## Open selected-scope items (not-proved ledger)
None. All 14 primary labels are formalized.

Note on Lemma 10.11 (honest-form modeling): the pivot-order-preservation half is
proved in literal source form (`higham10_11_cp_pivot_sequence_stable`, wrapping the
recursive complete-pivoting machinery `cpState`/`cpPivot`/`cpPivot_sequence_stable_small`
in `Cholesky/CholeskyPSD.lean`). The quantitative half is proved in two forms:
`higham10_11_schur_perturbation_leadingBlock` gives the exact decomposition
`S(A+E) = S(A) + γ·(A₂₁M²A₁₂) + R` with `R` entrywise `O(γ²)`, and
`higham10_11_schur_perturbation_opNorm2` upgrades that remainder to the source's
**operator 2-norm** (`opNorm2Le R (poly·γ²·m)`, routed through the repository's
`opNorm2`/`opNorm2Le` = mathlib's l2 operator norm). `higham10_11_firstOrder_eq_WtW`
identifies the first-order term as `γ·WᵀW` (`W = M A₁₂`), and
`higham10_11_firstOrder_opNorm2` proves its exact operator 2-norm
`opNorm2 (γ·WᵀW) = γ·‖W‖₂²` (positive-scalar homogeneity + the l2 C*-identity
`Matrix.l2_opNorm_conjTranspose_mul_self`, `Wᴴ = Wᵀ` over ℝ). Thus the source's
`‖S(cp(A+E)) − S(A)‖₂ = ‖W‖₂²‖E‖₂ + O(‖E‖₂²)` is now fully Lean-proved: exact
decomposition, exact leading coefficient `γ‖W‖₂²`, an operator-2-norm `O(γ²)`
remainder, and — via `higham10_11_leadingBlockPerturbation_opNorm2` — the exact
block-perturbation norm `‖E‖₂ = γ` for `E = γ·[[I,0],[0,0]]` (`k>0`, `γ≥0`).
Nothing about Lemma 10.11 remains as an unproven reading.

## Hidden-hypothesis summary
- `higham10_11_schur_perturbation_leadingBlock`: leading-block inverse data enters
  via genuine equations `M·A₁₁=1`, `(A₁₁+γI)·X=1` (not assumed bounds on the
  conclusion); entrywise bounds α,μ,χ are on the *data*, and the O(γ²) remainder is
  derived, not assumed.
- `higham10_11_firstOrder_eq_WtW`: assumes symmetry `A₂₁=A₁₂ᵀ`, `Mᵀ=M` — true in
  the SPD/PSD setting; does not assume the target.

New Lemma-10.11 declarations added at the chapter surface this session:
`higham10_11_schur_perturbation_leadingBlock`, `higham10_11_schur_perturbation_opNorm2`,
`higham10_11_firstOrder_eq_WtW`, `higham10_11_firstOrder_opNorm2`, `higham10_11_leadingBlockPerturbation_opNorm2` (quantitative half),
and `higham10_11_cp_pivot_sequence_stable` (thin wrapper over the pre-existing
`cpPivot_sequence_stable_small`). No duplicate parallel API: the recursive
complete-pivoting proofs and the `opNorm2Le` machinery are reused from
`Cholesky/CholeskyPSD.lean` and `Analysis/MatrixAlgebra.lean`.

## Verification
- Commands:
  - `lake exe cache get`
  - `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter10` → `Build completed successfully (3053 jobs)`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter10.lean` → exit 0 (no errors).
  - `#print axioms` on the new quantitative theorems (`…leadingBlock`, `…opNorm2`, `…firstOrder_eq_WtW`) → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms).
  - Placeholder scan `grep -nE 'sorry|admit|^\s*axiom |native_decide'` over ch10 + `Cholesky/` → clean.
- New vs pre-existing warnings: no new errors; only pre-existing deprecation/linter warnings
  (`Fin.coe_castAdd`/`Fin.coe_natAdd`, an unused-simp-arg hint, one unused variable).

## Documentation
- Inventory + report: `docs/source_coverage/higham_ch10.md` (this file).
- Not-proved ledger: empty (no open selected-scope rows).

## Open issues
- None. All 14 primary labels are formalized; Lemma 10.11's O(‖E‖²) quantitative half
  uses the same entrywise-honest modeling convention as Lemma 10.10 (noted above).
