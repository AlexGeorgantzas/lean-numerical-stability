# Higham Chapter 10 Formalization Report — "Cholesky Factorization"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 10, "Cholesky Factorization" (printed pp. 195–208).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch10.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Planning documents consulted: blueprint, Split 2 section of `split_primary_contracts.md`, `chapter_index.md`.
- Selected-scope gate: PASS. All 14 primary labels have a formalized surface; the only
  residual is the pivot-order-preservation half of Lemma 10.11, recorded below as a
  bounded, honestly-scoped open foundation (its quantitative conclusion is formalized).

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
| Lemma 10.11 (cp perturbation — quantitative half + pivot-stability core) | `higham10_11_schur_perturbation_leadingBlock`, `higham10_11_firstOrder_eq_WtW`, `higham10_11_pivot_argmax_stable` | eq (10.17): worst-case E=γ·[[I,0],[0,0]] norm change = ‖W‖²‖E‖+O(‖E‖²); plus the no-ties argmax-stability core. Only the `cp`-operator assembly OPEN (see below). |
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
| Source location | Exact claim | Current Lean status | Missing foundation | Smallest next Lean theorem |
|---|---|---|---|---|
| Lemma 10.11, first part (p. 204) | For A=cp(A) with no pivot ties (10.17) and small ‖E‖: A+E=cp(A+E) with the same pivot permutation | PARTIAL — argmax-stability core proved (`higham10_11_pivot_argmax_stable`); cp-operator assembly OPEN | complete-pivoting operator `cp(·)=ΠᵀAΠ` (recursive argmax pivot selection) + continuity of the stage Schur diagonal, chaining `higham10_11_pivot_argmax_stable` across all `r` stages | `cp` operator def + `cp_permutation_preserved` (same Π for `A` and `A+E` when ‖E‖ ≤ δ), then combine with `higham10_11_schur_perturbation_leadingBlock` |

The *quantitative* conclusion of Lemma 10.11 (the norm-change identity for the
displayed worst-case E) is closed by `higham10_11_schur_perturbation_leadingBlock`
+ `higham10_11_firstOrder_eq_WtW` via Lemma 10.10. The pivot-order-preservation
half now has its mathematical core proved (`higham10_11_pivot_argmax_stable`:
strict argmax survives small perturbations, i.e. condition (10.17) ⇒ unchanged
pivot choice); the remaining work is defining the `cp` operator and chaining the
stability across the `r` pivoting stages.

## Hidden-hypothesis summary
- `higham10_11_schur_perturbation_leadingBlock`: leading-block inverse data enters
  via genuine equations `M·A₁₁=1`, `(A₁₁+γI)·X=1` (not assumed bounds on the
  conclusion); entrywise bounds α,μ,χ are on the *data*, and the O(γ²) remainder is
  derived, not assumed.
- `higham10_11_firstOrder_eq_WtW`: assumes symmetry `A₂₁=A₁₂ᵀ`, `Mᵀ=M` — true in
  the SPD/PSD setting; does not assume the target.

## Verification
- Commands:
  - `lake exe cache get`
  - `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter10` → `Build completed successfully (3053 jobs)`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter10.lean` → exit 0 (no errors).
  - `#print axioms` on both new theorems → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms).
  - Placeholder scan `grep -nE 'sorry|admit|^\s*axiom |native_decide'` over ch10 + `Cholesky/` → clean.
- New vs pre-existing warnings: no new errors; only pre-existing deprecation/linter warnings
  (`Fin.coe_castAdd`/`Fin.coe_natAdd`, an unused-simp-arg hint, one unused variable).

## Documentation
- Inventory + report: `docs/source_coverage/higham_ch10.md` (this file).
- Not-proved ledger: the single open row above (Lemma 10.11 pivot-order half).

## Open issues
- None blocking. The cp-operator foundation for Lemma 10.11's pivot-order half is the
  next foundational target for fully closing that lemma.
