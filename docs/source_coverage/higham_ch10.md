# Higham Chapter 10 Formalization Report — "Cholesky Factorization"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 10, "Cholesky Factorization" (printed pp. 195–208).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch10.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Planning documents consulted: blueprint, Split 2 section of `split_primary_contracts.md`, `chapter_index.md`.
- Selected-scope gate: **PASS / SOURCE-DISCREPANCY** under the fresh strict
  source-strength audit completed 2026-07-19.  Every precise true selected row
  now has a source-facing producer.  The printed normwise clause of Theorem
  10.8 is false under its stated hypotheses and is closed by a checked
  counterexample plus the missing-domain correction; its independent
  componentwise clause is proved.  Theorem 10.14's unparameterized `O(u^2)`
  display is `DEFER-MISSING-PRECISE-STATEMENT` under the audit skill rather
  than an invented quantitative target.

Primary Lean module: `NumStability/Algorithms/HighamChapter10.lean`
(chapter-label surface); reusable proofs in `NumStability/Algorithms/Cholesky/*`.

## Completed selected targets (primary labels)
| Source label | Lean declaration(s) | Notes |
|---|---|---|
| Theorem 10.1 (SPD Cholesky existence+uniqueness) | `higham10_1_cholesky_existence`, `higham10_1_cholesky_uniqueness`, `higham10_1_cholesky_to_ldlt` | eqs (10.1)–(10.3); LDLᵀ rewrite |
| Algorithm 10.2 (Cholesky factorization) | `higham10_2_*` + Cholesky spec modules | kij/sdot forms; solve interface |
| Theorem 10.3 (backward error) | `higham10_3_cholesky_backward_error`, `higham10_3_fl_cholesky_*` | eqs (10.4)(10.5) |
| Theorem 10.4 (solve backward error) | `higham10_4_cholesky_solve_backward_error`, `higham10_4_fl_cholesky_solve_backward_error` | eqs (10.6)(10.7) |
| Theorem 10.5 (Demmel) | `higham10_5_demmel_bound`, `higham10_5_fl_cholesky_demmel_bound`, `higham10_5_demmel_bound_colNorm` | eq (10.8) |
| Theorem 10.6 (Demmel–Wilkinson, scaled error) | `higham10_6_actual_source_closed` in `Ch10ActualSourceClosure.lean`, plus the reusable `higham10_6_*` interfaces | **PASS at actual-algorithm strength**: from an SPD input, a successful concrete `fl_cholesky` run, the two literal rounded triangular solves, and the printed smallness condition, the theorem constructs the factorization/solve perturbation and scaled inverse-action bounds internally and returns the displayed scaled forward-error bound. |
| Theorem 10.7 (Demmel, success/failure) | `higham10_7_fl_cholesky_success_source`, `higham10_7_actual_algorithm_source_closed` in `Cholesky/Higham10Theorem10_7Source.lean`, plus the earlier `higham10_7_*` interfaces | **PASS at printed sharp strength**: from exactly `nγ_{n+1}/(1-γ_{n+1}) < λ_min(H)`, the source theorem constructs positivity of every concrete `fl_cholesky` pivot and proves the computed upper-triangular factor has unit determinant. No caller-supplied run or stage certificate is assumed. |
| Theorem 10.8 (Sun, sensitivity) | normwise source audit `higham10_8_printed_normwise_p2_source_discrepancy`, `..._factor_source_discrepancy` in `Ch10Theorem108Source.lean`; componentwise source closure `higham10_8_componentwise_source_nonsingInv` in `Ch10Theorem108Componentwise.lean` | **PASS / SOURCE-DISCREPANCY.** The source defines `epsilon = ‖Delta A‖_F/‖A‖_2` and prints a denominator `1-kappa_2(A) epsilon`, while assuming only `‖A⁻¹ Delta A‖_2<1`.  The checked diagonal example `A=diag(1,1/4)`, `Delta A=diag(1/2,0)` satisfies the printed existence/smallness hypotheses but has `kappa_2(A) epsilon=2`, so the printed RHS is negative.  The missing meaningful-domain condition `kappa_2(A) epsilon<1` is proved necessary/nonnegative.  Independently, the complete componentwise theorem constructs `Rhat⁻¹`, the normalized triangular factor, its inverse transpose, the Gram identity, and the nonnegative resolvent majorant from exactly the two Cholesky factorizations and `rho(|Gtilde|)<1`; no desired bound is assumed. |
| Theorem 10.9 (PSD Cholesky existence + pivoted form) | `higham10_9_psd_cholesky_existence`, `higham10_9_psd_pivoted_cholesky_rank`, `higham10_9_pivoted_cholesky_unique`, `higham10_9_psd_pivoted_cholesky_rank_unique`, `higham10_9_spd_pivoted_cholesky_full_rank`, `higham10_9_van_der_sluis`, `higham10_9_*cond_bound` | **CLOSED**: 10.9(a) is represented. `higham10_9_psd_pivoted_cholesky_rank` assembles the reusable constructive complete-pivoting certificate with the proved matrix-rank identification. `higham10_9_pivoted_cholesky_unique` proves uniqueness for the selected permutation/rank directly from positive leading pivots and zero trailing rows, and `..._rank_unique` packages the full 10.9(b) existence/rank/uniqueness statement. |
| Lemma 10.10 (Schur-complement perturbation) | `higham10_10_schur_complement_perturbation` | eqs (10.14)(10.15)(10.16); honest entrywise O(‖E‖²) |
| Lemma 10.11 (cp perturbation) | `Higham10_11NoTies`, `higham10_11_finite_noTies_gap_floor_cap`, `higham10_11_cp_pivot_sequence_stable_of_noTies_two_sided`, and signed quantitative endpoints in `Ch10Lemma1011Source.lean` | **PASS.** Finiteness turns the printed no-ties/nonbreakdown assumptions into the uniform positive gap, pivot floor, and finite cap internally.  A positive perturbation radius then preserves every first-`r` pivot for both `A+E` and `A-E`.  The signed Schur expansion retains the sign of the first-order term and bounds its operator-2-norm remainder quadratically. |
| Lemma 10.12 (‖A₁₁⁻¹A₁₂‖ bound) | `higham10_12_w_norm_bound_from_cond`, `higham10_12_psd_w_action_bound`, `higham10_12_w_action_norm_bound` | eq (10.18) |
| Lemma 10.13 (Frobenius cp bound) | `higham10_13_complete_pivoting_w_bound`, `higham10_13_pivoted_w_frobenius_bound`, `higham10_13_kahan_source_closed` in `Ch10KahanSharpnessSource.lean` | **PASS.** The Kahan rank-`r` complete-pivoted Gram family, its `W=A11⁻¹A12` identity, and both operator-2/Frobenius limiting norms are constructed, proving the printed constant sharp in the limit. |
| Theorem 10.14 (PSD backward error) | existing conditional/all-orders infrastructure `higham10_14_*` | **DEFER-MISSING-PRECISE-STATEMENT.** The printed conclusion contains an unparameterized `O(u²)` remainder and does not specify a remainder function, neighborhood, or constant.  The audit skill expressly forbids selecting an arbitrary completion.  Existing exact all-orders/as-run interfaces remain useful but are not misreported as the literal Landau statement. |

## Equations
(10.1)–(10.30) accounted for. Reusable-object equations formalized as defs/theorems:
(10.12) `higham10_12_outerProductResidual`; (10.13) `higham10_13_completePivotingInequality`;
(10.14)/(10.15) `higham10_14_schurComplement`; (10.16) inside `higham10_10_*`;
(10.17) `higham10_11_schur_perturbation_leadingBlock` (worst-case E);
(10.18) counterexample matrix `higham10_18_matrix` / `higham10_18_w_arbitrarily_large`;
(10.20) Kahan-matrix family; (10.26)(10.27)(10.28) termination criteria
`higham10_26_nonpositivePivotCriterion`, `higham10_27_*`, `higham10_28_relativeDiagonalStopCriterion`;
(10.29)(10.30) §10.4 positive-definite-symmetric-part `higham10_29_*`,
with literal operator-norm endpoint
`higham10_29_source_lu_growth_bound_opNorm2`, and
`higham10_30_complexPositiveDefiniteForm`.

### Post-(10.30) complex-symmetric growth and rounded-stability audit

The printed hypothesis has now been source-corrected to require **both** real
and imaginary parts to be real symmetric positive definite. The source-facing
closure in `Ch10ComplexPositiveDefiniteSourceClosure.lean` proves internally:
nonsingularity and all leading principal minors, existence of exact no-pivot
LU, a source-derived elimination/Schur trace, and the exact max-entry growth
bound `rho_n < 3`. No success, trace, or growth premise is supplied by the
caller. The tempting weakening in which the imaginary part is merely
symmetric is refuted by a checked `2 x 2` example with growth `17/4 > 3`.

The final printed sentence on p. 209 is qualitative: after stating `rho_n < 3`
it says only that no-pivot LU is "perfectly normwise backward stable"; it gives
no rounded executor or perturbation constant there. A literal real-component
complex Doolittle executor is now formalized. The theorem
`higham10_30_literalComplexGE_gamma_n_certificate_source_discrepancy` proves
that importing the real Theorem-9.3 radius `gamma_n` verbatim is false for that
model: an admissible `n = 2`, `u = 1/10` execution with both parts SPD and
`gammaValid` needs certificate radius at least `40/121`, while `gamma_2 = 1/4`.
The older certificate-to-backward-error theorem remains explicitly conditional
and is no longer reported as a literal rounded source closure.

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

There are no open precise selected-scope rows.  The only non-theorem terminal
dispositions are explicit and auditable:

- **Theorem 10.8 normwise display — SOURCE-DISCREPANCY.** The literal statement
  is false; `Ch10Theorem108Source.lean` supplies a complete factor-level
  counterexample and proves the omitted `κ₂(A)ε < 1` domain condition is what
  makes the displayed rational radius meaningful.  The independent
  componentwise clause is fully proved in `Ch10Theorem108Componentwise.lean`.
- **Theorem 10.14 / equation (10.22) — DEFER-MISSING-PRECISE-STATEMENT.** Its
  `O(u²)` term has no source-specified remainder object or constant.  Choosing
  one would invent a theorem rather than formalize the printed claim.

Note on Lemma 10.11 (honest-form modeling): the pivot-order-preservation half is
proved in literal source form.  `higham10_11_finite_noTies_gap_floor_cap`
constructs the former auxiliary gap/floor/cap data from the printed finite
no-ties/nonbreakdown assumptions, and
`higham10_11_cp_pivot_sequence_stable_of_noTies_two_sided` applies the recursive
complete-pivoting machinery to both signs of the perturbation. The quantitative
half is proved in signed forms:
`higham10_11_schur_perturbation_leadingBlock` gives the exact decomposition
`S(A+E) = S(A) + γ·(A₂₁M²A₁₂) + R` with `R` entrywise `O(γ²)`, and
`higham10_11_schur_perturbation_opNorm2` upgrades that remainder to the source's
**operator 2-norm** (`opNorm2Le R (poly·γ²·m)`, routed through the repository's
`opNorm2`/`opNorm2Le` = mathlib's l2 operator norm). `higham10_11_firstOrder_eq_WtW`
identifies the first-order term as `γ·WᵀW` (`W = M A₁₂`), and
`higham10_11_firstOrder_opNorm2` proves its exact operator 2-norm
`opNorm2 (γ·WᵀW) = γ·‖W‖₂²` (positive-scalar homogeneity + the l2 C*-identity
`Matrix.l2_opNorm_conjTranspose_mul_self`, `Wᴴ = Wᵀ` over ℝ). Thus the source's
first-order statement has an exact decomposition, exact leading coefficient,
and operator-2-norm quadratic remainder with the correct signed perturbation.

## Hidden-hypothesis summary
- The legacy `higham10_8_sun_*` wrappers do contain target-shaped premises,
  but they are no longer the source-facing closure surface.  The new normwise
  discrepancy and componentwise resolvent theorems do not use them.
- The legacy `higham10_14_*` interfaces retain target-shaped premises and are
  not counted as proof of the printed Landau statement; that source statement
  is deferred for lack of a precise remainder.
- The older `higham10_7_fl_cholesky_success_sharp` strengthened the source
  threshold.  It is superseded for gate purposes by
  `higham10_7_actual_algorithm_source_closed`, whose assumptions are exactly
  the printed threshold and natural algorithm-domain conditions.
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
  - `lake build NumStability.Algorithms.HighamChapter10` → `Build completed successfully (3053 jobs)`.
  - `lake env lean NumStability/Algorithms/HighamChapter10.lean` → exit 0 (no errors).
  - `#print axioms` on the new quantitative theorems (`…leadingBlock`, `…opNorm2`, `…firstOrder_eq_WtW`) and the 10.9(b) rank/uniqueness assembly → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms).
  - Placeholder scan `grep -nE 'sorry|admit|^\s*axiom |native_decide'` over ch10 + `Cholesky/` → clean.
- New vs pre-existing warnings: no new errors; only pre-existing deprecation/linter warnings
  (`Fin.coe_castAdd`/`Fin.coe_natAdd`, an unused-simp-arg hint, one unused variable).

## Documentation
- Inventory + report: `docs/source_coverage/higham_ch10.md` (this file).
- Open selected-scope ledger: the explicit list above; no separate ledger file.

## Open issues

None in the precise selected scope.  Future work may choose and document an
explicit quantitative interpretation of Theorem 10.14's `O(u²)` remainder,
but that would be a strengthening beyond the determinate source text and is
not required for this gate.
