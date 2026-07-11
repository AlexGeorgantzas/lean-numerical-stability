# Higham Chapter 12 Formalization Report — "Iterative Refinement"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 12, "Iterative Refinement" (printed pp. 231–242).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch12.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Selected-scope gate: **PASS** (closed 2026-07-05 by the ch12 session, commit
  `d67b6a1b` "fully solver-derived Theorem 12.4"; this report written 2026-07-11
  during the split-2 certification audit, after independently re-verifying the
  build, hygiene, and axioms on current `main`).

Primary Lean module: `LeanFpAnalysis/FP/Algorithms/HighamChapter12.lean`
(chapter-label surface); reusable one-step refinement proofs in
`LeanFpAnalysis/FP/Algorithms/IterativeRefinement.lean`.

## Primary labels (4)
| Source label | Status | Lean declaration(s) | Notes |
|---|---|---|---|
| Theorem 12.1 (mixed precision iterative refinement) | SKIP (qualitative) with exact core CLOSED | `higham12_forward_error_linear_contraction`, `higham12_forward_error_steady_state`, `higham12_5_forward_error_identity`, `higham12_5_forward_error_bound` | The printed statement is qualitative ("reduces the forward error by a factor **approximately** η at each stage, until ‖x−x̂‖/‖x‖ **≈** u"). The precise mathematical content — the affine error recurrence (12.3)–(12.5) and its geometric-contraction consequence — is proved exactly; the approximate envelope has no formalizable sharp form. |
| Theorem 12.2 (fixed precision iterative refinement) | SKIP (qualitative) with exact core CLOSED | same skeleton as 12.1 (contraction with `η`, steady state `≲ 2n·cond(A,x)u`) | Same qualitative caveat ("approximately", "≲"). |
| Theorem 12.3 (one-step refinement backward error, eq (12.10)) | CLOSED | `higham12_3_exact_one_step_residual_bound` | Proved in exact (non-asymptotic) form: the printed `+uq`, `q = O(u)` tail is carried as the exact residual expression rather than an asymptotic remainder. Hypotheses are the solver model (12.7), residual model (12.8), and rounded update (12.13). |
| Theorem 12.4 (refinement ⇒ componentwise backward stability) | CLOSED | `higham12_4_from_solver` (headline), `higham12_4_conditional_two_gamma_bound`, `higham12_4_explicit_condition`; engine `correction_neumann_inequality` (IterativeRefinement) | Fully solver-derived: `|b−Aŷ|ᵢ ≤ 2γ_{n+1}(|A||ŷ|+|b|)ᵢ` with the correction bound DERIVED from the solver model via the exact componentwise Neumann inequality (12.18)/(12.20) — not assumed. Explicit precise hypotheses: solver/residual/update models, nonnegative `|A⁻¹|` resolver, row-sum contraction `c = μ‖|A||A⁻¹|‖ < 1`, scalar side conditions. |

## Equations (12.1)–(12.22)
- Direct surfaces: (12.1) `higham12_1_SolverWBound`; (12.2) `higham12_2_residual_delta_bound`;
  (12.3)–(12.5) `higham12_3_exact_one_step_residual_bound`, `higham12_5_forward_error_identity`/`_bound`,
  contraction skeleton `higham12_forward_error_*`; (12.7) `higham12_7_initialResidualBound`;
  (12.8) `higham12_8_residualComputationBound`; (12.9) `higham12_9_conventional_residual_error`;
  (12.14) `higham12_14_residual_identity`/`_bound`; (12.17) `higham12_17_update_bound`/`_div`;
  (12.18) `higham12_18_residual_abs_bound`; (12.19) `higham12_19_combined_coefficients`;
  (12.20) `higham12_20_correction_via_resolver`; (12.21) `higham12_21_correction_product_bound`/`_infNorm_bound`;
  (12.22)/σ `higham12_22_infNorm_skew_apply`, `higham12_vectorAbsSkew_*`.
- (12.6) `uW ≡ γ₃ₙ|L̂||Û|`: REUSE_EXISTING — the LU instantiation of the solver
  model (12.1), supplied by Chapter 9's Theorem 9.4 surfaces (`higham9_4_*`).
- (12.10): the display of Theorem 12.3's conclusion — covered by that row.
- (12.11)–(12.13), (12.15), (12.16): proof-internal displays of Theorems
  12.3/12.4 (residual/solve/update instantiations and two substitution steps);
  represented inside the Lean proofs of the rows above rather than as
  standalone labels.

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| Thm 12.1/12.2 printed envelopes | "approximately η", "until ≈ u", "≲ 2n cond(A,x)u" | qualitative/asymptotic; exact cores proved (see table) |
| §12.3 (LAPACK usage), §12.4 Notes and References | software/history | non-mathematical |
| G_i/g_i "≈/≲" estimates after (12.5) | first-order heuristics | qualitative; exact recurrence proved |

## Benchmark-reserved
Problems 12.1–12.5 and Appendix A solution rows: identifiers only, not
formalized as chapter work. **Flag:** the pre-existing declaration
`higham12_problem_12_1_square` (HighamChapter12.lean) proves the σ-dominance
inequality `|A||x| ≤ σ‖A‖∞|x|` in dimension-compatible square form and is used
as infrastructure for the σ bridge of Theorem 12.4. The same inequality is the
content of the chapter's σ definition (§12.2, before Thm 12.4), so the fact
itself is in-scope chapter mathematics; the *name* advertises a
benchmark-reserved identifier. Recorded for a coordinator decision (rename to a
`higham12_sigma_*` name vs. grandfather); the declaration wraps a general fact
and does not transcribe the exercise text.

## Verification (2026-07-11 audit)
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter12`: PASS (3373 jobs) on
  `main` @ `e4bd6f2c` era; only pre-existing deprecation warnings.
- Hygiene: no `sorry`/`admit`/`axiom`/`unsafe` in `HighamChapter12.lean`.
- `#print axioms` on `higham12_3_exact_one_step_residual_bound`,
  `higham12_4_from_solver`, `higham12_5_forward_error_identity`,
  `higham12_forward_error_linear_contraction`:
  `[propext, Classical.choice, Quot.sound]` only.

## Open selected-scope items
None.
