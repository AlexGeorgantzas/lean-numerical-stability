# Higham Chapter 8 Formalization Report — "Triangular Systems"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 8, "Triangular Systems" (printed pp. 139–154).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch8.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Selected-scope gate: **PASS for the primary-label/equation scope**, with one
  outstanding **policy flag on benchmark-reserved Problems** (see below) that
  needs a coordinator decision but does not affect the primary rows.
  (Certified 2026-07-11, split-2 certification audit — first formal inventory;
  the chapter was formalized before per-chapter reports/gates existed.)

Primary Lean module: `LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
(6.6k lines); proofs in the focused modules TriangularSolve, ForwardSub,
TriangularSolveCombined, TriangularForwardBound, InverseBounds,
TriangularForwardComparison, TriangularArbitraryOrder, TriangularNoGuard,
MMatrix.

## Primary labels (14) — all CLOSED
| Source label | Lean declaration(s) | Notes |
|---|---|---|
| Algorithm 8.1 (back substitution) | `higham8_1_backSub` | wraps `fl_backSub` |
| Lemma 8.2 | `higham8_2_backSub_row_spec`, `higham8_2_backSub_row_tight` | |
| Theorem 8.3 | `higham8_3_backSub_backward_error` | |
| Lemma 8.4 (order-independent) | `higham8_4_anyOrder_backwardError` | |
| Theorem 8.5 | `higham8_5_backSub_backward_error` (+`_anyOrder`, forwardSub variants) | 4 specializations |
| Lemma 8.6 | `higham8_6_inv_abs_mul_bound_diagDom` | |
| Theorem 8.7 | `higham8_7_backSub_forward_error_diagDom` | |
| Lemma 8.8 | `higham8_8_rowDiagDominantUpper_condSkeel_bound` | condSkeel ≤ 2n−1 |
| Lemma 8.9 | `higham8_9_condAtSolution_le_comparisonMatrix` (+ eq/specialization cluster) | |
| Theorem 8.10 | `higham8_10_forwardSub_forward_error_mu_bound` | exact μ recurrence |
| Corollary 8.11 (M-matrix) | `higham8_11_mmatrix_forwardSub_relative_error` | |
| Theorem 8.12 | `higham8_12_abs_inv_le_comparison_inv` + `higham8_12_{infNorm,oneNorm,opNorm2,absolute_norm_vector}_chain`, `higham8_12_comparisonInv_le_WInv`, `higham8_12_WInv_le_ZInvFormula` | |
| Algorithm 8.13 | `higham8_13_inverse_bound_from_comparison` + `higham8_13_mu`/`_y`/recurrence | |
| Theorem 8.14 | `higham8_14_full_norm_chain` + six upper/lower bound pieces | |

## Equations (8.1)–(8.20)
All 20 have Lean surfaces under the `higham8_N_*` convention; (8.2)–(8.7),
(8.9), (8.11)–(8.20) additionally cite "(8.N)" in docstrings. (8.1) is
Algorithm 8.1's display; (8.8) is the row-diagonal-dominance condition
(Prop `higham8_8_rowDiagDominantUpper`); (8.10) is folded into the
Theorem 8.10 surface.

## Naming caveat (informational)
The `higham8_N_` prefix is overloaded across item kinds sharing the number N
(Lemma 8.2 vs eq (8.2) vs Problem 8.2, etc.); only docstrings disambiguate.
No numeric mismatches found: every `higham8_N_*` docstring cites label N.

## Benchmark-reserved — POLICY FLAG (coordinator decision needed)
Pre-existing declarations formalize several end-of-chapter Problems as genuine
exercise content (not general-fact wrappers):
- explicit prefix: `higham8_problem8_1_*` (4 decls, no-guard variants),
  `higham8_problem8_3_*` (1), `higham8_problem8_9_*` (35, Kahan matrix
  second-smallest singular value);
- bare-prefix (docstring-labeled "Problem 8.N"): Problems 8.2, 8.4, 8.5, 8.6,
  8.7, 8.8 under `higham8_N_*` names.

These predate the split project's benchmark-reserved-exercise ban (the ch8
formalization is one of the oldest in the repo). They are recorded here as
identifiers + locations only. **They are NOT counted toward the chapter's
selected-scope coverage above**, and none of the primary rows depends on
them (spot-checked: the primary-label declarations live in the shared
triangular/M-matrix modules or wrap them directly). Options for the
coordinator: (a) grandfather as pre-existing work, (b) quarantine/rename if
the affected Problems are wanted as clean benchmark items. No unilateral
deletion performed.

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| §8.4 numerical experiments, Tables 8.1–8.3 | machine outputs | empirical |
| §8.5 Notes and References, LAPACK notes | history/software | non-mathematical |
| epigraphs, motivating prose | quotations | editorial |

## Verification (2026-07-11 audit)
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`: PASS on current
  `main`.
- Hygiene: no `sorry`/`admit`/`axiom` in `HighamChapter8.lean` or the nine
  support modules.
- `#print axioms` on `higham8_3_*`, `higham8_5_*`, `higham8_7_*`,
  `higham8_10_*`, `higham8_12_infNorm_chain`, `higham8_14_full_norm_chain`:
  `[propext, Classical.choice, Quot.sound]` only.

## Open selected-scope items
None on primary labels/equations. One open policy row: the benchmark-reserved
Problem formalizations flagged above (decision, not proof work).
