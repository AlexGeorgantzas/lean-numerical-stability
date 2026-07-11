# Higham Chapter 7 Formalization Report — "Perturbation Theory for Linear Systems"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 7, "Perturbation Theory for Linear Systems" (printed pp. 119–133).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7–12).
- Selected-scope gate: **PASS** (certified 2026-07-11, split-2 certification
  audit). The chapter was formalized before the split project introduced
  per-chapter reports/gates; this report is the first formal inventory and was
  produced by mapping every contract label to its Lean surface, verifying the
  build, hygiene, and axioms on current `main`, and adding two thin
  source-labeled aliases for Theorem 7.8 (see below).

Primary Lean module: `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
(~26k lines, ~884 declarations); heavy perturbation proofs in
`LeanFpAnalysis/FP/Analysis/PerturbationTheory.lean`.

## Primary labels (9)
| Source label | Status | Lean declaration(s) | Notes |
|---|---|---|---|
| Theorem 7.1 (Rigal–Gaches, normwise backward error, eqs (7.1)–(7.3)) | CLOSED | `theorem7_1_subordinate` (+`_necessary`/`_sufficient`); core `rigal_gaches` (PerturbationTheory); attaining perturbations `eq_7_3_subordinate_attaining_perturbations` | |
| Theorem 7.2 (normwise forward error, eq (7.4)) | CLOSED | `theorem7_2_subordinate_forward_error_bound` | |
| Theorem 7.3 (Oettli–Prager, componentwise backward error, eqs (7.7)–(7.9)) | CLOSED | `oettli_prager` (+`_necessary`/`_sufficient`, PerturbationTheory) | docstrings cite "Higham Theorem 7.3" |
| Theorem 7.4 (componentwise forward error, eq (7.10)) | CLOSED | `theorem7_4_absolute_forward_error_bound`; componentwise core in PerturbationTheory | |
| Theorem 7.5 (van der Sluis, column/row equilibration near-optimality) | CLOSED | `theorem7_5_p1_column_equilibration_isLeast_right_scalings`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_*`, `theorem7_5_pinf_row_*` family | large family; supported by `eq_7_18`/`eq_7_20`/`eq_7_21` |
| Corollary 7.6 | CLOSED | `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings` + `corollary7_6_cholesky_*` family | |
| Theorem 7.7 (Stewart–Sun, Frobenius scaling) | CLOSED | `theorem7_7_stewart_sun_frobenius_scaling` (+`_of_left_inverse`, lower bound) | |
| Theorem 7.8 (Bauer, two-sided scaling, eq (7.24)) | CLOSED | aliases `theorem7_8_bauer_scaledInfCondSet_sInf_eq_spectralRadius`, `theorem7_8_bauer_scaledInfKappaSet_sInf_eq_spectralRadius` (added 2026-07-11) of `problem7_10a/b_irreducible_products_*_sInf_eq_spectralRadius` | The book proves Theorem 7.8 by "Proof. See Problem 7.10", so the full formalization legitimately lives in the `problem7_10*` family (irreducible-products form, Perron vector produced from irreducibility). The aliases give the primary label its own traceable surface. Infimum (`sInf`) form matches Rump's remark and specializes to the printed minimum under the attainment lemmas in the same family. |
| Lemma 7.9 (practical error bounds, eqs (7.28)–(7.29)) | CLOSED | `lemma7_9_componentwise_bound`, `lemma7_9_relative_infNorm_bound`, `lemma7_9_exact_for_residual_multiple` | neighbors `eq_7_30`, `eq_7_31` |

## Equations (7.1)–(7.33)
- Direct/labeled surfaces (24): (7.3), (7.4), (7.5), (7.9)–(7.16), (7.18)–(7.23),
  (7.25), (7.26), (7.28)–(7.31), (7.33) — via `eq_7_N*` declarations or
  docstring-cited surfaces in the two chapter files.
- (7.1), (7.2): the η definition and formula — inside Theorem 7.1's statement
  (covered by that row).
- (7.7), (7.8): the ω definition and formula — inside Theorem 7.3's statement
  (covered by that row).
- (7.24): Theorem 7.8's display (covered by that row).
- (7.27): §7.7 restatement of (7.2)+(7.8) — REUSE_EXISTING (same content as the
  Theorem 7.1/7.3 formulas).
- (7.6): a MATLAB experiment output (`1.00×10⁻¹⁰`) — SKIP (empirical).
- (7.17): the Kahan 3×3 ε-example illustrating `cond(A,x) ≪ cond(A) ≪ κ∞(A)` —
  SKIP (illustrative example; the phenomenon's quantitative content is the
  proved cond/κ surfaces (7.13)–(7.16)).
- (7.32): §7.8 "perturbation theory by calculus" first-order bound — SKIP
  (methodological aside; the book itself prefers the algebraic route, whose
  rigorous forms are Theorems 7.2/7.4, both closed).

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| epigraphs, §7.1/§7.2 numerical examples, (7.6), (7.17) | MATLAB experiments, illustrations | empirical/illustrative |
| §7.5 Extensions | survey of νₚ-measure, multiple-RHS, structured variants | survey prose; no owned primary label |
| §7.6 Numerical Stability | informal stability definitions, Table 7.2 | definitional prose (informal by the book's own choice) |
| (7.32), §7.8 | calculus derivation sketch | methodological aside |
| §7.9 Notes and References | history | non-mathematical ((7.33) `Pe = e` has a Lean surface: `IsStochasticMatrix`/`stochasticMatrix_mul_ones`) |

## Benchmark-reserved
Contract problem ledger for ch7: 7.1–7.6, 7.10–7.14 (benchmark-reserved).
Pre-existing `problem7_*` declarations exist throughout the chapter file
(~150, covering 7.1–7.11, 7.13, 7.15). Sampled docstrings uniformly wrap
general facts/building blocks and do not transcribe exercise statements.
Note: Problems 7.7, 7.8, 7.9, 7.15 are NOT in the reserved ledger, so their
surfaces are unrestricted. The `problem7_10*` family doubles as the proof of
primary Theorem 7.8 because the book delegates that proof to Problem 7.10;
this is recorded here as sanctioned overlap, now fronted by `theorem7_8_*`
aliases. These declarations predate the benchmark policy; recorded for
coordinator awareness, no action required.

## Verification (2026-07-11 audit)
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`: PASS on current
  `main`; aliases type-checked and rebuilt.
- Hygiene: no `sorry`/`admit`/`axiom` in `HighamChapter7.lean` or
  `PerturbationTheory.lean`.
- `#print axioms` on the nine headline label surfaces (7.1–7.9 rows above):
  `[propext, Classical.choice, Quot.sound]` only.

## Open selected-scope items
None.
