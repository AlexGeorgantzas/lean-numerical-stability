# Higham Chapter 14 Source Coverage Ledger

> **Fresh strict audit (2026-07-18): gate FAIL.** Theorem 14.5 and Corollaries
> 14.6-14.7 remain conditional family contracts with unconstructed finalization,
> inverse, solve, or regularity fields. Honest partials do not pass the strict
> source-strength gate. See `AUDIT_ch01-28_2026-07-18.md`.

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 14, "Matrix Inversion". Mode: core. Split: 3A.
- Detailed inventories: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`, `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`; Claude coverage note: `docs/source_coverage/higham_ch14_claude.md`. This file is the canonical top-level source-coverage ledger.
- **Selected-scope gate: FAIL.** Lemmas 14.1-14.3 and the exact Algorithm 14.4
  specification are closed. Theorem 14.5 and Corollaries 14.6-14.7 have
  source-strength conditional endpoints, but no constructor connects the
  repository's rounded Algorithm 14.4 execution to all of their family fields.

## Primary-label coverage

| Label | Status | Lean declaration(s) / module |
|---|---|---|
| **Lemma 14.1** / (14.8) — Method 2 triangular-inverse left residual | VERIFIED | `ch14ext_method2_left_residual`(`_normwise`), `Ch14Method2Loop.lean` — concrete reverse-column loop, `γ_{n+2}` |
| **Lemma 14.2** / (14.10)–(14.13) — Method 1B block right residual | VERIFIED | `ch14ext_method1B_whole_right_residual`(`_normwise`), `Ch14Method1BWhole.lean` — whole-matrix, any block partition, `γ_n` |
| **Lemma 14.3** — Method 2C block left residual | VERIFIED | `ch14ext_method2C_whole_left_residual`(`_normwise`), `Ch14Method2CWhole.lean` — whole-matrix N-block |
| **Algorithm 14.4** — GJE with partial pivoting | VERIFIED (spec + structure) | `GaussJordanPivoting.lean` (`ch14ext_pivotRow_max`, `ch14ext_perm_isPermutation`, `ch14ext_pivoted_multiplier_abs_le_one`, elimination = matmul) |
| **Theorem 14.5** / (14.31)–(14.33) — overall GJE residual + forward error | PARTIAL (conditional family endpoint) | `ch14ext_gjeSourceTrace_theorem14_5_printed_vanishing_family_endpoint` proves the printed bounds after a `Ch14GJETheorem145SourceFamily` is supplied. `Ch14GJEOperationalBridge.lean` now constructs the returned vector and canonical exact inverse/solve witnesses, but `ch14ext_finalizationCounter_not_identity` proves that successful nonzero pivots do not construct the family's `final_matrix = I` field for the current rounded trace. |
| **Corollary 14.6** — SPD GJE forward stability | PARTIAL (conditional family endpoint) | `ch14ext_cor146Source_vanishing_family_endpoint` has the literal printed constants, but `Ch14Cor146SourceRunFamily` is not produced by the rounded GJE path; it additionally retains scaled-inverse and uniform-inverse regularity fields. |
| **Corollary 14.7** — row diagonally dominant GJE | PARTIAL (conditional family endpoint) | `ch14ext_cor147Source_vanishing_family_endpoint` has the literal printed constants, but `Ch14Cor147SourceFamily` is not produced by the rounded GJE path and retains finalization and uniform stage/inverse regularity fields. |
| **Problem 14.14** — Hyman determinant backward error | VERIFIED | `ch14ext_hyman_flDet_backward_error_original`, `Ch14HymanDeterminant.lean` — exact fl-Hyman det of `H+ΔH`, `\|ΔH\| ≤ γ_{2n-1}\|H\|` |
| **Problem 14.15** — determinant perturbation bound | VERIFIED | `ch14ext_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard`, `Chapter14Problem1415Weyl.lean` — built the all-index Weyl singular-value perturbation bound from scratch |

## Equation coverage

(14.1)/(14.2) ideal residuals VERIFIED; (14.3) forward error with explicit `ε²` remainder VERIFIED; (14.4)–(14.7) Method 1 VERIFIED; (14.8) = Lemma 14.1; (14.10)–(14.13) = Lemma 14.2; (14.14) Method 2B instability CLOSED via explicit witness `Δ=[0,ε]`; (14.15)–(14.19) Methods A/B/C (conditional interfaces); (14.20)–(14.22) Method D exact algebra + `(4γ+2γ²)` envelope; (14.23) Method D left residual (with upper-tri-inverse certificate); (14.25)–(14.26) local rounded GJE recurrences VERIFIED; (14.27), (14.29)–(14.32), and the fixed-matrix addendum to (14.30) PARTIAL because they consume the unproduced finalization/family contract; (14.28) and the algebraic decomposition (14.33) VERIFIED.

## Honest-strength notes / residuals (non-gating)

- `ch14ext_gjeSourceComputedOutput` makes the returned vector definitionally
  equal to the recursively executed trace. Nonsingularity constructs the exact
  inverse and solve witnesses through
  `ch14ext_gjeCanonicalUpperInverse_isInverse` and
  `ch14ext_gjeCanonicalUpperSolve_exact`; their family boundedness reduces to
  boundedness of the canonical inverse.
- The smallest remaining source-strength blocker is operational finalization.
  The current rounded step computes the eliminated matrix entry with rounded
  division/multiplication/subtraction. For a legal multiplication-biased
  `FPModel`, the normalized 2-by-2 successful trace leaves that entry equal to
  `-u`, not zero. The combined theorem
  `ch14ext_finalizationCounter_all_local_guards_but_not_identity` includes both
  gamma-validity guards and pivot success. Therefore the assumed
  `final_matrix = I` field is not derivable from successful pivots. Closing the
  row requires one rounded Algorithm 14.4 executor that explicitly models the
  structural zero assignments and final diagonal scaling, followed by the
  local-error and family-regularity proofs for that same executor.
- Method D's remaining upstream inputs (Thm 9.3 LU backward error for arbitrary A, fl-matmul) are proved elsewhere in the repo; the product-error is discharged.
- Cross-chapter role: consumes ch3 γ-calculus, ch8 triangular-solve backward error, ch9 LU (`LUBackwardError`), ch10 Cholesky (SPD Cor 14.6), ch6 Lemma 6.6 (SPD 2-norm); provides matrix-inversion backward/forward error used by condition-estimation (ch15) context.

## Verification

- All modules build under the green full `lake build`; `#print axioms` on load-bearing decls = `[propext, Classical.choice, Quot.sound]`; adversarially verified. Audited 2026-07-17.
