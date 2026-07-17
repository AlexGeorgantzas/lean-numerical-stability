# Higham Chapter 14 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 14, "Matrix Inversion". Mode: core. Split: 3A.
- Detailed inventories: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`, `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`; Claude coverage note: `docs/source_coverage/higham_ch14_claude.md`. This file is the canonical top-level source-coverage ledger.
- **Selected-scope gate: PASS.** All 9 primary labels are VERIFIED or honest PARTIAL with source-faithful documented residuals; none MISSING. All modules axiom-clean (`[propext, Classical.choice, Quot.sound]`) and adversarially verified.

## Primary-label coverage

| Label | Status | Lean declaration(s) / module |
|---|---|---|
| **Lemma 14.1** / (14.8) — Method 2 triangular-inverse left residual | VERIFIED | `ch14ext_method2_left_residual`(`_normwise`), `Ch14Method2Loop.lean` — concrete reverse-column loop, `γ_{n+2}` |
| **Lemma 14.2** / (14.10)–(14.13) — Method 1B block right residual | VERIFIED | `ch14ext_method1B_whole_right_residual`(`_normwise`), `Ch14Method1BWhole.lean` — whole-matrix, any block partition, `γ_n` |
| **Lemma 14.3** — Method 2C block left residual | VERIFIED | `ch14ext_method2C_whole_left_residual`(`_normwise`), `Ch14Method2CWhole.lean` — whole-matrix N-block |
| **Algorithm 14.4** — GJE with partial pivoting | VERIFIED (spec + structure) | `GaussJordanPivoting.lean` (`ch14ext_pivotRow_max`, `ch14ext_perm_isPermutation`, `ch14ext_pivoted_multiplier_abs_le_one`, elimination = matmul) |
| **Theorem 14.5** / (14.31)–(14.33) — overall GJE residual + forward error | PARTIAL (printed 8nu residual reached) | `ch14ext_gjeConstructedQ_residual_8nu` reaches the printed `8nu` residual (14.31) from the concrete loop (via `Ch14GaussJordanStep`/`Ch14GaussJordanAccumulation`/`Ch14GaussJordanQConstruction` + Codex source-closure modules). Residual: the (14.32) forward-error two-term split `2nu\|A⁻¹\|\|L̂\|\|Û\|\|x̂\| + 6nu\|…\|` is on a single 3-factor object (documented structural residual; 2nu/6nu constants audited). |
| **Corollary 14.6** — SPD GJE forward stability | PARTIAL (cores derived) | `ch14ext_gje_spd_forward_stability_kappa2_leading`, `ch14ext_gje_spd_residual_relative_norm2_*` + Codex `Ch14Corollary146SourceClosure`. Residual: literal `8n³u·κ₂^{1/2}` / `8n^{5/2}u·κ₂` (3-vs-2-factor norm structure, entrywise `\|R⁻¹\|` vs opNorm2, exact-Cholesky idealization). |
| **Corollary 14.7** — row diagonally dominant GJE | PARTIAL (cores derived) | `ch14ext_cor147_condU_infNorm_le` (cond_∞(U) ≤ 2n−1), `ch14ext_cor147_absLU_infNorm_le` + Codex `Ch14Corollary147SourceClosure`. |
| **Problem 14.14** — Hyman determinant backward error | VERIFIED | `ch14ext_hyman_flDet_backward_error_original`, `Ch14HymanDeterminant.lean` — exact fl-Hyman det of `H+ΔH`, `\|ΔH\| ≤ γ_{2n-1}\|H\|` |
| **Problem 14.15** — determinant perturbation bound | VERIFIED | `ch14ext_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard`, `Chapter14Problem1415Weyl.lean` — built the all-index Weyl singular-value perturbation bound from scratch |

## Equation coverage

(14.1)/(14.2) ideal residuals VERIFIED; (14.3) forward error with explicit `ε²` remainder VERIFIED; (14.4)–(14.7) Method 1 VERIFIED; (14.8) = Lemma 14.1; (14.10)–(14.13) = Lemma 14.2; (14.14) Method 2B instability CLOSED via explicit witness `Δ=[0,ε]`; (14.15)–(14.19) Methods A/B/C (conditional interfaces); (14.20)–(14.22) Method D exact algebra + `(4γ+2γ²)` envelope; (14.23) Method D left residual (with upper-tri-inverse certificate); (14.25)–(14.30) GJE recurrence/accumulation; (14.31)–(14.33) overall GJE (Thm 14.5).

## Honest-strength notes / residuals (non-gating)

- Theorem 14.5 forward-error two-term split and Corollaries 14.6/14.7 literal printed constants remain documented structural residuals (3-factor-vs-2-factor norm grouping; exact-Cholesky idealization). The printed 8nu residual (14.31) itself is reached.
- Method D's remaining upstream inputs (Thm 9.3 LU backward error for arbitrary A, fl-matmul) are proved elsewhere in the repo; the product-error is discharged.
- Cross-chapter role: consumes ch3 γ-calculus, ch8 triangular-solve backward error, ch9 LU (`LUBackwardError`), ch10 Cholesky (SPD Cor 14.6), ch6 Lemma 6.6 (SPD 2-norm); provides matrix-inversion backward/forward error used by condition-estimation (ch15) context.

## Verification

- All modules build under the green full `lake build`; `#print axioms` on load-bearing decls = `[propext, Classical.choice, Quot.sound]`; adversarially verified. Audited 2026-07-17.
