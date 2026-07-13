# Higham Chapter 14 — Claude Coverage Note (Split 3A)

Chapter 14 "Matrix Inversion" is Split 3A. This note tracks the rows closed by the
Claude agent, in NEW import-only modules (namespace `LeanFpAnalysis.FP.Ch14Ext`,
`ch14ext_`-prefixed) that reuse the existing `higham14_*` / `gje_*` / `triInv_*`
certificate routes. The detailed per-row ledgers under `docs/chapter14/` are the
canonical inventory; this note records the Claude-authored closures.

Source: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM,
2002), Chapter 14. All modules axiom-clean (`[propext, Classical.choice, Quot.sound]`)
and adversarially verified.

## Wave 1 — independent rows (closed)

| Row | Statement | Status | Module / headline decl |
|---|---|---|---|
| **(14.3)** §14.1 | `\|A⁻¹−Y\| ≤ ε\|A⁻¹\|\|A\|\|A⁻¹\| + O(ε²)` for `Y=(A+ΔA)⁻¹`, `\|ΔA\|≤ε\|A\|` | **CLOSED** | `Ch14ForwardErrorEndpoint.lean` — `ch14ext_eq14_3_forward_error_endpoint` (O(ε²) made rigorous as an explicit `ε²·(≥0)` term; uses the exact identity `A⁻¹−Y=A⁻¹ΔA Y` + Codex's `higham14_eq14_3_forward_error_firstorder_plus_remainder`) |
| **Problem 14.15** | `κ₂(A)‖ΔA‖₂/‖A‖₂ < 1 ⟹ \|det(A+ΔA)/det(A) − 1\| ≤ nκ₂·(‖ΔA‖₂/‖A‖₂)/(1−nκ₂·‖ΔA‖₂/‖A‖₂)` | **CLOSED** | `Chapter14Problem1415Weyl.lean` — `ch14ext_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_inv_card_guard`. Built a **Courant–Fischer min-max + all-index Weyl/Mirsky singular-value perturbation bound** `\|σ_i(A+Δ)−σ_i(A)\| ≤ ‖Δ‖₂` from scratch (Mathlib/repo had only top+min index). Uses the corrected `<1/n` smallness guard (the repo had proved Higham's literal `<1` insufficient). |
| **Problem 14.14** | Hyman's method computes exact `det(H+ΔH)`, `\|ΔH\| ≤ γ_{2n-1}\|H\|`, + diagonal-similarity effect | **CLOSED** | `Ch14HymanDeterminant.lean` — `ch14ext_hyman_flDet_backward_error_original`. Exact `γ_{2n-1}` derived from the fl back-substitution + inner-product model; stronger than printed (exact det identity). |

## Reusable infrastructure added (potentially useful elsewhere)

- **All-index Weyl/Mirsky singular-value perturbation** for real rectangular / complex matrices, built on a from-scratch Courant–Fischer min-max over the Gram eigenbasis (`ch14ext_problem14_15_all_index_singularValue_abs_sub_le_opNorm2`, `ch14ext_singularValue_abs_sub_le_of_euclideanLin_diff_bound`). Mathlib currently lacks this; it may unblock other perturbation rows.

## Wave 2 — deep GJE-cluster cores (Codex stopped; sole ownership)

Each *derives* a per-step/loop hypothesis Codex had left assumed (verified: `derivedNotAssumed = true` in every case), rather than re-assuming it. All axiom-clean, adversarially verified, import-only.

| Row | Status | Module / result |
|---|---|---|
| **Lemma 14.1** / (14.8) — Method 2 triangular-inverse left residual | **CLOSED** | `Ch14Method2Loop.lean` — `ch14ext_method2_left_residual`(`_normwise`). Concrete reverse-column loop (`termination_by n − j`) derives the strict-tail `fl_dotProduct`/`fl_mul` recurrence; no assumed storage hypothesis. |
| **Algorithm 14.4** — full GJE with partial pivoting | **CLOSED** (spec + structural) | `GaussJordanPivoting.lean` — pivot selection (max-magnitude), permutation (`ch14ext_perm_isPermutation`), multiplier `\|m\|≤1` under pivoting (`ch14ext_pivoted_multiplier_abs_le_one`), elimination = matmul, column-zeroing. (Numerical stability is Theorem 14.5, separate.) |
| **(14.14)** — Method 2B block-update instability | **CLOSED** | `MatrixInversionMethod2BInstance.lean` — explicit witness `Δ=[0,ε]`; off-diagonal residual not small + unbounded amplification, largeness derived. |
| **Theorem 14.5** / (14.25)–(14.26) per-step | **PARTIAL** | `Ch14GaussJordanStep.lean` — **derived** the GJE second-stage per-step `γ₃` bound `\|Û_{k+1}−N̂ₖÛₖ\| ≤ γ₃\|N̂ₖ\|\|Ûₖ\|` (+ RHS analogue) from `fl(a op b)=(a op b)(1+δ)`, discharging Codex's assumed `hComp` unconditionally. **Residual:** the multi-stage cumulative accumulation (14.27)–(14.30) to the printed `8nu`/`2nu` endpoints (14.31)–(14.32). |
| **Lemma 14.3** — Method 2C block left residual | **PARTIAL** | `Ch14Method2C.lean` — base + Higham's 2-block reduction, deriving the residual from block update + back-substitution error. **Residual:** the outer N-block recursion (N>2). |
| **Lemma 14.2** / (14.10)–(14.13) — Method 1B block right residual | **PARTIAL** | `Ch14BlockTriInverse.lean` — derives the row-local certificates from the two-block partition (Higham's reduced case, p.265). **Residual:** the general N-block loop (N>2). |

## Wave 3 — dependent deep tail

| Row | Status | Module / result |
|---|---|---|
| **Lemma 14.3** — Method 2C block triangular inverse, **whole-matrix / general N-block** | **CLOSED** | `Ch14Method2CWhole.lean` — `ch14ext_method2C_whole_left_residual`: for any block partition `bs : List ℕ`, `\|X̂L−I\| ≤ (γ_{n+2}+2γ_n+γ_n²)\|X̂\|\|L\|`, constant derived. Upgrades wave-2's 2-block case to the full flat `Fin n` statement. |
| **Theorem 14.5** / (14.27)–(14.32) | **PARTIAL (accumulation closed)** | `Ch14GaussJordanAccumulation.lean` — the multi-stage accumulation (14.27)/(14.28) is closed **unconditionally** (Duhamel telescoping of the wave-2 per-step Δ_k with the `(1+γ₃)` growth envelope → `gje_c3·\|X\|\|·\|`). Endpoints (14.31)/(14.32) reached via `gje_overall_residual`/`_forward_error` in `gje_c3` form. **Residuals:** Higham's own WLOG `D=I` normalization; the cumulative-product inverse `Q=(∏N̂)⁻¹` supplied as data (constructible as the reverse product of `N̂ₖ⁻¹=I+n̂ₖeₖᵀ`); the printed `8nu`/`2nu` = `gje_c3` + GE first-stage budget (scalar audit). The wave-2 obstruction (column-dependent rounding ⇏ single j-independent `DeltaN`) is confirmed and honored — the additive accumulation route was used. |
| **Method D (14.20)–(14.23)** | **PARTIAL** | `Ch14MethodDLeftResidual.lean` — the printed `(4γ+2γ²)` componentwise + normwise left-residual envelope (14.23) derived at arbitrary ε (removes Codex's hardcoded accumulator). **Residual:** three local certificates (notably the upper-triangular-inverse left residual `\|X_U U − I\|`) — genuine inputs to Higham's Method D analysis, not smuggled. |

## Wave 4 — Corollaries 14.6 / 14.7 + Method D completion

| Row | Status | Module / result |
|---|---|---|
| **Corollary 14.6** (SPD GJE residual + forward stability) | **PARTIAL (cores derived)** | `Ch14GaussJordanSPDCorollary.lean` — derived the **spectral Cholesky identity** `‖RᵀR‖₂ = ‖R‖₂²` (closing a step the codebase had flagged *open* at `HighamChapter10:970`), discharged the α/β/η SPD norm-aggregations via the Lemma 6.6 operator-2 chain, and derived the residual + forward-stability bounds with the printed **κ₂ leading constant derived**. **Residual:** the literal `8n³u·κ₂^{1/2}` constant is blocked by a 3-factor-vs-2-factor structure inherited from the accumulation surrogate (β/η stay a scale-dependent additive remainder), the entrywise `\|Rinv\|` majorant vs `opNorm2`, and exact-Cholesky idealization (`+O(u²)`). |
| **Corollary 14.7** (row diagonally dominant GJE) | **PARTIAL (cores derived)** | `Ch14Corollary147.lean` — **fully derived** the two row-dominant control facts: `cond_∞(U) = ‖\|U⁻¹\|\|U\|‖_∞ ≤ 2n−1` (Lemma 8.8 repackaged) and the `\|L\|\|U\|` bound for A=LU row-dominant. **Residual:** the printed (14.31)/(14.32) leading-order bounds are wired as hypotheses rather than to the accumulation endpoint. |
| **Method D** upper-triangular-inverse certificate | **PARTIAL (chief target closed)** | `Ch14MethodDUpperCertificate.lean` — **derived unconditionally** the upper-triangular-inverse left residual `\|X_U U − I\| ≤ γ_{n+2}\|X_U\|\|U\|` via a **reversal-conjugation bridge** `U ↦ JUJ` (`J=Fin.rev`; the naive transpose lands in the wrong residual slot), discharging Method D's chief local certificate. **Residual:** two standard upstream FP inputs (LU backward error = Thm 9.3, fl-matmul error) remain as hypotheses — both proven elsewhere in the repo, wireable. |

## Notes

- Chapter 14 was co-owned with a concurrent Codex agent, now stopped; wave 1 took the independent rows, waves 2–4 the deep GJE-cluster cores + corollaries.
- **Closed primary labels / rows (Claude):** (14.3), (14.14), **Lemma 14.1**, **Lemma 14.3** (whole-matrix), **Algorithm 14.4** (spec), Problems 14.14 & 14.15; plus the unconditional Theorem 14.5 per-step (14.25)/(14.26) and multi-stage accumulation (14.27)/(14.28); the Method D (14.23) envelope + its upper-tri certificate; the spectral Cholesky identity and the Cor 14.7 `cond(U)≤2n−1` control fact.
- **Advanced with derived cores + documented residuals (not literal-constant closure):** Theorem 14.5 overall endpoints (14.31)–(14.33), Corollary 14.6, Corollary 14.7, Method D whole-matrix, Lemma 14.2 (Method 1B, 2-block). The residuals are consistently: Higham's own WLOG `D=I`, a constructible cumulative-product inverse, the printed integer-constant scalar audits, wireable upstream FP certificates, and the Method 1B N-block induction.
