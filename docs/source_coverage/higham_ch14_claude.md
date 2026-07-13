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

## Notes

- Chapter 14 was co-owned with a concurrent Codex agent (now stopped). Wave 1 targeted the rows independent of Codex's §14.3–§14.4 Gauss–Jordan cluster.
- Wave 2 (in progress at time of writing) targets the deep GJE-cluster cores (Theorem 14.5 keystone loop, Lemmas 14.1/14.2/14.3 Method 2/1B/2C loops, Algorithm 14.4 pivoting spec, Method 2B (14.14) instability instance).
