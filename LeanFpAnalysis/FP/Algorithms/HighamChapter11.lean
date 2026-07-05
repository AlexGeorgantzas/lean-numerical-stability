-- Algorithms/HighamChapter11.lean
--
-- Source-facing entry points for Higham Chapter 11, "Symmetric Indefinite
-- and Skew-Symmetric Systems".  Reusable predicates and abstract stability
-- interfaces live in `Cholesky.CholeskyIndefinite`; this file gives stable
-- chapter labels for the split-2 ledger.

import LeanFpAnalysis.FP.Algorithms.HighamChapter10
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskyIndefinite

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-! ## Chapter 11 intro and §11.1 block LDL^T factorization -/

/-- **Equation (11.1)** source predicate:
`P A P^T = L D L^T`, with unit lower triangular `L` and symmetric block
diagonal `D` with diagonal blocks of size one or two. -/
abbrev higham11_1_BlockLDLTSpec (n : ℕ)
    (A L D : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) : Prop :=
  BlockLDLTSpec n A L D σ

/-- **Equation (11.2)** nonsingularity condition for the first pivot block. -/
def higham11_2_NonsingularPivotBlock
    (s : ℕ) (E E_inv : Fin s → Fin s → ℝ) : Prop :=
  (∀ i j : Fin s, ∑ k : Fin s, E i k * E_inv k j = if i = j then 1 else 0) ∧
  (∀ i j : Fin s, ∑ k : Fin s, E_inv i k * E k j = if i = j then 1 else 0)

/-- **Equation (11.3)** symmetric Schur complement
`B - C E^{-1} C^T` from the first block LDL^T step. -/
noncomputable def higham11_3_symmetricSchurComplement (m s : ℕ)
    (B : Fin m → Fin m → ℝ)
    (C : Fin m → Fin s → ℝ)
    (E_inv : Fin s → Fin s → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => B i j - ∑ p : Fin s, ∑ q : Fin s, C i p * E_inv p q * C j q

/-- **Equation (11.3), `s = 1` exact factorization step**: with pivot `A 0 0 ≠ 0`,
the 1×1-pivot unit-lower-triangular `L` and block-diagonal `D` (pivot + trailing
Schur complement) reproduce `A` exactly, `∑ L·D·Lᵀ = A`.  The exact base of the
diagonal-pivoting recursion behind Theorem 11.3. -/
theorem higham11_3_oneByOne_step_factorization (m : ℕ)
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (ha : A 0 0 ≠ 0) (hsym : ∀ i : Fin m, A 0 i.succ = A i.succ 0)
    (L D : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hL0 : L 0 0 = 1)
    (hLcol : ∀ i : Fin m, L i.succ 0 = A i.succ 0 / A 0 0)
    (hL0s : ∀ j : Fin m, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin m, L i.succ j.succ = if i = j then 1 else 0)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin m, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin m, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin m, D i.succ j.succ
      = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) :
    ∀ I J : Fin (m + 1),
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J :=
  oneByOne_step_factorization m A ha hsym L D hL0 hLcol hL0s hLtr
    hD00 hD0s hDs0 hDtr

/-- **Eq (11.1)/(11.3) inductive step** for the exact block-LDLᵀ recursion: with
the trailing block factorized recursively (`hIH : L_S·D_S·L_Sᵀ = S`, the Schur
complement) and first-stage 1×1-pivot multipliers, the assembled `L,D` reproduce
`A` exactly.  Iterating gives the exact `PAPᵀ = LDLᵀ` behind Theorem 11.3. -/
theorem higham11_3_blockLDLT_assemble_step (n : ℕ)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (ha : A 0 0 ≠ 0) (hsym : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (S L_S D_S : Fin n → Fin n → ℝ)
    (hS : ∀ i j : Fin n, S i j = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0)
    (hIH : ∀ i j : Fin n, (∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂) = S i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL0 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = A i.succ 0 / A 0 0)
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ I J : Fin (n + 1),
      (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J :=
  blockLDLT_assemble_step n A ha hsym S L_S D_S hS hIH L D
    hL0 hLcol hL0s hLtr hD00 hD0s hDs0 hDtr

/-- **Eq (11.1)/(11.2) exact factorization existence** (no-2×2-pivot case): a
symmetric `A` all of whose successive Schur-complement pivots are nonzero
(`AllOnePivots`) has an exact `LDLᵀ` factorization `∑ L·D·Lᵀ = A`.  The exact
`PAPᵀ = LDLᵀ` recursion (P = I) underlying Theorem 11.3. -/
theorem higham11_1_exact_blockLDLT_all_oneByOne (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, A i j = A j i) (hp : AllOnePivots n A) :
    ∃ L D : Fin n → Fin n → ℝ,
      ∀ I J, (∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) = A I J :=
  exact_blockLDLT_all_oneByOne n A hsym hp

/-! ## §11.1.1 Complete pivoting -/

/-- **Algorithm 11.1** pivoting parameter
`alpha = (1 + sqrt 17) / 8`. -/
noncomputable def higham11_1_bunchParlettAlpha : ℝ :=
  bunchParlettAlpha

/-- **Algorithm 11.1** source decision predicate for the first
Bunch-Parlett complete-pivoting step. -/
abbrev higham11_1_BunchParlettCompletePivotChoice
    (α μ0 μ1 : ℝ) (s : PivotSize) : Prop :=
  BunchParlettCompletePivotChoice α μ0 μ1 s

/-- The Bunch-Parlett parameter is the positive root selected from
`4 alpha^2 - alpha - 1 = 0`. -/
theorem higham11_1_bunch_parlett_alpha_root :
    4 * higham11_1_bunchParlettAlpha ^ 2 -
      higham11_1_bunchParlettAlpha - 1 = 0 :=
  bunch_parlett_alpha_root

/-- **§11.1.1 α-derivation**: `α = (1+√17)/8` is exactly the value balancing the
two single-step growth bounds `(1 + 1/α)²` (two 1×1 steps) and `1 + 2/(1−α)`
(one 2×2 step).  Connects `higham11_1_oneByOne_schur_growth` and
`higham11_4_twoByTwo_schur_growth`. -/
theorem higham11_1_growth_balance :
    (1 + 1 / higham11_1_bunchParlettAlpha) ^ 2 =
      1 + 2 / (1 - higham11_1_bunchParlettAlpha) :=
  bunch_parlett_growth_balance

/-- **§11.1.1 growth-factor recursion**: a stage-maximum sequence `r` obeying the
single-step ratio bound `r(k+1) ≤ (1 + 1/α)·r k` (supplied for each stage by
`higham11_1_oneByOne_schur_growth` / `higham11_4_twoByTwo_schur_growth`) satisfies
`r n ≤ (1 + 1/α)^n · ρ₀`, the derivation of the printed `ρₙ ≤ (1 + α⁻¹)^{n−1}`. -/
theorem higham11_1_growth_factor_recursion (α ρ0 : ℝ) (r : ℕ → ℝ)
    (hα : 0 < α) (h0 : r 0 = ρ0)
    (hstep : ∀ k, r (k + 1) ≤ (1 + 1 / α) * r k) :
    ∀ n, r n ≤ (1 + 1 / α) ^ n * ρ0 :=
  geom_growth_iterate α ρ0 r hα h0 hstep

/-- **Equation (11.4)**, the scalar entry of the 2 by 2 Schur complement
`b_ij - [c_i1 c_i2] E^{-1} [c_j1, c_j2]^T`. -/
noncomputable def higham11_4_twoByTwoSchurEntry
    (bij ci1 ci2 cj1 cj2 e11 e12 e21 e22 : ℝ) : ℝ :=
  bij - (ci1 * (e11 * cj1 + e12 * cj2) +
    ci2 * (e21 * cj1 + e22 * cj2))

/-- Complete-pivoting growth-bound interface:
`rho_n <= (1 + alpha^{-1})^(n-1)`. -/
theorem higham11_1_bunch_parlett_growth_bound (n : ℕ) (hn : 0 < n)
    (ρ_n : ℝ)
    (hρ : ρ_n ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) :
    ρ_n ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) :=
  bunch_parlett_growth_bound n hn ρ_n hρ

/-- Complete-pivoting multiplier bound interface:
`|L_ij| <= max {1/alpha, 1/(1-alpha)}`. -/
theorem higham11_1_bunch_parlett_L_bound (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (c_bound : ℝ)
    (hc : c_bound =
      max (1 / higham11_1_bunchParlettAlpha)
          (1 / (1 - higham11_1_bunchParlettAlpha)))
    (hL : ∀ i j : Fin n, |L i j| ≤ c_bound) :
    ∀ i j : Fin n, |L i j| ≤ c_bound :=
  bunch_parlett_L_bound n L c_bound hc hL

/-- **§11.1.1 multiplier bound**, proved from the pivot-acceptance test: a 1×1
pivot `e` with `α·ω ≤ |e|` and off-pivot entries bounded by `ω` gives
multipliers `|c/e| ≤ 1/α`.  This is the honest derivation behind the
`bunch_parlett_L_bound` interface (`|L_ij| ≤ max{1/α, 1/(1-α)}`). -/
theorem higham11_1_oneByOne_multiplier_bound (c e ω α : ℝ)
    (hα : 0 < α) (hω : 0 < ω) (hc : |c| ≤ ω) (he : α * ω ≤ |e|) :
    |c / e| ≤ 1 / α :=
  oneByOne_multiplier_bound c e ω α hα hω hc he

/-- **§11.1.1 single-step element growth for a 1×1 pivot**:
`|b − c₁c₂/e| ≤ (1 + 1/α)·μ₀` when `α·μ₀ ≤ |e|` and all active entries are
bounded by `μ₀`.  This is the printed bound `|ã_ij| ≤ μ₀ + μ₀²/μ₁ ≤ (1+1/α)μ₀`
and the mechanism behind the growth-factor bound `ρₙ ≤ (1+α⁻¹)^{n−1}`. -/
theorem higham11_1_oneByOne_schur_growth (b c1 c2 e μ0 α : ℝ)
    (hα : 0 < α) (hμ : 0 < μ0)
    (hb : |b| ≤ μ0) (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0)
    (he : α * μ0 ≤ |e|) :
    |b - c1 * c2 / e| ≤ (1 + 1 / α) * μ0 :=
  oneByOne_schur_growth b c1 c2 e μ0 α hα hμ hb hc1 hc2 he

/-- **§11.1.1 2×2 pivot determinant bound**:
`det E = e₁₁e₂₂ − e₂₁² ≤ (α² − 1)μ₀²` for a complete-pivoting 2×2 block, and,
for `α ∈ [0,1)`, `|det E| ≥ (1 − α²)μ₀²`. -/
theorem higham11_4_twoByTwo_det_bound (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    e11 * e22 - e21 ^ 2 ≤ (α ^ 2 - 1) * μ0 ^ 2 :=
  twoByTwo_completePivot_det_bound e11 e22 e21 μ0 μ1 α hμ1 he11 he22 he21 hμ1α

/-- **§11.1.1 2×2 pivot nonsingularity magnitude bound**:
`|det E| ≥ (1 − α²)μ₀²` for `α ∈ [0,1)`, the printed estimate used to bound
`E⁻¹` and hence the 2×2-step element growth `(1 + 2/(1−α))μ₀`. -/
theorem higham11_4_twoByTwo_absdet_lower (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    (1 - α ^ 2) * μ0 ^ 2 ≤ |e11 * e22 - e21 ^ 2| :=
  twoByTwo_completePivot_absdet_lower e11 e22 e21 μ0 μ1 α
    hμ1 hα0 hα1 he11 he22 he21 hμ1α

/-- **Eq (11.4) element growth for a 2×2 complete-pivoting step**:
the Schur entry `higham11_4_twoByTwoSchurEntry` built from inverse-block entries
`e₁₁,e₁₂,e₂₁,e₂₂` bounded by `|e₁₁|,|e₂₂| ≤ αK`, `|e₁₂|,|e₂₁| ≤ K` with
`K = 1/((1−α²)μ₀)`, and active entries `≤ μ₀`, satisfies
`|ã| ≤ (1 + 2/(1−α))·μ₀`.  This is the printed §11.1.1 bound and, with
`higham11_1_oneByOne_schur_growth`, completes both single-step growth bounds. -/
theorem higham11_4_twoByTwo_schur_growth
    (bij ci1 ci2 cj1 cj2 e11 e12 e21 e22 μ0 α K : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hb : |bij| ≤ μ0)
    (hci1 : |ci1| ≤ μ0) (hci2 : |ci2| ≤ μ0)
    (hcj1 : |cj1| ≤ μ0) (hcj2 : |cj2| ≤ μ0)
    (he11 : |e11| ≤ α * K) (he12 : |e12| ≤ K)
    (he21 : |e21| ≤ K) (he22 : |e22| ≤ α * K) :
    |higham11_4_twoByTwoSchurEntry bij ci1 ci2 cj1 cj2 e11 e12 e21 e22|
      ≤ (1 + 2 / (1 - α)) * μ0 := by
  unfold higham11_4_twoByTwoSchurEntry
  exact twoByTwo_schur_growth bij ci1 ci2 cj1 cj2 e11 e12 e21 e22 μ0 α K
    hα0 hα1 hμ hK hb hci1 hci2 hcj1 hcj2 he11 he12 he21 he22

/-- **§11.1.1 printed inverse bound** `|E⁻¹| ≤ K·[[α,1],[1,α]]`, `K = 1/((1−α²)μ₀)`:
the entrywise bounds on `E⁻¹ = d⁻¹[[e₂₂,−e₂₁],[−e₂₁,e₁₁]]` for a complete-pivoting
2×2 block, derived from the determinant magnitude bound. -/
theorem higham11_4_twoByTwo_inverse_entry_bounds (e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1) :
    |e22 / (e11 * e22 - e21 ^ 2)| ≤ α * K
      ∧ |e11 / (e11 * e22 - e21 ^ 2)| ≤ α * K
      ∧ |e21 / (e11 * e22 - e21 ^ 2)| ≤ K :=
  twoByTwo_inverse_entry_bounds e11 e22 e21 μ0 μ1 α K
    hμ1 hα0 hα1 hμ he11 he22 he21 hμ1α hK

/-- **§11.1.1 self-contained 2×2 growth**: substituting the actual inverse block
`E⁻¹` into the eq-(11.4) Schur entry, `|ã| ≤ (1 + 2/(1−α))μ₀` holds using only the
pivot-block data (no assumed inverse-entry bounds). -/
theorem higham11_4_twoByTwo_schur_growth_of_block
    (bij ci1 ci2 cj1 cj2 e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hb : |bij| ≤ μ0)
    (hci1 : |ci1| ≤ μ0) (hci2 : |ci2| ≤ μ0)
    (hcj1 : |cj1| ≤ μ0) (hcj2 : |cj2| ≤ μ0) :
    |higham11_4_twoByTwoSchurEntry bij ci1 ci2 cj1 cj2
        (e22 / (e11 * e22 - e21 ^ 2)) (-(e21 / (e11 * e22 - e21 ^ 2)))
        (-(e21 / (e11 * e22 - e21 ^ 2))) (e11 / (e11 * e22 - e21 ^ 2))|
      ≤ (1 + 2 / (1 - α)) * μ0 := by
  unfold higham11_4_twoByTwoSchurEntry
  exact twoByTwo_schur_growth_of_block bij ci1 ci2 cj1 cj2 e11 e22 e21 μ0 μ1 α K
    hμ1 hα0 hα1 hμ he11 he22 he21 hμ1α hK hb hci1 hci2 hcj1 hcj2

/-! ## §11.1.2 Partial pivoting -/

/-- **Algorithm 11.2** branch predicate for the Bunch-Kaufman partial
pivoting tests. -/
abbrev higham11_2_BunchKaufmanPartialPivotCase
    (α a11 arr ω1 ωr : ℝ) (branch : BunchKaufmanCase) : Prop :=
  BunchKaufmanPartialPivotCase α a11 arr ω1 ωr branch

/-- **Equation (11.5)** first-order 2 by 2 pivot solve certificate.  The
source theorem also includes `O(u^2)` terms, recorded in the ledger as a
deferred asymptotic refinement. -/
def higham11_5_twoByTwoPivotSolveStable
    (u c : ℝ) (E ΔE : Fin 2 → Fin 2 → ℝ) : Prop :=
  ∀ i j : Fin 2, |ΔE i j| ≤ c * u * |E i j|

/-- **Theorem 11.3** source-facing interface for the block LDL^T backward
error theorem.  This records the exact componentwise target shape; the detailed
floating-point pivot/solve analysis is supplied by the hypothesis. -/
theorem higham11_3_block_ldlt_backward_error_interface (n : ℕ)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (bound : Fin n → Fin n → ℝ)
    (h : ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ bound i j) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ bound i j) ∧
      (∀ i j : Fin n,
        ∑ k₁ : Fin n, ∑ k₂ : Fin n,
          L_hat i k₁ * D_hat k₁ k₂ * L_hat j k₂ =
        A (σ i) (σ j) + ΔA1 i j)) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ bound i j) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ bound i j) ∧
      (∀ i j : Fin n,
        ∑ k₁ : Fin n, ∑ k₂ : Fin n,
          L_hat i k₁ * D_hat k₁ k₂ * L_hat j k₂ =
        A (σ i) (σ j) + ΔA1 i j) :=
  h

/-- **Theorem 11.3 per-step floating-point building block**: the fl backward
error of one 1×1 Schur-complement update `s = fl(a − fl(fl(c₁/e)·c₂))` equals the
exact entry `a − c₁c₂/e` plus a derived error `≤ γ₃·(|a| + |c₁c₂/e|)`.  This is a
genuine (non-assumed) atomic ingredient toward the block-LDLᵀ backward error
`higham11_3_block_ldlt_backward_error_interface`; the full recursion over all
stages remains open (see chapter report). -/
theorem higham11_3_fl_oneByOne_schur_step_error
    (fp : FPModel) (a e c1 c2 : ℝ)
    (he : e ≠ 0) (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 * (|a| + |c1 * c2 / e|) ∧
      fp.fl_sub a (fp.fl_mul (fp.fl_div c1 e) c2) = (a - c1 * c2 / e) + Δ :=
  fl_oneByOne_schur_step_error fp a e c1 c2 he hval

/-- **Theorem 11.3 / eq (11.5), `s = 1` case**: the computed 1×1 pivot solve
`x̂ = fl(b/e)` of `e·x = b` satisfies `(e + Δe)·x̂ = b` with `|Δe| ≤ γ₁·|e|` — a
derived (non-assumed) instance of the block-solve perturbation hypothesis (11.5)
for 1×1 pivots. -/
theorem higham11_3_fl_oneByOne_solve_backward_error
    (fp : FPModel) (b e : ℝ)
    (he : e ≠ 0) (hval : gammaValid fp 1) :
    ∃ Δe : ℝ, |Δe| ≤ gamma fp 1 * |e| ∧ (e + Δe) * fp.fl_div b e = b :=
  fl_oneByOne_solve_backward_error fp b e he hval

/-- **Theorem 11.3 per-stage trailing fl backward error** (Higham [608,1997]
§4.2): the computed `L̂D̂L̂ᵀ` trailing entry `l̂_i·e·l̂_j` plus the computed Schur
entry `Ŝ = fl(b − fl(l̂_i·c_j))` equals `b + Δ` with
`|Δ| ≤ 2γ₃(|b| + |c_i c_j/e|)` — the atomic `(i,j)` step of Theorem 11.3's
componentwise backward-error induction. -/
theorem higham11_3_fl_stage_trailing_error (fp : FPModel) (e ci cj b : ℝ)
    (he : e ≠ 0) (hval : gammaValid fp 3) :
    ∃ Δ : ℝ, |Δ| ≤ 2 * gamma fp 3 * (|b| + |ci * cj / e|) ∧
      fp.fl_div ci e * e * fp.fl_div cj e
        + fp.fl_sub b (fp.fl_mul (fp.fl_div ci e) cj) = b + Δ :=
  fl_oneByOne_stage_trailing_error fp e ci cj b he hval

/-- **Equation (11.6)**, the partial-pivoting example matrix. -/
noncomputable def higham11_6_partialPivotExampleA
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 1 then ε
    else if i.val = 1 ∧ j.val = 0 then ε
    else if i.val = 1 ∧ j.val = 2 then 1
    else if i.val = 2 ∧ j.val = 1 then 1
    else if i.val = 2 ∧ j.val = 2 then 1
    else 0

/-- **Equation (11.6)**, the displayed lower triangular factor. -/
noncomputable def higham11_6_partialPivotExampleL
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = j.val then 1
    else if i.val = 2 ∧ j.val = 0 then 1 / ε
    else 0

/-- **Equation (11.6)**, the displayed block diagonal factor. -/
noncomputable def higham11_6_partialPivotExampleD
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 1 then ε
    else if i.val = 1 ∧ j.val = 0 then ε
    else if i.val = 2 ∧ j.val = 2 then 1
    else 0

/-- **Equation (11.6)** verified algebraically:
`A = L D L^T` for `ε ≠ 0`. -/
theorem higham11_6_partialPivotExample_factorization
    (ε : ℝ) (hε : ε ≠ 0) :
    ∀ i j : Fin 3,
      ∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
        higham11_6_partialPivotExampleL ε i k₁ *
          higham11_6_partialPivotExampleD ε k₁ k₂ *
          higham11_6_partialPivotExampleL ε j k₂ =
      higham11_6_partialPivotExampleA ε i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, higham11_6_partialPivotExampleA, higham11_6_partialPivotExampleL,
      higham11_6_partialPivotExampleD, hε]

/-- The Higham [1997] max-entry bound used in the proof of Theorem 11.4:
`|| |L||D||L^T| ||_M <= 36 n rho_n ||A||_M`. -/
def higham11_4_bunchKaufmanMaxEntryProductBound
    (n : ℕ) (productMax ρ_n Amax : ℝ) : Prop :=
  productMax ≤ 36 * (n : ℝ) * ρ_n * Amax

/-- **Theorem 11.4 constant (Higham [608, 1997], eq (4.13))**: the `36` in the
bound `‖|L̂||D̂||L̂ᵀ|‖_M ≤ 36 n ρₙ ‖A‖_M` comes from
`(3+α²)(3+α)/(1−α²)² ≤ 36` at `α = (1+√17)/8`. -/
theorem higham11_4_bound_const_le_36 :
    (3 + higham11_1_bunchParlettAlpha ^ 2) * (3 + higham11_1_bunchParlettAlpha)
      / (1 - higham11_1_bunchParlettAlpha ^ 2) ^ 2 ≤ 36 :=
  bunch_kaufman_bound_const_le_36

/-- **Theorem 11.4 constant (Higham [608, 1997], appendix (A.3))**:
`(3+α²)/(1−α²) ≤ 6`, bounding `|E||E⁻¹||E| ≤ 6|E|` for a 2×2 pivot. -/
theorem higham11_4_pivot_norm_const_le_six :
    (3 + higham11_1_bunchParlettAlpha ^ 2) / (1 - higham11_1_bunchParlettAlpha ^ 2) ≤ 6 :=
  bunch_kaufman_pivot_norm_const_le_six

/-- **§11.1.2 1×1-pivot growth constant (Higham [608, 1997])**: `1/α < 2`, giving
the 1×1-pivot entry bound `g_ij ≤ α⁻¹·max < 2·max`. -/
theorem higham11_4_recip_alpha_lt_two : 1 / higham11_1_bunchParlettAlpha < 2 :=
  bunch_kaufman_recip_alpha_lt_two

/-- **Theorem 11.4** normwise Bunch-Kaufman stability interface. -/
theorem higham11_4_bunch_kaufman_stability (n : ℕ)
    (A L_hat D_hat : Fin n → Fin n → ℝ)
    (ρ_n maxNorm_A : ℝ) (hmA : 0 ≤ maxNorm_A)
    (hA_norm : ∀ i j : Fin n, |A i j| ≤ maxNorm_A)
    (hstab : ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A) :
    ∀ i j : Fin n,
      ∑ k₁ : Fin n, ∑ k₂ : Fin n,
        |L_hat i k₁| * |D_hat k₁ k₂| * |L_hat j k₂| ≤
      36 * ↑n * ρ_n * maxNorm_A :=
  bunch_kaufman_stability n A L_hat D_hat ρ_n maxNorm_A hmA hA_norm hstab

/-- **Theorem 11.4** solve backward-error target shape for Bunch-Kaufman
partial pivoting. -/
theorem higham11_4_bunch_kaufman_solve_backward_error_interface (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (p ρ_n u Amax : ℝ)
    (hsolve : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ p * ρ_n * u * Amax) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i)) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ p * ρ_n * u * Amax) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  hsolve

/-! ## §11.1.3 Rook pivoting -/

/-- **Algorithm 11.5** source decision predicate for symmetric rook pivoting. -/
abbrev higham11_5_SymmetricRookFirstPivotChoice
    (α a11 arr ω1 ωr : ℝ) (s : PivotSize) : Prop :=
  SymmetricRookFirstPivotChoice α a11 arr ω1 ωr s

/-- The printed rook-pivoting entry bound for the `L` factor. -/
def higham11_5_rookPivotLBound (n : ℕ) (α : ℝ)
    (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |L i j| ≤ max (1 / (1 - α)) (1 / α)

/-- The printed condition-number bound for accepted 2 by 2 rook pivots. -/
def higham11_5_rookPivotTwoByTwoCondBound (α κ : ℝ) : Prop :=
  κ ≤ (1 + α) / (1 - α)

/-- **Equation (11.7)** source-shaped forward-error bound. -/
def higham11_7_forwardErrorBound
    (relativeError p_n u condAx residualTerm : ℝ) : Prop :=
  relativeError ≤ p_n * u * condAx + residualTerm

/-! ## §11.1.4 Tridiagonal matrices -/

/-- **Algorithm 11.6** pivoting parameter
`alpha = (sqrt 5 - 1) / 2`. -/
noncomputable def higham11_6_bunchTridiagonalAlpha : ℝ :=
  bunchTridiagonalAlpha

/-- The tridiagonal pivoting parameter satisfies `alpha^2 + alpha - 1 = 0`. -/
theorem higham11_6_bunch_tridiagonal_alpha_root :
    higham11_6_bunchTridiagonalAlpha ^ 2 +
      higham11_6_bunchTridiagonalAlpha - 1 = 0 :=
  bunch_tridiagonal_alpha_root

/-- **Algorithm 11.6** source decision predicate for Bunch's tridiagonal
pivot-size strategy. -/
abbrev higham11_6_BunchTridiagonalPivotChoice
    (σ a11 a21 : ℝ) (s : PivotSize) : Prop :=
  BunchTridiagonalPivotChoice σ a11 a21 s

/-- **Equation (11.8)** source predicate: unpermuted block LDL^T
factorization for a symmetric tridiagonal matrix. -/
abbrev higham11_8_tridiagonalBlockLDLTSpec (n : ℕ)
    (A L D : Fin n → Fin n → ℝ) : Prop :=
  BlockLDLTSpec n A L D id

/-- **Theorem 11.7** normwise stability target shape for Bunch's
tridiagonal pivoting strategy. -/
theorem higham11_7_tridiagonal_backward_error_interface (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (c u Amax : ℝ)
    (hsolve : ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ c * u * Amax) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ c * u * Amax) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i)) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ c * u * Amax) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ c * u * Amax) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i) :=
  hsolve

/-! ## §11.2 Aasen's method -/

/-- Source predicate for symmetric tridiagonal matrices. -/
abbrev higham11_8_IsSymTridiagonal (n : ℕ)
    (T : Fin n → Fin n → ℝ) : Prop :=
  IsSymTridiagonal n T

/-- Aasen factorization source specification:
`P A P^T = L T L^T`, `L` unit lower triangular with first column `e_1`,
and `T` symmetric tridiagonal. -/
abbrev higham11_8_AasenSpec (n : ℕ)
    (A L T : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) : Prop :=
  AasenSpec n A L T σ

/-- **Equation (11.10)**, `H = T L^T`. -/
noncomputable def higham11_10_aasenH (n : ℕ)
    (T L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, T i k * L j k

/-- **Equation (11.12)**, diagonal equation in `A = L H`. -/
def higham11_12_aasenDiagonalEquation (n : ℕ)
    (A L H : Fin n → Fin n → ℝ) : Prop :=
  ∀ i : Fin n,
    A i i = (∑ j : Fin n, if j.val < i.val then L i j * H j i else 0) + H i i

/-- **Equation (11.13)**, subdiagonal equation in `A = L H`,
written with zero-based finite indices. -/
def higham11_13_aasenSubdiagonalEquation (n : ℕ)
    (A L H : Fin n → Fin n → ℝ) : Prop :=
  ∀ i k : Fin n, k.val = i.val + 1 →
    A k i = (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) + H k i

/-- **Equation (11.14)**, update for entries below the diagonal in the
next column of `L`, written with zero-based finite indices. -/
def higham11_14_aasenNextColumnEquation (n : ℕ)
    (A L H : Fin n → Fin n → ℝ) : Prop :=
  ∀ i next k : Fin n, next.val = i.val + 1 → i.val + 2 ≤ k.val →
    L k next =
      (A k i - ∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) /
        H next i

/-- **Equation (11.12) derivation**: the Aasen diagonal equation holds for any
`A = L·H` with `L` unit lower triangular.  Exact-arithmetic identity behind the
Aasen recurrence (not the fl analysis): `A i i = ∑_{j<i} L i j · H j i + H i i`,
by unit-lower-triangularity of `L`. -/
theorem higham11_12_aasen_diagonal_equation_of_product (n : ℕ)
    (A L H : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, L i i = 1)
    (hLupper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hprod : ∀ i k : Fin n, (∑ j, L i j * H j k) = A i k) :
    higham11_12_aasenDiagonalEquation n A L H := by
  intro i
  have key : ∀ j : Fin n, L i j * H j i
      = (if j.val < i.val then L i j * H j i else 0)
        + (if i.val ≤ j.val then L i j * H j i else 0) := by
    intro j
    by_cases h : j.val < i.val
    · simp [h, Nat.not_le.mpr h]
    · simp [h, Nat.not_lt.mp h]
  rw [← hprod i i, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [hLdiag i]
  · intro j _ hji
    by_cases h : i.val ≤ j.val
    · have hlt : i.val < j.val :=
        lt_of_le_of_ne h (fun e => hji (Fin.ext e.symm))
      simp [h, hLupper i j hlt]
    · simp [h]
  · intro hnm; exact absurd (Finset.mem_univ i) hnm

/-- **Equation (11.13) derivation**: the Aasen subdiagonal equation holds for any
`A = L·H` with `L` unit lower triangular.  For `k = i+1`,
`A k i = ∑_{j≤i} L k j · H j i + H k i`. -/
theorem higham11_13_aasen_subdiagonal_equation_of_product (n : ℕ)
    (A L H : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, L i i = 1)
    (hLupper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hprod : ∀ i k : Fin n, (∑ j, L i j * H j k) = A i k) :
    higham11_13_aasenSubdiagonalEquation n A L H := by
  intro i k hk
  have key : ∀ j : Fin n, L k j * H j i
      = (if j.val ≤ i.val then L k j * H j i else 0)
        + (if k.val ≤ j.val then L k j * H j i else 0) := by
    intro j
    by_cases h : j.val ≤ i.val
    · have hnk : ¬ k.val ≤ j.val := by omega
      simp [h, hnk]
    · have hkj : k.val ≤ j.val := by omega
      simp [h, hkj]
  rw [← hprod k i, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp [hLdiag k]
  · intro j _ hjk
    by_cases h : k.val ≤ j.val
    · have hlt : k.val < j.val :=
        lt_of_le_of_ne h (fun e => hjk (Fin.ext e.symm))
      simp [h, hLupper k j hlt]
    · simp [h]
  · intro hnm; exact absurd (Finset.mem_univ k) hnm

/-- **Aasen band structure of `H = T·Lᵀ`** (Higham §11.2): with `T` tridiagonal
and `L` lower triangular, `H j i = ∑ₖ T j k·L i k = 0` for `j > i+1`.  The
structural fact that lets the column update (11.14) pick out a single term. -/
theorem higham11_10_aasenH_band (n : ℕ) (T L : Fin n → Fin n → ℝ)
    (hT : ∀ a b : Fin n, a.val + 1 < b.val ∨ b.val + 1 < a.val → T a b = 0)
    (hL : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (i j : Fin n) (hji : i.val + 1 < j.val) :
    higham11_10_aasenH n T L j i = 0 := by
  unfold higham11_10_aasenH
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : k.val ≤ i.val
  · rw [hT j k (Or.inr (by omega)), zero_mul]
  · rw [hL i k (by omega), mul_zero]

/-- **Equation (11.14) derivation**: for `A = L·H` with `L` unit lower triangular
and `H` banded (`H j i = 0` for `j > i+1`, e.g. from `higham11_10_aasenH_band`),
the below-diagonal next-column entries of `L` are
`L k next = (A k i − ∑_{j≤i} L k j·H j i) / H next i` (`next = i+1`, `k ≥ i+2`),
provided the pivot `H next i ≠ 0`.  Exact-arithmetic Aasen recurrence, toward Thm 11.8. -/
theorem higham11_14_aasen_next_column_of_product (n : ℕ)
    (A L H : Fin n → Fin n → ℝ)
    (hHband : ∀ i j : Fin n, i.val + 1 < j.val → H j i = 0)
    (hprod : ∀ k i : Fin n, (∑ j, L k j * H j i) = A k i)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0) :
    higham11_14_aasenNextColumnEquation n A L H := by
  intro i next k hnext hk
  have key : ∀ j : Fin n, L k j * H j i
      = (if j.val ≤ i.val then L k j * H j i else 0)
        + (if i.val < j.val then L k j * H j i else 0) := by
    intro j
    by_cases h : j.val ≤ i.val
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_le h]
  have htail : (∑ j, if i.val < j.val then L k j * H j i else 0)
      = L k next * H next i := by
    rw [Finset.sum_eq_single next]
    · have : i.val < next.val := by omega
      simp [this]
    · intro j _ hjn
      by_cases h : i.val < j.val
      · have hgt : i.val + 1 < j.val := by
          rcases lt_or_eq_of_le (Nat.succ_le_of_lt h) with h1 | h1
          · exact h1
          · exact absurd (Fin.ext (by omega)) hjn
        rw [hHband i j hgt]; simp
      · simp [h]
    · intro hnm; exact absurd (Finset.mem_univ next) hnm
  have hsum : A k i
      = (∑ j, if j.val ≤ i.val then L k j * H j i else 0) + L k next * H next i := by
    rw [← hprod k i, Finset.sum_congr rfl (fun j _ => key j),
      Finset.sum_add_distrib, htail]
  rw [eq_div_iff (hHnz i next hnext)]
  linarith [hsum]

/-- **Equation (11.15)**, the Aasen solve chain
`L z = P b`, `T y = z`, `L^T w = y`, `x = P w`. -/
def higham11_15_aasenSolveChain (n : ℕ)
    (Pmat L T : Fin n → Fin n → ℝ)
    (b z y w x : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, ∑ j : Fin n, L i j * z j = ∑ j : Fin n, Pmat i j * b j) ∧
  (∀ i : Fin n, ∑ j : Fin n, T i j * y j = z i) ∧
  (∀ i : Fin n, ∑ j : Fin n, L j i * w j = y i) ∧
  (∀ i : Fin n, x i = ∑ j : Fin n, Pmat i j * w j)

/-- **Theorem 11.8** componentwise Aasen backward-error target shape. -/
theorem higham11_8_aasen_backward_error_interface (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (bound : Fin n → Fin n → ℝ)
    (hsolve : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ bound i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i)) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA i j| ≤ bound i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  hsolve

/-- **Theorem 11.8** normwise Aasen bound
`||Delta A||_inf <= (n-1)^2 gamma_(15n+25) ||T_hat||_inf`. -/
def higham11_8_aasenNormwiseBackwardBound
    (n : ℕ) (ΔA_inf γ15n25 T_inf : ℝ) : Prop :=
  ΔA_inf ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * T_inf

/-- Aasen growth factor `rho_n = max_ij |t_ij| / max_ij |a_ij|`. -/
noncomputable def higham11_8_aasenGrowthFactor
    (Tmax Amax : ℝ) : ℝ :=
  Tmax / Amax

/-- The printed Aasen growth-factor bound `rho_n <= 4^(n-2)`. -/
def higham11_8_aasenGrowthBound (n : ℕ) (ρ_n : ℝ) : Prop :=
  ρ_n ≤ (4 : ℝ) ^ (n - 2)

/-! ## §11.3 Skew-symmetric block LDL^T factorization -/

/-- Real skew-symmetric matrix predicate, `A^T = -A`. -/
abbrev higham11_16_IsSkewSymmetric (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Prop :=
  IsSkewSymmetric n A

/-- A real skew-symmetric matrix has zero diagonal. -/
theorem higham11_16_skew_diag_zero (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hA : higham11_16_IsSkewSymmetric n A) :
    ∀ i : Fin n, A i i = 0 :=
  skewSymmetric_diag_zero n A hA

/-- **Equation (11.16)** source predicate:
`P A P^T = L D L^T` with skew block diagonal `D`. -/
abbrev higham11_16_SkewBlockLDLTSpec (n : ℕ)
    (A L D : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) : Prop :=
  SkewBlockLDLTSpec n A L D σ

/-- **Equation (11.16)** skew Schur complement
`B + C E^{-1} C^T`. -/
noncomputable def higham11_16_skewSchurComplement (m s : ℕ)
    (B : Fin m → Fin m → ℝ)
    (C : Fin m → Fin s → ℝ)
    (E_inv : Fin s → Fin s → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => B i j + ∑ p : Fin s, ∑ q : Fin s, C i p * E_inv p q * C j q

/-- **Algorithm 11.9** source pivot predicate for skew-symmetric block
LDL^T factorization. -/
abbrev higham11_9_SkewBunchPivotChoice
    (firstColumnTailZero : Prop) (pivotMagnitude : ℝ) (s : PivotSize) : Prop :=
  SkewBunchPivotChoice firstColumnTailZero pivotMagnitude s

/-- The skew-symmetric pivoting analysis gives `|L_ij| <= 1`. -/
theorem higham11_9_skew_L_entry_bound_interface (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (hL : ∀ i j : Fin n, |L i j| ≤ 1) :
    ∀ i j : Fin n, |L i j| ≤ 1 :=
  hL

/-- The skew-symmetric Schur-complement entry bound
`|s_ij| <= 3 max_ij |a_ij|`. -/
def higham11_9_skewSchurEntryBound
    (sij Amax : ℝ) : Prop :=
  |sij| ≤ 3 * Amax

/-- **Algorithm 11.9 multiplier bound**, proved: for a skew 2×2 pivot the
multiplier `c/a₂₁` (an entry of `CE⁻¹`, hence of `L`) satisfies `|c/a₂₁| ≤ 1`
whenever the pivot `a₂₁` has the largest magnitude (`|c| ≤ |a₂₁|`).  This is the
honest derivation behind `higham11_9_skew_L_entry_bound_interface`. -/
theorem higham11_9_skew_multiplier_bound (c a21 : ℝ)
    (ha : a21 ≠ 0) (hc : |c| ≤ |a21|) :
    |c / a21| ≤ 1 :=
  skew_twoByTwo_multiplier_bound c a21 ha hc

/-- **Algorithm 11.9 Schur-entry bound**, proved: the skew 2×2 Schur entry
`s = a_ij − (a_{i2}/a₂₁)a_{j1} + (a_{i1}/a₂₁)a_{j2}` satisfies the printed
`higham11_9_skewSchurEntryBound s M`, i.e. `|s| ≤ 3M`, when every active entry is
`≤ M` and the multipliers are `≤ 1` (`|a_{i1}|,|a_{i2}| ≤ |a₂₁|`). -/
theorem higham11_9_skew_schur_entry_bound
    (aij ai1 ai2 aj1 aj2 a21 M : ℝ) (ha : a21 ≠ 0)
    (hij : |aij| ≤ M) (hj1 : |aj1| ≤ M) (hj2 : |aj2| ≤ M)
    (hi1 : |ai1| ≤ |a21|) (hi2 : |ai2| ≤ |a21|) :
    higham11_9_skewSchurEntryBound
      (aij - (ai2 / a21) * aj1 + (ai1 / a21) * aj2) M :=
  skew_twoByTwo_schur_entry_bound aij ai1 ai2 aj1 aj2 a21 M
    ha hij hj1 hj2 hi1 hi2

/-- The printed skew growth-factor bound
`rho_n <= (sqrt 3)^(n-2)`. -/
def higham11_9_skewGrowthBound (n : ℕ) (ρ_n : ℝ) : Prop :=
  ρ_n ≤ (Real.sqrt 3) ^ (n - 2)

/-! ## Problems -/

/-- **Problem 11.2**, inertia formula for block diagonal `D`: each 2 by 2
indefinite block contributes one positive and one negative eigenvalue. -/
def higham11_problem_11_2_inertiaFormula
    (pPlus pMinus pZero q iPlus iMinus iZero : ℕ) : Prop :=
  iPlus = pPlus + q ∧ iMinus = pMinus + q ∧ iZero = pZero

/-- **Problem 11.3**, the simplified 2 by 2 Bunch-Kaufman decision tree. -/
def higham11_problem_11_3_twoByTwoPartialPivoting
    (α a11 a22 a21 : ℝ) (s : PivotSize) : Prop :=
  (|a11| ≥ α * |a21| ∧ s = PivotSize.one) ∨
  (|a22| ≥ α * |a21| ∧ s = PivotSize.one) ∨
  (|a11| < α * |a21| ∧ |a22| < α * |a21| ∧ s = PivotSize.two)

/-- **Problem 11.4**, SPD inputs to Bunch-Kaufman partial pivoting use only
positive 1 by 1 pivots, possibly after symmetric interchanges. -/
def higham11_problem_11_4_spdPartialPivotingOutcome
    (n : ℕ) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i ≠ j → D i j = 0) ∧
  (∀ i : Fin n, 0 < D i i)

/-- **Problem 11.9**, symmetric quasidefinite block matrix source predicate. -/
def higham11_problem_11_9_isSymmetricQuasidefinite
    (n m : ℕ)
    (H : Fin n → Fin n → ℝ)
    (G : Fin m → Fin m → ℝ) : Prop :=
  IsSymPosDef n H ∧ IsSymPosDef m G

/-! ## Problem proof-completion lemmas -/

/-- **Problem 11.1**, determinant of the principal `2 x 2` block on rows
and columns `i,j`. -/
def higham11_problem_11_1_principalTwoByTwoDet {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  A i i * A j j - A i j * A j i

/-- **Problem 11.1**: if every `1 x 1` and `2 x 2` principal pivot block of
a symmetric matrix is singular, then the matrix is zero.  This is the exact
Appendix A argument used to justify the existence of a nonsingular pivot block
for any nonzero symmetric matrix. -/
theorem higham11_problem_11_1_zero_of_symmetric_singular_principal_pivots
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hSym : ∀ i j : Fin n, A i j = A j i)
    (hOne : ∀ i : Fin n, A i i = 0)
    (hTwo : ∀ i j : Fin n,
      higham11_problem_11_1_principalTwoByTwoDet A i j = 0) :
    ∀ i j : Fin n, A i j = 0 := by
  intro i j
  by_cases hij : i = j
  · subst i
    exact hOne j
  · have hdet :
        -(A i j * A i j) = 0 := by
      simpa [higham11_problem_11_1_principalTwoByTwoDet, hOne i, hOne j,
        hSym j i] using hTwo i j
    have hsq : (A i j) ^ 2 = 0 := by
      nlinarith
    exact sq_eq_zero_iff.mp hsq

/-- **Problem 11.2**, exact `2 x 2` symmetric pivot block. -/
def higham11_problem_11_2_twoByTwoPivot (a b c : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then a
    else if i.val = 0 ∧ j.val = 1 then b
    else if i.val = 1 ∧ j.val = 0 then b
    else c

/-- **Problem 11.2**, overflow-avoiding inverse formula from Appendix A:
`E^{-1} = 1/(b*((a/b)*(c/b)-1)) * [[c/b,-1],[-1,a/b]]`. -/
noncomputable def higham11_problem_11_2_twoByTwoPivotScaledInverse
    (a b c : ℝ) : Fin 2 → Fin 2 → ℝ :=
  let d : ℝ := b * ((a / b) * (c / b) - 1)
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then (c / b) / d
    else if i.val = 0 ∧ j.val = 1 then (-1) / d
    else if i.val = 1 ∧ j.val = 0 then (-1) / d
    else (a / b) / d

/-- **Problem 11.2**, proved inverse certificate for the Appendix A scaled
`2 x 2` pivot inverse formula. -/
theorem higham11_problem_11_2_twoByTwoPivot_scaledInverse_spec
    (a b c : ℝ) (hb : b ≠ 0)
    (hd : b * ((a / b) * (c / b) - 1) ≠ 0) :
    higham11_2_NonsingularPivotBlock 2
      (higham11_problem_11_2_twoByTwoPivot a b c)
      (higham11_problem_11_2_twoByTwoPivotScaledInverse a b c) := by
  have hd_eq :
      b * ((a / b) * (c / b) - 1) = (a * c - b ^ 2) / b := by
    field_simp [hb]
  have hdet_ne : a * c - b ^ 2 ≠ 0 := by
    intro hzero
    apply hd
    rw [hd_eq, hzero, zero_div]
  have hdet_ne_comm : c * a - b ^ 2 ≠ 0 := by
    intro hzero
    apply hdet_ne
    rwa [mul_comm c a] at hzero
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [higham11_problem_11_2_twoByTwoPivot,
      higham11_problem_11_2_twoByTwoPivotScaledInverse, Fin.sum_univ_two] <;>
    field_simp [hb, hdet_ne, hdet_ne_comm] <;>
    ring_nf

/-- **Problem 11.2**, determinant negativity from the common Appendix A
pivot-growth estimate `det(E) <= (alpha^2 - 1) * beta^2`, with
`alpha^2 < 1` and nonzero pivot scale `beta`. -/
theorem higham11_problem_11_2_det_negative_of_pivot_bound
    (α β detE : ℝ) (hα : α ^ 2 < 1) (hβ : β ≠ 0)
    (hdet : detE ≤ (α ^ 2 - 1) * β ^ 2) :
    detE < 0 := by
  have hβsq : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hcoef : α ^ 2 - 1 < 0 := by linarith
  have hrhs : (α ^ 2 - 1) * β ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hcoef hβsq
  exact lt_of_le_of_lt hdet hrhs

/-- **Problem 11.4**, local SPD obstruction: a real SPD matrix cannot have a
`2 x 2` principal pivot block whose determinant is negative. -/
theorem higham11_problem_11_4_spd_no_negative_twoByTwo_principal_det
    {n : ℕ} (A : Fin n → Fin n → ℝ) (hSPD : IsSymPosDef n A)
    {i j : Fin n} (hij : i ≠ j) :
    ¬ A i i * A j j - A i j ^ 2 < 0 := by
  have hpos := higham10_problem_10_1_two_by_two_minor_pos A hSPD hij
  linarith

/-- **Problem 11.7**, core algebra for the modified Bunch-Kaufman test.
If the `2 x 2` principal block is positive definite, the modified
`omega_r = ||A(:,r)||_inf` quantity dominates `a_rr`, and `alpha <= 1`, then
the second pivot test `|a_11| omega_r >= alpha * omega_1^2` is passed. -/
theorem higham11_problem_11_7_modifiedOmega_second_test_from_spd_minor
    (α a11 arr ar1 ωr : ℝ)
    (ha11 : 0 < a11)
    (hminor : 0 < a11 * arr - ar1 ^ 2)
    (harr_le : arr ≤ ωr)
    (hα : α ≤ 1) :
    α * ar1 ^ 2 ≤ |a11| * ωr := by
  have har_sq_nonneg : 0 ≤ ar1 ^ 2 := sq_nonneg ar1
  have har_sq_lt : ar1 ^ 2 < a11 * arr := by linarith
  have harr_to_ω : a11 * arr ≤ a11 * ωr :=
    mul_le_mul_of_nonneg_left harr_le (le_of_lt ha11)
  have har_sq_le_ω : ar1 ^ 2 ≤ a11 * ωr :=
    le_trans (le_of_lt har_sq_lt) harr_to_ω
  have hα_sq : α * ar1 ^ 2 ≤ ar1 ^ 2 :=
    calc
      α * ar1 ^ 2 ≤ 1 * ar1 ^ 2 :=
        mul_le_mul_of_nonneg_right hα har_sq_nonneg
      _ = ar1 ^ 2 := by ring
  rw [abs_of_pos ha11]
  exact le_trans hα_sq har_sq_le_ω

/-- **Problem 11.8**, the permuted matrix obtained from the example (11.6)
under complete pivoting or rook pivoting. -/
noncomputable def higham11_problem_11_8_rookCompleteExampleA
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1
    else if i.val = 0 ∧ j.val = 1 then 1
    else if i.val = 1 ∧ j.val = 0 then 1
    else if i.val = 1 ∧ j.val = 2 then ε
    else if i.val = 2 ∧ j.val = 1 then ε
    else if i.val = 2 ∧ j.val = 2 then 1
    else 0

/-- **Problem 11.8**, the lower triangular factor produced for the
complete/rook-pivoting factorization of the example (11.6). -/
noncomputable def higham11_problem_11_8_rookCompleteExampleL
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = j.val then 1
    else if i.val = 1 ∧ j.val = 0 then 1
    else if i.val = 2 ∧ j.val = 1 then -ε
    else 0

/-- **Problem 11.8**, the diagonal factor
`diag(1, -1, 1 + eps^2)`. -/
noncomputable def higham11_problem_11_8_rookCompleteExampleD
    (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1
    else if i.val = 1 ∧ j.val = 1 then -1
    else if i.val = 2 ∧ j.val = 2 then 1 + ε ^ 2
    else 0

/-- **Problem 11.8**, exact algebraic factorization produced by complete
pivoting and rook pivoting for the matrix in (11.6). -/
theorem higham11_problem_11_8_rookCompleteExample_factorization
    (ε : ℝ) :
    ∀ i j : Fin 3,
      ∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
        higham11_problem_11_8_rookCompleteExampleL ε i k₁ *
          higham11_problem_11_8_rookCompleteExampleD ε k₁ k₂ *
          higham11_problem_11_8_rookCompleteExampleL ε j k₂ =
      higham11_problem_11_8_rookCompleteExampleA ε i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, higham11_problem_11_8_rookCompleteExampleA,
      higham11_problem_11_8_rookCompleteExampleL,
      higham11_problem_11_8_rookCompleteExampleD]
  ring

/-- **Problem 11.9(a)**, kernel-trivial form of nonsingularity for a
symmetric quasidefinite block matrix
`[[H, B^T], [B, -G]]` with `H` and `G` SPD.  This is the Appendix A argument
written directly on the block equations, avoiding a separate determinant API:
multiply the two block rows by `u` and `v`, cancel the `B` cross terms, and use
positive definiteness of `H` and `G`. -/
theorem higham11_problem_11_9_quasidefinite_kernel_trivial
    {n m : ℕ} (H : Fin n → Fin n → ℝ)
    (B : Fin m → Fin n → ℝ) (G : Fin m → Fin m → ℝ)
    (hH : IsSymPosDef n H) (hG : IsSymPosDef m G)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (h₁ : ∀ i : Fin n,
      (∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k) = 0)
    (h₂ : ∀ k : Fin m,
      (∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l) = 0) :
    (∀ i : Fin n, u i = 0) ∧ (∀ k : Fin m, v k = 0) := by
  let qH : ℝ := ∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j
  let qG : ℝ := ∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l
  let cross₁ : ℝ := ∑ i : Fin n, ∑ k : Fin m, u i * B k i * v k
  let cross₂ : ℝ := ∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i
  have hrow_zero :
      ∑ i : Fin n,
        u i * ((∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k)) = 0 := by
    calc
      ∑ i : Fin n,
          u i * ((∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k))
          = ∑ i : Fin n, u i * 0 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [h₁ i]
      _ = 0 := by simp
  have hcol_zero :
      ∑ k : Fin m,
        v k * ((∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l)) = 0 := by
    calc
      ∑ k : Fin m,
          v k * ((∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l))
          = ∑ k : Fin m, v k * 0 := by
            apply Finset.sum_congr rfl
            intro k _
            rw [h₂ k]
      _ = 0 := by simp
  have hrow_expand :
      ∑ i : Fin n,
        u i * ((∑ j : Fin n, H i j * u j) + (∑ k : Fin m, B k i * v k)) =
      qH + cross₁ := by
    have hHsum :
        ∑ i : Fin n, u i * (∑ j : Fin n, H i j * u j) = qH := by
      dsimp [qH]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hBsum :
        ∑ i : Fin n, u i * (∑ k : Fin m, B k i * v k) = cross₁ := by
      dsimp [cross₁]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hHsum, hBsum]
  have hcol_expand :
      ∑ k : Fin m,
        v k * ((∑ i : Fin n, B k i * u i) - (∑ l : Fin m, G k l * v l)) =
      cross₂ - qG := by
    have hBsum :
        ∑ k : Fin m, v k * (∑ i : Fin n, B k i * u i) = cross₂ := by
      dsimp [cross₂]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hGsum :
        ∑ k : Fin m, v k * (∑ l : Fin m, G k l * v l) = qG := by
      dsimp [qG]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hBsum, hGsum]
  have hcross : cross₂ = cross₁ := by
    dsimp [cross₁, cross₂]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hrow_q : qH + cross₁ = 0 := by
    rw [← hrow_expand]
    exact hrow_zero
  have hcol_q : cross₁ - qG = 0 := by
    rw [← hcross, ← hcol_expand]
    exact hcol_zero
  have hqsum : qH + qG = 0 := by
    nlinarith
  have hqH_nonneg : 0 ≤ qH := by
    by_cases hu : ∃ i : Fin n, u i ≠ 0
    · exact le_of_lt (hH.2 u hu)
    · push_neg at hu
      simp [qH, hu]
  have hqG_nonneg : 0 ≤ qG := by
    by_cases hv : ∃ k : Fin m, v k ≠ 0
    · exact le_of_lt (hG.2 v hv)
    · push_neg at hv
      simp [qG, hv]
  have hqH_zero : qH = 0 := by nlinarith
  have hqG_zero : qG = 0 := by nlinarith
  constructor
  · by_contra hu
    push_neg at hu
    have hpos := hH.2 u hu
    nlinarith
  · by_contra hv
    push_neg at hv
    have hpos := hG.2 v hv
    nlinarith

/-- **Problem 11.9(c)**, concrete block-quadratic form for
`A S = [[H, -B^T], [B, G]]`.  The off-diagonal block terms cancel, leaving the
sum of the SPD quadratic forms for `H` and `G`. -/
theorem higham11_problem_11_9_signed_block_quadratic_pos
    {n m : ℕ} (H : Fin n → Fin n → ℝ)
    (B : Fin m → Fin n → ℝ) (G : Fin m → Fin m → ℝ)
    (hH : IsSymPosDef n H) (hG : IsSymPosDef m G)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (hnz : (∃ i : Fin n, u i ≠ 0) ∨ (∃ k : Fin m, v k ≠ 0)) :
    0 <
      (∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j) +
      (∑ i : Fin n, ∑ k : Fin m, u i * (-B k i) * v k) +
      (∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i) +
      (∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l) := by
  let qH : ℝ := ∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j
  let qG : ℝ := ∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l
  let cross₁ : ℝ := ∑ i : Fin n, ∑ k : Fin m, u i * B k i * v k
  let cross₂ : ℝ := ∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i
  have hcross : cross₂ = cross₁ := by
    dsimp [cross₁, cross₂]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hneg :
      (∑ i : Fin n, ∑ k : Fin m, u i * (-B k i) * v k) = -cross₁ := by
    dsimp [cross₁]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpos_cross :
      (∑ k : Fin m, ∑ i : Fin n, v k * B k i * u i) = cross₂ := by
    rfl
  have hqH_nonneg : 0 ≤ qH := by
    by_cases hu : ∃ i : Fin n, u i ≠ 0
    · exact le_of_lt (hH.2 u hu)
    · push_neg at hu
      simp [qH, hu]
  have hqG_nonneg : 0 ≤ qG := by
    by_cases hv : ∃ k : Fin m, v k ≠ 0
    · exact le_of_lt (hG.2 v hv)
    · push_neg at hv
      simp [qG, hv]
  have hq_pos : 0 < qH + qG := by
    rcases hnz with hu | hv
    · have hpos := hH.2 u hu
      nlinarith
    · have hpos := hG.2 v hv
      nlinarith
  rw [show
      (∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j) = qH by rfl]
  rw [show
      (∑ k : Fin m, ∑ l : Fin m, v k * G k l * v l) = qG by rfl]
  rw [hneg, hpos_cross, hcross]
  nlinarith

/-- **Problem 11.9(c)** reuse of Chapter 10: a matrix whose symmetric part is
SPD is nonsymmetric positive definite.  The block computation
`(AS + (AS)^T)/2 = diag(H,G)` is the remaining block-layout step. -/
theorem higham11_problem_11_9_nonsymPosDef_of_symPartSPD {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n (symmetricPart n A)) :
    IsNonsymPosDef n A :=
  (nonsymPosDef_iff_symPartSPD n A).mpr hSPD

end LeanFpAnalysis.FP
