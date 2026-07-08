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

/-- **Theorem 11.3 inductive step (trailing-block fl backward error)**, Higham
[608,1997] §4.2: with computed 1×1 multipliers and a recursive factorization
`L_S,D_S` approximating the computed Schur complement within `Bs`, the assembled
factors satisfy `|(L̂D̂L̂ᵀ)_{i+1,j+1} − A_{i+1,j+1}| ≤ 2γ₃(|A_{i+1,j+1}| +
|A_{i+1,0}A_{0,j+1}/A00|) + Bs i j` on the trailing block. -/
theorem higham11_3_fl_blockLDLT_trailing_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (hval : gammaValid fp 3)
    (L_S D_S : Fin n → Fin n → ℝ) (Bs : Fin n → Fin n → ℝ)
    (hIH : ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂)
        - fp.fl_sub (A i.succ j.succ)
            (fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ))| ≤ Bs i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L i.succ k₁ * D k₁ k₂ * L j.succ k₂) - A i.succ j.succ|
        ≤ 2 * gamma fp 3 * (|A i.succ j.succ|
            + |A i.succ 0 * A 0 j.succ / A 0 0|) + Bs i j :=
  fl_blockLDLT_trailing_bound n fp A he hsym1 hval L_S D_S Bs hIH L D
    hLcol hLtr hD00 hD0s hDs0 hDtr

/-- **Theorem 11.3 pivot-row/col fl backward error**: `(L̂D̂L̂ᵀ)_{0,0} = A00`
exactly, and `|(L̂D̂L̂ᵀ)_{0,j+1} − A_{0,j+1}| ≤ u·|A_{0,j+1}|` — the pivot-row half
of the 1×1-stage assemble step (trailing half is `higham11_3_fl_blockLDLT_trailing_bound`). -/
theorem higham11_3_fl_blockLDLT_pivot_row_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0) :
    (∑ k₁, ∑ k₂, L 0 k₁ * D k₁ k₂ * L 0 k₂) = A 0 0
    ∧ ∀ j : Fin n,
        |(∑ k₁, ∑ k₂, L 0 k₁ * D k₁ k₂ * L j.succ k₂) - A 0 j.succ|
          ≤ fp.u * |A 0 j.succ| :=
  fl_blockLDLT_pivot_row_bound n fp A he hsym1 L D hL00 hLcol hL0s hD00 hD0s

/-- **Theorem 11.3 pivot-column fl backward error**:
`|(L̂D̂L̂ᵀ)_{i+1,0} − A_{i+1,0}| ≤ u·|A_{i+1,0}|` — the pivot-column case,
completing all four index cases of the single 1×1-pivot fl assemble step. -/
theorem higham11_3_fl_blockLDLT_pivot_col_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (he : A 0 0 ≠ 0)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hD00 : D 0 0 = A 0 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0) :
    ∀ i : Fin n,
      |(∑ k₁, ∑ k₂, L i.succ k₁ * D k₁ k₂ * L 0 k₂) - A i.succ 0|
        ≤ fp.u * |A i.succ 0| :=
  fl_blockLDLT_pivot_col_bound n fp A he L D hL00 hLcol hL0s hD00 hDs0

/-- **Theorem 11.3 one-stage all-index fl backward-error envelope**: the four
index cases of one rounded 1×1-pivot block-LDLᵀ assemble step are packaged into
one entrywise bound.  The pivot entry is exact, pivot row/column entries have
`u|A|` error, and trailing entries have the per-stage Schur error plus the
recursive trailing envelope `Bs`.  This is the next local bridge toward the full
block-matrix induction; the multi-stage recursion remains open in the report. -/
noncomputable abbrev higham11_3_fl_oneByOneStageBound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (Bs : Fin n → Fin n → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  flBlockLDLTOneByOneStageBound n fp A Bs

/-- **Theorem 11.3 one-stage all-index fl backward-error bound**:
`|(L̂D̂L̂ᵀ) I J - A I J|` is bounded by
`higham11_3_fl_oneByOneStageBound` for every index pair of a single rounded
1×1-pivot stage. -/
theorem higham11_3_fl_blockLDLT_oneByOne_stage_bound (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (hval : gammaValid fp 3)
    (L_S D_S : Fin n → Fin n → ℝ) (Bs : Fin n → Fin n → ℝ)
    (hIH : ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂)
        - fp.fl_sub (A i.succ j.succ)
            (fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ))| ≤ Bs i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ I J : Fin (n + 1),
      |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
        ≤ higham11_3_fl_oneByOneStageBound n fp A Bs I J :=
  fl_blockLDLT_oneByOne_stage_bound n fp A he hsym1 hval L_S D_S Bs hIH L D
    hL00 hLcol hL0s hLtr hD00 hD0s hDs0 hDtr

/-- **Theorem 11.3 rounded Schur complement** for the all-1×1-pivot path:
`fl(Aᵢⱼ - fl(fl(Aᵢ₀/A₀₀) A₀ⱼ))`. -/
noncomputable abbrev higham11_3_fl_schurCompl (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin n → Fin n → ℝ :=
  flSchurCompl n fp A

/-- Stored-symmetric rounded Schur complement for Theorem 11.3's all-1×1 path:
compute one triangle and copy it across the diagonal. -/
noncomputable abbrev higham11_3_fl_storedSymSchurCompl (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin n → Fin n → ℝ :=
  flStoredSymSchurCompl n fp A

/-- The stored-symmetric rounded Schur complement is symmetric by construction. -/
theorem higham11_3_fl_storedSymSchurCompl_symm (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∀ i j : Fin n, higham11_3_fl_storedSymSchurCompl n fp A i j =
      higham11_3_fl_storedSymSchurCompl n fp A j i :=
  flStoredSymSchurCompl_symm n fp A

/-- The stored-symmetric rounded Schur complement supplies the first-row /
first-column equality used by the one-stage floating assemble theorem. -/
theorem higham11_3_fl_storedSymSchurCompl_first_row_col (n : ℕ) (fp : FPModel)
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) :
    ∀ i : Fin n, higham11_3_fl_storedSymSchurCompl (n + 1) fp A 0 i.succ =
      higham11_3_fl_storedSymSchurCompl (n + 1) fp A i.succ 0 :=
  flStoredSymSchurCompl_first_row_col n fp A

/-- Entrywise discrepancy between stored-symmetric and raw rounded Schur
complements. -/
noncomputable abbrev higham11_3_fl_storedSymSchurDefect (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin n → Fin n → ℝ :=
  flStoredSymSchurDefect n fp A

/-- **Theorem 11.3 stored-Schur one-stage bridge**: if the recursive trailing
factors approximate the stored-symmetric rounded Schur complement, the existing
one-stage LDLᵀ bound applies with the stored trailing envelope plus the explicit
stored-vs-raw Schur defect. -/
theorem higham11_3_fl_blockLDLT_oneByOne_stage_bound_of_stored_schur
    (n : ℕ) (fp : FPModel)
    (A : Fin (n + 1) → Fin (n + 1) → ℝ)
    (he : A 0 0 ≠ 0) (hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0)
    (hval : gammaValid fp 3)
    (L_S D_S B : Fin n → Fin n → ℝ)
    (hIH : ∀ i j : Fin n,
      |(∑ k₁, ∑ k₂, L_S i k₁ * D_S k₁ k₂ * L_S j k₂)
        - higham11_3_fl_storedSymSchurCompl n fp A i j| ≤ B i j)
    (L D : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hL00 : L 0 0 = 1)
    (hLcol : ∀ i : Fin n, L i.succ 0 = fp.fl_div (A i.succ 0) (A 0 0))
    (hL0s : ∀ j : Fin n, L 0 j.succ = 0)
    (hLtr : ∀ i j : Fin n, L i.succ j.succ = L_S i j)
    (hD00 : D 0 0 = A 0 0)
    (hD0s : ∀ j : Fin n, D 0 j.succ = 0)
    (hDs0 : ∀ i : Fin n, D i.succ 0 = 0)
    (hDtr : ∀ i j : Fin n, D i.succ j.succ = D_S i j) :
    ∀ I J : Fin (n + 1),
      |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
        ≤ higham11_3_fl_oneByOneStageBound n fp A
          (fun i j => B i j + higham11_3_fl_storedSymSchurDefect n fp A i j) I J :=
  fl_blockLDLT_oneByOne_stage_bound_of_stored_schur n fp A he hsym1 hval
    L_S D_S B hIH L D hL00 hLcol hL0s hLtr hD00 hD0s hDs0 hDtr

/-- Recursive nonzero-pivot condition for the stored-symmetric all-1×1
floating block-LDLᵀ path. -/
noncomputable abbrev higham11_3_FlStoredAllOnePivots (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  FlStoredAllOnePivots fp n A

/-- Recursive entrywise envelope for the stored-symmetric all-1×1 floating
block-LDLᵀ path. -/
noncomputable abbrev higham11_3_fl_storedAllOneByOneBound (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  flBlockLDLTStoredAllOneByOneBound fp n A

/-- **Theorem 11.3 stored-symmetric all-1×1 recursive fl bound**: for a symmetric
input whose stored-symmetric rounded Schur path has nonzero pivots, there exist
computed-style factors `L̂,D̂` whose product approximates `A` entrywise within
`higham11_3_fl_storedAllOneByOneBound`. -/
theorem higham11_3_fl_blockLDLT_stored_all_oneByOne_bound (fp : FPModel)
    (hval : gammaValid fp 3) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hp : higham11_3_FlStoredAllOnePivots fp n A) :
    ∃ L D : Fin n → Fin n → ℝ,
      ∀ I J,
        |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
          ≤ higham11_3_fl_storedAllOneByOneBound fp n A I J :=
  fl_blockLDLT_stored_all_oneByOne_bound fp hval n A hsym hp

/-- Recursive rounded-pivot side condition for Theorem 11.3's all-1×1 path. -/
noncomputable abbrev higham11_3_FlAllOneSymmetricPivots (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  FlAllOneSymmetricPivots fp n A

/-- Recursive entrywise envelope obtained by iterating the one-stage floating
block-LDLᵀ bound along the rounded all-1×1-pivot path. -/
noncomputable abbrev higham11_3_fl_allOneByOneBound (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  flBlockLDLTAllOneByOneBound fp n A

/-- **Theorem 11.3 all-1×1-pivot recursive fl bound**: under the rounded
all-1×1 pivot/symmetry side condition, there exist computed-style factors
`L̂,D̂` whose product approximates `A` entrywise within
`higham11_3_fl_allOneByOneBound`. -/
theorem higham11_3_fl_blockLDLT_all_oneByOne_bound (fp : FPModel)
    (hval : gammaValid fp 3) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hp : higham11_3_FlAllOneSymmetricPivots fp n A) :
    ∃ L D : Fin n → Fin n → ℝ,
      ∀ I J,
        |(∑ k₁, ∑ k₂, L I k₁ * D k₁ k₂ * L J k₂) - A I J|
          ≤ higham11_3_fl_allOneByOneBound fp n A I J :=
  fl_blockLDLT_all_oneByOne_bound fp hval n A hp

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

/-- Bunch's tridiagonal pivoting parameter is strictly positive. -/
theorem higham11_6_bunch_tridiagonal_alpha_pos :
    0 < higham11_6_bunchTridiagonalAlpha :=
  bunch_tridiagonal_alpha_pos

/-- Bunch's tridiagonal pivoting parameter is less than one. -/
theorem higham11_6_bunch_tridiagonal_alpha_lt_one :
    higham11_6_bunchTridiagonalAlpha < 1 :=
  bunch_tridiagonal_alpha_lt_one

/-- The tridiagonal pivoting parameter satisfies `alpha^2 = 1 - alpha`. -/
theorem higham11_6_bunch_tridiagonal_alpha_sq :
    higham11_6_bunchTridiagonalAlpha ^ 2 =
      1 - higham11_6_bunchTridiagonalAlpha :=
  bunch_tridiagonal_alpha_sq

/-- **Algorithm 11.6** source decision predicate for Bunch's tridiagonal
pivot-size strategy. -/
abbrev higham11_6_BunchTridiagonalPivotChoice
    (σ a11 a21 : ℝ) (s : PivotSize) : Prop :=
  BunchTridiagonalPivotChoice σ a11 a21 s

/-- **Algorithm 11.6**, one-by-one branch threshold extraction. -/
theorem higham11_6_tridiagonal_pivot_choice_one_threshold (σ a11 a21 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one) :
    σ * |a11| ≥ higham11_6_bunchTridiagonalAlpha * a21 ^ 2 :=
  bunch_tridiagonal_pivot_choice_one_threshold σ a11 a21 hchoice

/-- **Algorithm 11.6**, two-by-two branch threshold extraction. -/
theorem higham11_6_tridiagonal_pivot_choice_two_threshold (σ a11 a21 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two) :
    σ * |a11| < higham11_6_bunchTridiagonalAlpha * a21 ^ 2 :=
  bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice

/-- **Algorithm 11.6**, constructor for the one-by-one branch from the printed
threshold test. -/
theorem higham11_6_tridiagonal_pivot_choice_one_of_threshold (σ a11 a21 : ℝ)
    (hthreshold : σ * |a11| ≥ higham11_6_bunchTridiagonalAlpha * a21 ^ 2) :
    higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one :=
  bunch_tridiagonal_pivot_choice_one_of_threshold σ a11 a21 hthreshold

/-- **Algorithm 11.6**, constructor for the two-by-two branch from the printed
strict threshold test. -/
theorem higham11_6_tridiagonal_pivot_choice_two_of_threshold (σ a11 a21 : ℝ)
    (hthreshold : σ * |a11| < higham11_6_bunchTridiagonalAlpha * a21 ^ 2) :
    higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two :=
  bunch_tridiagonal_pivot_choice_two_of_threshold σ a11 a21 hthreshold

/-- **Algorithm 11.6**, one-by-one branch nonsingularity: if the neighboring
offdiagonal entry is nonzero, the accepted scalar pivot is nonzero. -/
theorem higham11_6_tridiagonal_pivot_choice_one_a11_ne_zero_of_a21_ne_zero
    (σ a11 a21 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one)
    (ha21 : a21 ≠ 0) :
    a11 ≠ 0 :=
  bunch_tridiagonal_pivot_choice_one_a11_ne_zero_of_a21_ne_zero σ a11 a21
    hchoice ha21

/-- **Algorithm 11.6**, two-by-two branch nonsingularity with a nonnegative
left-hand side in the pivot test. -/
theorem higham11_6_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg
    (σ a11 a21 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hleft_nonneg : 0 ≤ σ * |a11|) :
    a21 ≠ 0 :=
  bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg σ a11 a21
    hchoice hleft_nonneg

/-- **Algorithm 11.6**, two-by-two branch nonsingularity when `σ` is
nonnegative. -/
theorem higham11_6_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg
    (σ a11 a21 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 ≤ σ) :
    a21 ≠ 0 :=
  bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21
    hchoice hσ

/-- **Theorem 11.7 dependency**, two-by-two tridiagonal pivot determinant:
Algorithm 11.6's two-pivot branch plus `|a22| ≤ σ` gives the determinant lower
bound for the accepted `2 × 2` block. -/
theorem higham11_7_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa22 : |a22| ≤ σ) :
    (1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2 ≤
      |a11 * a22 - a21 ^ 2| :=
  bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound σ a11 a21 a22
    hchoice hσa22

/-- **Theorem 11.7 dependency**, nonsingularity of the accepted `2 × 2`
tridiagonal pivot block under the Algorithm 11.6 two-pivot branch. -/
theorem higham11_7_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa22 : |a22| ≤ σ) :
    a11 * a22 - a21 ^ 2 ≠ 0 :=
  bunch_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound σ a11 a21 a22
    hchoice hσa22

/-- **Theorem 11.7 dependency**, inverse-entry bounds for the accepted `2 × 2`
tridiagonal pivot block. -/
theorem higham11_7_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ) :
    |a22 / (a11 * a22 - a21 ^ 2)| ≤
        σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) ∧
    |(-a21) / (a11 * a22 - a21 ^ 2)| ≤
        |a21| / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) ∧
    |a11 / (a11 * a22 - a21 ^ 2)| ≤
        σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) :=
  bunch_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound σ a11 a21 a22
    hchoice hσa11 hσa22

/-- **Theorem 11.7 atomic fl update**, for the scalar Schur update produced by
an accepted `2 × 2` tridiagonal pivot. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_schur_step_error
    (fp : FPModel) (b c f : ℝ) (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 * (|b| + |c * f * c|) ∧
      fp.fl_sub b (fp.fl_mul (fp.fl_mul c f) c) = (b - c * f * c) + Δ :=
  fl_tridiagonal_twoByTwo_schur_step_error fp b c f hval

/-- **Theorem 11.7 atomic fl update**, specialized to Algorithm 11.6's accepted
`2 × 2` tridiagonal pivot and the corresponding inverse-entry budget. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound
    (fp : FPModel) (σ a11 a21 a22 b c : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 *
        (|b| + |c| *
          (σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + Δ :=
  fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound fp σ a11 a21 a22 b c
    hchoice hσa11 hσa22 hval

/-- **Theorem 11.7 atomic backward-error form**, for the scalar Schur update
after an accepted `2 × 2` tridiagonal pivot. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound
    (fp : FPModel) (σ a11 a21 a22 b c : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hval : gammaValid fp 3) :
    ∃ Δb : ℝ,
      |Δb| ≤ gamma fp 3 *
        (|b| + |c| *
          (σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b + Δb) - c * (a11 / (a11 * a22 - a21 ^ 2)) * c :=
  fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound fp
    σ a11 a21 a22 b c hchoice hσa11 hσa22 hval

/-- **Theorem 11.7 local uniform bound**, turning the scalar `2 × 2`
tridiagonal pivot backward error into an `Amax`/`κ` stage budget. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hval : gammaValid fp 3) :
    ∃ Δb : ℝ,
      |Δb| ≤ gamma fp 3 * (Amax + Amax * κ * Amax) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b + Δb) - c * (a11 / (a11 * a22 - a21 ^ 2)) * c :=
  fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound fp
    σ a11 a21 a22 b c Amax κ hchoice hσa11 hσa22 hAmax hκ hb hc
    hratio hval

/-- **Theorem 11.7 one-stage trailing block envelope**, for the single trailing
entry affected by a `2 × 2` pivot in a symmetric tridiagonal matrix. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hval : gammaValid fp 3) :
    ∃ ΔS : Fin 1 → Fin 1 → ℝ,
      (∀ i j : Fin 1, |ΔS i j| ≤ gamma fp 3 * (Amax + Amax * κ * Amax)) ∧
      (∀ i j : Fin 1,
        fp.fl_sub b
            (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
          = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + ΔS i j) :=
  fl_tridiagonal_twoByTwo_trailing_one_stage_bound fp
    σ a11 a21 a22 b c Amax κ hchoice hσa11 hσa22 hAmax hκ hb hc
    hratio hval

/-- **Theorem 11.7 local printed-budget handoff**, for the single trailing block
affected by an accepted `2 × 2` tridiagonal pivot. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔS : Fin 1 → Fin 1 → ℝ,
      (∀ i j : Fin 1, |ΔS i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin 1,
        fp.fl_sub b
            (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
          = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + ΔS i j) :=
  fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound fp
    σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
    hb hc hratio hbudget hval

/-- **Theorem 11.7 first-stage embedding**, placing the printed-budget trailing
scalar perturbation from an accepted `2 × 2` tridiagonal pivot into the ambient
`3 × 3` tridiagonal block-LDLᵀ step with zeros outside the trailing entry. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin 3 → Fin 3 → ℝ,
      (∀ i j : Fin 3, |ΔA i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin 3,
        i ≠ (⟨2, by decide⟩ : Fin 3) ∨
          j ≠ (⟨2, by decide⟩ : Fin 3) →
        ΔA i j = 0) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (⟨2, by decide⟩ : Fin 3) (⟨2, by decide⟩ : Fin 3) :=
  fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three fp
    σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
    hb hc hratio hbudget hval

/-- Local index of the first trailing scalar after a leading `2 × 2`
tridiagonal pivot inside a block of size `n+3`. -/
abbrev higham11_7_tridiagonalTwoByTwoFirstTrailingIndex (n : ℕ) :
    Fin (n + 3) :=
  tridiagonalTwoByTwoFirstTrailingIndex n

/-- Offset embedding of the recursive trailing subproblem after a leading
`2 × 2` tridiagonal pivot. -/
abbrev higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex (n : ℕ)
    (i : Fin (n + 1)) : Fin (n + 3) :=
  tridiagonalTwoByTwoTrailingSubproblemIndex n i

@[simp] theorem higham11_7_tridiagonalTwoByTwoFirstTrailingIndex_val (n : ℕ) :
    (higham11_7_tridiagonalTwoByTwoFirstTrailingIndex n).val = 2 :=
  tridiagonalTwoByTwoFirstTrailingIndex_val n

@[simp] theorem higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex_val
    (n : ℕ) (i : Fin (n + 1)) :
    (higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex n i).val =
      i.val + 2 :=
  tridiagonalTwoByTwoTrailingSubproblemIndex_val n i

@[simp] theorem higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex_zero
    (n : ℕ) :
    higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex n 0 =
      higham11_7_tridiagonalTwoByTwoFirstTrailingIndex n :=
  tridiagonalTwoByTwoTrailingSubproblemIndex_zero n

/-- The recursive trailing-subproblem embedding after a leading tridiagonal
`2 × 2` pivot is injective. -/
theorem higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex_injective (n : ℕ) :
    Function.Injective
      (higham11_7_tridiagonalTwoByTwoTrailingSubproblemIndex n) :=
  tridiagonalTwoByTwoTrailingSubproblemIndex_injective n

/-- **Theorem 11.7 local recursion embedding**, placing the printed-budget
trailing scalar perturbation from an accepted `2 × 2` tridiagonal pivot into an
ambient local block of size `n+3`, with zeros outside the first trailing entry. -/
theorem higham11_7_fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : higham11_6_BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - higham11_6_bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin (n + 3),
        i ≠ higham11_7_tridiagonalTwoByTwoFirstTrailingIndex n ∨
          j ≠ higham11_7_tridiagonalTwoByTwoFirstTrailingIndex n →
        ΔA i j = 0) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (higham11_7_tridiagonalTwoByTwoFirstTrailingIndex n)
            (higham11_7_tridiagonalTwoByTwoFirstTrailingIndex n) :=
  fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed n fp
    σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
    hb hc hratio hbudget hval

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

/-- **Equation (11.14) floating-point scalar update**, relative-error form.
The computed scalar update `fl(fl(a - s) / h)` equals the exact update
`(a - s) / h` multiplied by a two-operation relative error bounded by `γ₂`.
This is the local fl ingredient for the Aasen next-column recurrence. -/
theorem higham11_14_fl_aasen_next_column_update_rel_error
    (fp : FPModel) (a s h : ℝ) (hh : h ≠ 0) (hval : gammaValid fp 2) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 2 ∧
      fp.fl_div (fp.fl_sub a s) h = ((a - s) / h) * (1 + θ) := by
  obtain ⟨δs, hδs, hs⟩ := fp.model_sub a s
  obtain ⟨δd, hδd, hd⟩ := fp.model_div (fp.fl_sub a s) h hh
  obtain ⟨θ, hθ, hprod⟩ :=
    prod_error_bound fp 2 ![δs, δd]
      (by intro i; fin_cases i <;> simp_all) hval
  have hfactor : (1 + δs) * (1 + δd) = 1 + θ := by
    have h := hprod
    rw [Fin.prod_univ_two] at h
    simpa using h
  refine ⟨θ, hθ, ?_⟩
  rw [hd, hs, ← hfactor]
  field_simp [hh]

/-- **Equation (11.14) floating-point scalar update**, additive-error form.
The same two-operation Aasen update can be written as the exact scalar update
plus `Δ`, with `|Δ| ≤ γ₂ |(a-s)/h|`. -/
theorem higham11_14_fl_aasen_next_column_update_abs_error
    (fp : FPModel) (a s h : ℝ) (hh : h ≠ 0) (hval : gammaValid fp 2) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 2 * |(a - s) / h| ∧
      fp.fl_div (fp.fl_sub a s) h = (a - s) / h + Δ := by
  obtain ⟨θ, hθ, hrel⟩ :=
    higham11_14_fl_aasen_next_column_update_rel_error fp a s h hh hval
  refine ⟨((a - s) / h) * θ, ?_, ?_⟩
  · rw [abs_mul, mul_comm (gamma fp 2)]
    exact mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
  · rw [hrel]
    ring

/-- **Equation (11.14) floating-point next-column update**, finite-sum
specialization.  For the actual Aasen numerator
`A k i - ∑_{j≤i} L k j H j i`, the rounded scalar update has the additive
`γ₂` error supplied by `higham11_14_fl_aasen_next_column_update_abs_error`. -/
theorem higham11_14_fl_aasen_next_column_update_sum_abs_error (n : ℕ)
    (fp : FPModel) (A L H : Fin n → Fin n → ℝ)
    (i next k : Fin n)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hnext : next.val = i.val + 1) (hval : gammaValid fp 2) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 2 *
        |(A k i - ∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) /
          H next i| ∧
      fp.fl_div
          (fp.fl_sub (A k i)
            (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0))
          (H next i)
        =
          (A k i - ∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) /
              H next i
            + Δ :=
  higham11_14_fl_aasen_next_column_update_abs_error fp (A k i)
    (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) (H next i)
    (hHnz i next hnext) hval

/-- **Equation (11.14) floating-point next-column update**, exact-recurrence
bridge.  If the exact Aasen recurrence gives
`L k next = (A k i - ∑_{j≤i} L k j H j i) / H next i`, then the rounded scalar
update equals `L k next + Δ` with `|Δ| ≤ γ₂ |L k next|`. -/
theorem higham11_14_fl_aasen_next_column_update_abs_error_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (i next k : Fin n) (hnext : next.val = i.val + 1)
    (hk : i.val + 2 ≤ k.val) (hval : gammaValid fp 2) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 2 * |L k next| ∧
      fp.fl_div
          (fp.fl_sub (A k i)
            (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0))
          (H next i)
        = L k next + Δ := by
  obtain ⟨Δ, hΔ, hfl⟩ :=
    higham11_14_fl_aasen_next_column_update_sum_abs_error n fp A L H
      i next k hHnz hnext hval
  refine ⟨Δ, ?_, ?_⟩
  · rw [hrec i next k hnext hk]
    exact hΔ
  · rw [hfl, hrec i next k hnext hk]

/-- Source-shaped floating-point dot product for the prefix sum in Aasen's
next-column recurrence (11.14).  Entries beyond `j ≤ i` are masked to zero so
the computation can use the library's fixed-length `fl_dotProduct`. -/
noncomputable def higham11_14_fl_aasenPrefixDot (n : ℕ)
    (fp : FPModel) (L H : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  fl_dotProduct fp n (fun j => if j.val ≤ i.val then L k j else 0) (fun j => H j i)

/-- **Equation (11.14) prefix-sum formation error**.  The rounded masked dot
product for `∑_{j≤i} L k j H j i` equals the exact masked sum plus an additive
residual bounded by the standard dot-product `γ_n` radius. -/
theorem higham11_14_fl_aasen_prefix_dot_abs_error (n : ℕ)
    (fp : FPModel) (L H : Fin n → Fin n → ℝ) (i k : Fin n)
    (hval : gammaValid fp n) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp n *
        ∑ j : Fin n, |if j.val ≤ i.val then L k j else 0| * |H j i| ∧
      higham11_14_fl_aasenPrefixDot n fp L H i k =
        (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) + Δ := by
  let x : Fin n → ℝ := fun j => if j.val ≤ i.val then L k j else 0
  let y : Fin n → ℝ := fun j => H j i
  have hbound := dotProduct_error_bound fp n x y hval
  have hsum :
      (∑ j : Fin n, x j * y j) =
        ∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val ≤ i.val
    · simp only [x, y, hj, if_true]
    · simp only [x, y, hj, if_false, zero_mul]
  refine
    ⟨higham11_14_fl_aasenPrefixDot n fp L H i k -
        (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0), ?_, ?_⟩
  · simpa [higham11_14_fl_aasenPrefixDot, x, y, hsum] using hbound
  · ring

/-- Source-length floating-point dot product for the prefix sum in Aasen's
next-column recurrence (11.14).  Unlike `higham11_14_fl_aasenPrefixDot`, this
uses a vector of length `next.val`, so when `next = i+1` the error radius is the
source prefix length rather than the ambient dimension. -/
noncomputable def higham11_14_fl_aasenSourcePrefixDot (n : ℕ)
    (fp : FPModel) (L H : Fin n → Fin n → ℝ)
    (i next k : Fin n) : ℝ :=
  fl_dotProduct fp next.val
    (fun j : Fin next.val => L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩)
    (fun j : Fin next.val => H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i)

/-- **Equation (11.14) source-prefix formation error**.  The rounded dot
product over the source-length prefix `j = 0, ..., i` has a `γ_{i+1}`-style
additive residual and reindexes to the same masked `j≤i` Aasen sum. -/
theorem higham11_14_fl_aasen_source_prefix_dot_abs_error (n : ℕ)
    (fp : FPModel) (L H : Fin n → Fin n → ℝ) (i next k : Fin n)
    (hnext : next.val = i.val + 1) (hval : gammaValid fp next.val) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp next.val *
        ∑ j : Fin next.val,
          |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
            |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i| ∧
      higham11_14_fl_aasenSourcePrefixDot n fp L H i next k =
        (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) + Δ := by
  let x : Fin next.val → ℝ :=
    fun j => L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩
  let y : Fin next.val → ℝ :=
    fun j => H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i
  have hbound := dotProduct_error_bound fp next.val x y hval
  have hprefix :
      (∑ j : Fin next.val, x j * y j) =
        ∑ j : Fin next.val,
          L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ *
            H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i := by
    apply Finset.sum_congr rfl
    intro j _
    simp [x, y]
  have hle_lt :
      (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) =
        ∑ j : Fin n, if j.val < next.val then L k j * H j i else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hiff : j.val ≤ i.val ↔ j.val < next.val := by omega
    by_cases hj : j.val ≤ i.val
    · have hjlt : j.val < next.val := hiff.mp hj
      simp [hj, hjlt]
    · have hjnlt : ¬j.val < next.val := by
        intro hjlt
        exact hj (hiff.mpr hjlt)
      simp [hj, hjnlt]
  have hmasked :=
    finMaskedPrefixSum_eq_finSum next (fun j : Fin n => L k j * H j i)
  have hsum :
      (∑ j : Fin next.val, x j * y j) =
        ∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0 := by
    calc
      (∑ j : Fin next.val, x j * y j)
          = ∑ j : Fin next.val,
              L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ *
                H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i := hprefix
      _ = (∑ j : Fin n, if j.val < next.val then L k j * H j i else 0) :=
        hmasked.symm
      _ = (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0) :=
        hle_lt.symm
  refine
    ⟨higham11_14_fl_aasenSourcePrefixDot n fp L H i next k -
        (∑ j : Fin n, if j.val ≤ i.val then L k j * H j i else 0), ?_, ?_⟩
  · simpa [higham11_14_fl_aasenSourcePrefixDot, x, y, hsum] using hbound
  · ring

/-- **Equation (11.14) source-prefix formed update**, direct componentwise
absolute-error form.  This is the source-length analogue of
`higham11_14_fl_aasen_next_column_update_formed_sum_abs_sub_bound_of_exact_recurrence`,
using the `γ_{next.val}` prefix-dot budget when `next = i+1`. -/
theorem higham11_14_fl_aasen_next_column_update_source_prefix_abs_sub_bound_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (i next k : Fin n) (hnext : next.val = i.val + 1)
    (hk : i.val + 2 ≤ k.val) (hvalSum : gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2) :
    let Bsum : ℝ :=
      gamma fp next.val *
        ∑ j : Fin next.val,
          |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
            |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
    |fp.fl_div
        (fp.fl_sub (A k i) (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
        (H next i) - L k next| ≤
      Bsum / |H next i| +
        gamma fp 2 * (|L k next| + Bsum / |H next i|) := by
  let Bsum : ℝ :=
    gamma fp next.val *
      ∑ j : Fin next.val,
        |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
          |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
  obtain ⟨Δs, hΔs, hsumfl⟩ :=
    higham11_14_fl_aasen_source_prefix_dot_abs_error n fp L H i next k hnext hvalSum
  obtain ⟨Δu, hΔu, hfl⟩ :=
    higham11_14_fl_aasen_next_column_update_abs_error fp (A k i)
      (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k) (H next i)
      (hHnz i next hnext) hvalUpdate
  have harg :
      (A k i - higham11_14_fl_aasenSourcePrefixDot n fp L H i next k) /
          H next i =
        L k next - Δs / H next i := by
    rw [hsumfl, hrec i next k hnext hk]
    ring
  have hΔu' : |Δu| ≤ gamma fp 2 * |L k next - Δs / H next i| := by
    simpa [harg] using hΔu
  have hΔs_div : |Δs / H next i| ≤ Bsum / |H next i| := by
    simpa [Bsum, abs_div] using
      div_le_div_of_nonneg_right hΔs (abs_nonneg (H next i))
  have hinner :
      |L k next - Δs / H next i| ≤
        |L k next| + Bsum / |H next i| := by
    calc
      |L k next - Δs / H next i|
          ≤ |L k next| + |-(Δs / H next i)| := by
            simpa [sub_eq_add_neg] using abs_add_le (L k next) (-(Δs / H next i))
      _ = |L k next| + |Δs / H next i| := by rw [abs_neg]
      _ ≤ |L k next| + Bsum / |H next i| :=
        add_le_add (le_refl _) hΔs_div
  have hγ2 : 0 ≤ gamma fp 2 := gamma_nonneg fp hvalUpdate
  have hmain :
      |-Δs / H next i + Δu| ≤
        Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|) := by
    calc
      |-Δs / H next i + Δu|
          ≤ |-Δs / H next i| + |Δu| := abs_add_le _ _
      _ = |Δs / H next i| + |Δu| := by
        have hneg : -Δs / H next i = -(Δs / H next i) := by ring
        rw [hneg, abs_neg]
      _ ≤ Bsum / |H next i| + gamma fp 2 * |L k next - Δs / H next i| :=
        add_le_add hΔs_div hΔu'
      _ ≤ Bsum / |H next i| +
            gamma fp 2 * (|L k next| + Bsum / |H next i|) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hinner hγ2)
  rw [hfl, harg]
  have hdiff : L k next - Δs / H next i + Δu - L k next =
      -Δs / H next i + Δu := by
    ring
  rw [hdiff]
  exact hmain

/-- **Equation (11.14) source-prefix update**, column componentwise lift.  If a
chosen per-entry budget dominates the scalar source-prefix bound for each
updated row `k ≥ i+2`, then the rounded Aasen next-column update satisfies that
componentwise budget throughout the column. -/
theorem higham11_14_fl_aasen_next_column_update_source_prefix_column_component_bound_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (i next : Fin n) (hnext : next.val = i.val + 1)
    (hvalSum : gammaValid fp next.val) (hvalUpdate : gammaValid fp 2)
    (β : Fin n → ℝ)
    (hβ : ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|) ≤ β k) :
    ∀ k : Fin n, i.val + 2 ≤ k.val →
      |fp.fl_div
          (fp.fl_sub (A k i) (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i) - L k next| ≤ β k := by
  intro k hk
  exact
    (higham11_14_fl_aasen_next_column_update_source_prefix_abs_sub_bound_of_exact_recurrence
      n fp A L H hrec hHnz i next k hnext hk hvalSum hvalUpdate).trans
      (hβ k hk)

/-- **Equation (11.14) source-prefix update**, relative next-column package.
If the rounded updates define the computed `next` column below the first
subdiagonal and the remaining entries are unchanged, then the source-prefix
column budget supplies the relative factor hypothesis needed by the Aasen
factorization-product residual theorem. -/
theorem higham11_14_fl_aasen_next_column_source_prefix_Lhat_column_relative_bound_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H L_hat : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (i next : Fin n) (hnext : next.val = i.val + 1)
    (hvalSum : gammaValid fp next.val) (hvalUpdate : gammaValid fp 2)
    (γ_factor : ℝ) (hγ_factor : 0 ≤ γ_factor)
    (hLhat_update : ∀ k : Fin n, i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed : ∀ k : Fin n, ¬ i.val + 2 ≤ k.val →
      L_hat k next = L k next)
    (hbudget_rel : ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|) :
    ∀ k : Fin n, |L_hat k next - L k next| ≤ γ_factor * |L k next| := by
  intro k
  by_cases hk : i.val + 2 ≤ k.val
  · rw [hLhat_update k hk]
    exact
      higham11_14_fl_aasen_next_column_update_source_prefix_column_component_bound_of_exact_recurrence
        n fp A L H hrec hHnz i next hnext hvalSum hvalUpdate
        (fun k => γ_factor * |L k next|) hbudget_rel k hk
  · rw [hLhat_fixed k hk]
    simp [mul_nonneg hγ_factor (abs_nonneg (L k next))]

/-- **Equation (11.14) source-prefix update**, global relative-factor package.
If every successor column `next = i+1` is supplied by the rounded source-prefix
update and every non-successor column is unchanged, then the full computed
factor `L_hat` satisfies the relative entrywise hypothesis consumed by the
Aasen factorization-product residual theorem. -/
theorem higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H L_hat : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (γ_factor : ℝ) (hγ_factor : 0 ≤ γ_factor)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|) :
    ∀ k j : Fin n, |L_hat k j - L k j| ≤ γ_factor * |L k j| := by
  intro k j
  by_cases hsucc : ∃ i : Fin n, j.val = i.val + 1
  · rcases hsucc with ⟨i, hnext⟩
    exact
      higham11_14_fl_aasen_next_column_source_prefix_Lhat_column_relative_bound_of_exact_recurrence
        n fp A L H L_hat hrec hHnz i j hnext (hvalSum i j hnext) hvalUpdate
        γ_factor hγ_factor
        (fun k hk => hLhat_update i j k hnext hk)
        (fun k hk => hLhat_fixed_successor i j k hnext hk)
        (fun k hk => hbudget_rel i j hnext k hk)
        k
  · rw [hLhat_fixed_other k j (by
        intro i hi
        exact hsucc ⟨i, hi⟩)]
    simp [mul_nonneg hγ_factor (abs_nonneg (L k j))]

/-- **Equation (11.14) floating-point next-column update with a formed sum**.
Combines the rounded prefix dot-product formation error with the subsequent
rounded subtraction/division update.  Under the exact Aasen recurrence, the
computed update equals `L k next - Δs / H next i + Δu`, where `Δs` is the
prefix-dot formation residual and `Δu` is the two-operation update residual. -/
theorem higham11_14_fl_aasen_next_column_update_formed_sum_abs_error_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (i next k : Fin n) (hnext : next.val = i.val + 1)
    (hk : i.val + 2 ≤ k.val) (hvalSum : gammaValid fp n)
    (hvalUpdate : gammaValid fp 2) :
    ∃ Δs Δu : ℝ,
      |Δs| ≤ gamma fp n *
        ∑ j : Fin n, |if j.val ≤ i.val then L k j else 0| * |H j i| ∧
      |Δu| ≤ gamma fp 2 * |L k next - Δs / H next i| ∧
      fp.fl_div
          (fp.fl_sub (A k i) (higham11_14_fl_aasenPrefixDot n fp L H i k))
          (H next i)
        = L k next - Δs / H next i + Δu := by
  obtain ⟨Δs, hΔs, hsumfl⟩ :=
    higham11_14_fl_aasen_prefix_dot_abs_error n fp L H i k hvalSum
  obtain ⟨Δu, hΔu, hfl⟩ :=
    higham11_14_fl_aasen_next_column_update_abs_error fp (A k i)
      (higham11_14_fl_aasenPrefixDot n fp L H i k) (H next i)
      (hHnz i next hnext) hvalUpdate
  refine ⟨Δs, Δu, hΔs, ?_, ?_⟩
  · have harg :
        (A k i - higham11_14_fl_aasenPrefixDot n fp L H i k) / H next i =
          L k next - Δs / H next i := by
      rw [hsumfl, hrec i next k hnext hk]
      ring
    simpa [harg] using hΔu
  · have harg :
        (A k i - higham11_14_fl_aasenPrefixDot n fp L H i k) / H next i =
          L k next - Δs / H next i := by
      rw [hsumfl, hrec i next k hnext hk]
      ring
    rw [hfl, harg]

/-- **Equation (11.14) formed-sum update**, single-residual corollary.  This
packages the prefix-dot residual and the final subtraction/division residual
into the downstream shape `computed = L k next + Δ`, with an explicit scalar
budget. -/
theorem higham11_14_fl_aasen_next_column_update_formed_sum_single_abs_error_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (i next k : Fin n) (hnext : next.val = i.val + 1)
    (hk : i.val + 2 ≤ k.val) (hvalSum : gammaValid fp n)
    (hvalUpdate : gammaValid fp 2) :
    let Bsum : ℝ :=
      gamma fp n *
        ∑ j : Fin n, |if j.val ≤ i.val then L k j else 0| * |H j i|
    ∃ Δ : ℝ,
      |Δ| ≤ Bsum / |H next i| +
        gamma fp 2 * (|L k next| + Bsum / |H next i|) ∧
      fp.fl_div
          (fp.fl_sub (A k i) (higham11_14_fl_aasenPrefixDot n fp L H i k))
          (H next i)
        = L k next + Δ := by
  let Bsum : ℝ :=
    gamma fp n *
      ∑ j : Fin n, |if j.val ≤ i.val then L k j else 0| * |H j i|
  obtain ⟨Δs, Δu, hΔs, hΔu, hfl⟩ :=
    higham11_14_fl_aasen_next_column_update_formed_sum_abs_error_of_exact_recurrence
      n fp A L H hrec hHnz i next k hnext hk hvalSum hvalUpdate
  refine ⟨-Δs / H next i + Δu, ?_, ?_⟩
  · have hΔs_div : |Δs / H next i| ≤ Bsum / |H next i| := by
      simpa [Bsum, abs_div] using
        div_le_div_of_nonneg_right hΔs (abs_nonneg (H next i))
    have hinner :
        |L k next - Δs / H next i| ≤
          |L k next| + Bsum / |H next i| := by
      calc
        |L k next - Δs / H next i|
            ≤ |L k next| + |-(Δs / H next i)| := by
              simpa [sub_eq_add_neg] using abs_add_le (L k next) (-(Δs / H next i))
        _ = |L k next| + |Δs / H next i| := by rw [abs_neg]
        _ ≤ |L k next| + Bsum / |H next i| :=
          add_le_add (le_refl _) hΔs_div
    have hγ2 : 0 ≤ gamma fp 2 := gamma_nonneg fp hvalUpdate
    calc
      |-Δs / H next i + Δu|
          ≤ |-Δs / H next i| + |Δu| := abs_add_le _ _
      _ = |Δs / H next i| + |Δu| := by
        have hneg : -Δs / H next i = -(Δs / H next i) := by ring
        rw [hneg, abs_neg]
      _ ≤ Bsum / |H next i| + gamma fp 2 * |L k next - Δs / H next i| :=
        add_le_add hΔs_div hΔu
      _ ≤ Bsum / |H next i| +
            gamma fp 2 * (|L k next| + Bsum / |H next i|) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hinner hγ2)
  · rw [hfl]
    ring

/-- **Equation (11.14) formed-sum update**, componentwise absolute-error form.
This unwraps the single-residual corollary into the direct inequality needed
when assembling column or row perturbation budgets. -/
theorem higham11_14_fl_aasen_next_column_update_formed_sum_abs_sub_bound_of_exact_recurrence
    (n : ℕ) (fp : FPModel) (A L H : Fin n → Fin n → ℝ)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (i next k : Fin n) (hnext : next.val = i.val + 1)
    (hk : i.val + 2 ≤ k.val) (hvalSum : gammaValid fp n)
    (hvalUpdate : gammaValid fp 2) :
    let Bsum : ℝ :=
      gamma fp n *
        ∑ j : Fin n, |if j.val ≤ i.val then L k j else 0| * |H j i|
    |fp.fl_div
        (fp.fl_sub (A k i) (higham11_14_fl_aasenPrefixDot n fp L H i k))
        (H next i) - L k next| ≤
      Bsum / |H next i| +
        gamma fp 2 * (|L k next| + Bsum / |H next i|) := by
  obtain ⟨Δ, hΔ, hfl⟩ :=
    higham11_14_fl_aasen_next_column_update_formed_sum_single_abs_error_of_exact_recurrence
      n fp A L H hrec hHnz i next k hnext hk hvalSum hvalUpdate
  rw [hfl]
  simpa using hΔ

/-- **Equation (11.15)**, the Aasen solve chain
`L z = P b`, `T y = z`, `L^T w = y`, `x = P w`. -/
def higham11_15_aasenSolveChain (n : ℕ)
    (Pmat L T : Fin n → Fin n → ℝ)
    (b z y w x : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, ∑ j : Fin n, L i j * z j = ∑ j : Fin n, Pmat i j * b j) ∧
  (∀ i : Fin n, ∑ j : Fin n, T i j * y j = z i) ∧
  (∀ i : Fin n, ∑ j : Fin n, L j i * w j = y i) ∧
  (∀ i : Fin n, x i = ∑ j : Fin n, Pmat i j * w j)

/-- **Equation (11.15) outer triangular solves**, floating-point backward-error
wrapper.  The first and third solves in Aasen's solve chain are ordinary
forward/back substitution with `L` and `Lᵀ`; this packages the existing Chapter
8 substitution theorems in the notation of Chapter 11.  The middle tridiagonal
`T y = z` solve remains a separate obligation. -/
theorem higham11_15_fl_aasen_outer_triangular_solves_backward_error
    (fp : FPModel) (n : ℕ) (Pmat L : Fin n → Fin n → ℝ)
    (b y : Fin n → ℝ)
    (hLdiag : ∀ i : Fin n, L i i ≠ 0)
    (hLlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hval : gammaValid fp n) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let U : Fin n → Fin n → ℝ := fun i j => L j i
    ∃ ΔL ΔU : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      (∀ i j : Fin n, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (L i j + ΔL i j) * fl_forwardSub fp n L rhs j = rhs i) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U y j = y i) := by
  intro rhs U
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    forwardSub_backward_error fp n L rhs hLdiag hLlower hval
  have hUdiag : ∀ i : Fin n, U i i ≠ 0 := by
    intro i
    exact hLdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
    intro i j hji
    exact hLlower j i hji
  obtain ⟨ΔU, hΔU, hback⟩ :=
    backSub_backward_error fp n U y hUdiag hUupper hval
  exact ⟨ΔL, ΔU, hΔL, hΔU, hforward, hback⟩

/-- **Equation (11.15) middle tridiagonal solve**, floating-point backward-error
bridge.  Once the tridiagonal factorization of `T` is expressed by the Chapter
9 equation-(9.20) model, the actual rounded triangular solves used for
`T y = z` give a source perturbation `(T + ΔT) y_hat = z` with the
equation-(9.22) `f(γ_n)|L_hat||U_hat|` componentwise bound. -/
theorem higham11_15_fl_aasen_middle_tridiagonal_solve_backward_error
    (fp : FPModel) (n : ℕ)
    (T L_hat U_hat : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (DeltaT_LU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T L_hat U_hat
      DeltaT_LU (gamma fp n))
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hn : gammaValid fp n) :
    let q_hat := fl_forwardSub fp n L_hat z
    let y_hat := fl_backSub fp n U_hat q_hat
    ∃ DeltaL DeltaU DeltaT : Fin n → Fin n → ℝ,
      higham9_21_tridiag_solve_perturbation_model n L_hat U_hat
        q_hat y_hat z DeltaL DeltaU (gamma fp n) ∧
      (∀ i j : Fin n, |DeltaT i j| ≤
        higham9_14_f (gamma fp n) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (T i j + DeltaT i j) * y_hat j = z i) := by
  intro q_hat y_hat
  obtain ⟨DeltaL, DeltaU, h21⟩ :=
    higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma
      fp n L_hat U_hat z hL_diag hU_diag hLT hUT hn
  obtain ⟨DeltaT, hDeltaT_bound, hDeltaT_eq⟩ :=
    higham9_22_source_f_bound_of_9_20_9_21_models n T L_hat U_hat
      q_hat y_hat z (gamma fp n) (gamma_nonneg fp hn)
      DeltaT_LU DeltaL DeltaU h20 h21
  exact ⟨DeltaL, DeltaU, DeltaT, h21, hDeltaT_bound, hDeltaT_eq⟩

/-- **Equation (11.15) rounded solve-chain component package**.  This composes
the two Chapter-8 triangular-solve backward-error results for the outer Aasen
solves with the Chapter-9 tridiagonal middle-solve bridge.  The conclusion
exposes the three perturbed equations for the computed chain
`L z_hat = P b`, `T y_hat = z_hat`, `L^T w_hat = y_hat`, together with
`x_hat = P w_hat`. -/
theorem higham11_15_fl_aasen_solve_chain_backward_error_components
    (fp : FPModel) (n : ℕ)
    (Pmat L T L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hL_lower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let x_hat : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * w_hat j
    ∃ DeltaL_outer DeltaU_outer DeltaL_mid DeltaU_mid DeltaT :
        Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaL_outer i j| ≤ gamma fp n * |L i j|) ∧
      (∀ i j : Fin n, |DeltaU_outer i j| ≤ gamma fp n * |U_outer i j|) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (L i j + DeltaL_outer i j) * z_hat j = rhs i) ∧
      higham9_21_tridiag_solve_perturbation_model n L_T_hat U_T_hat
        q_hat y_hat z_hat DeltaL_mid DeltaU_mid (gamma fp n) ∧
      (∀ i j : Fin n, |DeltaT i j| ≤
        higham9_14_f (gamma fp n) *
          ∑ k : Fin n, |L_T_hat i k| * |U_T_hat k j|) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (T i j + DeltaT i j) * y_hat j = z_hat i) ∧
      (∀ i : Fin n,
        ∑ j : Fin n, (U_outer i j + DeltaU_outer i j) * w_hat j = y_hat i) ∧
      (∀ i : Fin n, x_hat i = ∑ j : Fin n, Pmat i j * w_hat j) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat x_hat
  obtain ⟨DeltaL_outer, DeltaU_outer,
      hDeltaL_outer, hDeltaU_outer, hForward_outer, hBack_outer⟩ :=
    higham11_15_fl_aasen_outer_triangular_solves_backward_error
      fp n Pmat L b y_hat hL_diag hL_lower hn
  obtain ⟨DeltaL_mid, DeltaU_mid, DeltaT,
      hMiddle_model, hDeltaT_bound, hMiddle_backward⟩ :=
    higham11_15_fl_aasen_middle_tridiagonal_solve_backward_error
      fp n T L_T_hat U_T_hat z_hat DeltaT_LU h20
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn
  refine ⟨DeltaL_outer, DeltaU_outer, DeltaL_mid, DeltaU_mid, DeltaT,
    hDeltaL_outer, hDeltaU_outer, hForward_outer, hMiddle_model,
    hDeltaT_bound, hMiddle_backward, hBack_outer, ?_⟩
  intro i
  rfl

/-- Perturbation matrix obtained by collapsing the rounded Aasen solve-chain
product `(L+ΔL)(T+ΔT)(U+ΔU)` against the exact product `LTU`. -/
noncomputable def higham11_15_aasenChainDeltaA (n : ℕ)
    (L T U DeltaL DeltaT DeltaU : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    (∑ p : Fin n, ∑ q : Fin n,
      (L i p + DeltaL i p) * (T p q + DeltaT p q) *
        (U q j + DeltaU q j)) -
    (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * U q j)

/-- Scalar seven-term product perturbation bound for one `(p,q)` term in the
collapsed Aasen solve-chain product. -/
theorem higham11_15_aasenTripleTerm_abs_bound
    (l t u dl dt du BL BT BU : ℝ)
    (hBL : 0 ≤ BL) (hBT : 0 ≤ BT)
    (hdl : |dl| ≤ BL) (hdt : |dt| ≤ BT) (hdu : |du| ≤ BU) :
    |(l + dl) * (t + dt) * (u + du) - l * t * u| ≤
      BL * |t| * |u| + |l| * BT * |u| + |l| * |t| * BU +
      BL * BT * |u| + BL * |t| * BU + |l| * BT * BU + BL * BT * BU := by
  have habs7 (a b c d e f g : ℝ) :
      |a + b + c + d + e + f + g| ≤
        |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    have h1 := abs_add_le (((((a + b) + c) + d) + e) + f) g
    have h2 := abs_add_le ((((a + b) + c) + d) + e) f
    have h3 := abs_add_le (((a + b) + c) + d) e
    have h4 := abs_add_le ((a + b) + c) d
    have h5 := abs_add_le (a + b) c
    have h6 := abs_add_le a b
    nlinarith
  have h1 : |dl * t * u| ≤ BL * |t| * |u| := by
    calc |dl * t * u|
        = |dl| * |t| * |u| := by rw [abs_mul, abs_mul]
      _ ≤ BL * |t| * |u| := by gcongr
  have h2 : |l * dt * u| ≤ |l| * BT * |u| := by
    calc |l * dt * u|
        = |l| * |dt| * |u| := by rw [abs_mul, abs_mul]
      _ ≤ |l| * BT * |u| := by gcongr
  have h3 : |l * t * du| ≤ |l| * |t| * BU := by
    calc |l * t * du|
        = |l| * |t| * |du| := by rw [abs_mul, abs_mul]
      _ ≤ |l| * |t| * BU := by gcongr
  have h4 : |dl * dt * u| ≤ BL * BT * |u| := by
    calc |dl * dt * u|
        = |dl| * |dt| * |u| := by rw [abs_mul, abs_mul]
      _ ≤ BL * BT * |u| := by gcongr
  have h5 : |dl * t * du| ≤ BL * |t| * BU := by
    calc |dl * t * du|
        = |dl| * |t| * |du| := by rw [abs_mul, abs_mul]
      _ ≤ BL * |t| * BU := by gcongr
  have h6 : |l * dt * du| ≤ |l| * BT * BU := by
    calc |l * dt * du|
        = |l| * |dt| * |du| := by rw [abs_mul, abs_mul]
      _ ≤ |l| * BT * BU := by gcongr
  have h7 : |dl * dt * du| ≤ BL * BT * BU := by
    calc |dl * dt * du|
        = |dl| * |dt| * |du| := by rw [abs_mul, abs_mul]
      _ ≤ BL * BT * BU := by gcongr
  have hsplit :
      (l + dl) * (t + dt) * (u + du) - l * t * u =
        dl * t * u + l * dt * u + l * t * du +
        dl * dt * u + dl * t * du + l * dt * du + dl * dt * du := by
    ring
  rw [hsplit]
  have habs := habs7 (dl * t * u) (l * dt * u) (l * t * du)
    (dl * dt * u) (dl * t * du) (l * dt * du) (dl * dt * du)
  nlinarith

/-- Collected scalar product perturbation bound with symmetric outer relative
coefficient `γ` and a supplied middle perturbation budget `BT`. -/
theorem higham11_15_aasenTripleTerm_abs_bound_gamma
    (l t u dl dt du γ BT : ℝ)
    (hγ : 0 ≤ γ) (hBT : 0 ≤ BT)
    (hdl : |dl| ≤ γ * |l|) (hdt : |dt| ≤ BT)
    (hdu : |du| ≤ γ * |u|) :
    |(l + dl) * (t + dt) * (u + du) - l * t * u| ≤
      (2 * γ + γ ^ 2) * |l| * |t| * |u| +
        (1 + 2 * γ + γ ^ 2) * |l| * BT * |u| := by
  have hbase :=
    higham11_15_aasenTripleTerm_abs_bound l t u dl dt du
      (γ * |l|) BT (γ * |u|)
      (mul_nonneg hγ (abs_nonneg _)) hBT
      hdl hdt hdu
  calc
    |(l + dl) * (t + dt) * (u + du) - l * t * u|
        ≤ (γ * |l|) * |t| * |u| + |l| * BT * |u| +
            |l| * |t| * (γ * |u|) + (γ * |l|) * BT * |u| +
            (γ * |l|) * |t| * (γ * |u|) + |l| * BT * (γ * |u|) +
            (γ * |l|) * BT * (γ * |u|) := hbase
    _ = (2 * γ + γ ^ 2) * |l| * |t| * |u| +
          (1 + 2 * γ + γ ^ 2) * |l| * BT * |u| := by ring

/-- Entrywise-to-matrix summation bridge for
`higham11_15_aasenChainDeltaA`: to bound one collapsed source perturbation
entry it suffices to bound each `(p,q)` triple-product perturbation term and
sum the resulting budgets. -/
theorem higham11_15_aasenChainDeltaA_abs_bound_of_entrywise
    (n : ℕ) (L T U DeltaL DeltaT DeltaU : Fin n → Fin n → ℝ)
    (i j : Fin n) (B : Fin n → Fin n → ℝ)
    (hentry : ∀ p q : Fin n,
      |(L i p + DeltaL i p) * (T p q + DeltaT p q) *
          (U q j + DeltaU q j) - L i p * T p q * U q j| ≤ B p q) :
    |higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j| ≤
      ∑ p : Fin n, ∑ q : Fin n, B p q := by
  have hsum :
      higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j =
        ∑ p : Fin n, ∑ q : Fin n,
          ((L i p + DeltaL i p) * (T p q + DeltaT p q) *
            (U q j + DeltaU q j) - L i p * T p q * U q j) := by
    unfold higham11_15_aasenChainDeltaA
    simp [Finset.sum_sub_distrib]
  rw [hsum]
  calc
    |∑ p : Fin n, ∑ q : Fin n,
        ((L i p + DeltaL i p) * (T p q + DeltaT p q) *
          (U q j + DeltaU q j) - L i p * T p q * U q j)|
        ≤ ∑ p : Fin n,
            |∑ q : Fin n,
              ((L i p + DeltaL i p) * (T p q + DeltaT p q) *
                (U q j + DeltaU q j) - L i p * T p q * U q j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Fin n, ∑ q : Fin n, B p q := by
          apply Finset.sum_le_sum
          intro p _
          calc
            |∑ q : Fin n,
              ((L i p + DeltaL i p) * (T p q + DeltaT p q) *
                (U q j + DeltaU q j) - L i p * T p q * U q j)|
                ≤ ∑ q : Fin n,
                    |(L i p + DeltaL i p) * (T p q + DeltaT p q) *
                      (U q j + DeltaU q j) - L i p * T p q * U q j| :=
                  Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ q : Fin n, B p q :=
                  Finset.sum_le_sum (fun q _ => hentry p q)

/-- Closed componentwise budget for the collapsed Aasen solve-chain
perturbation, expressed as the summed scalar triple-product budget. -/
noncomputable def higham11_15_aasenChainDeltaABound (n : ℕ)
    (γ : ℝ) (BT L T U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ∑ p : Fin n, ∑ q : Fin n,
      ((2 * γ + γ ^ 2) * |L i p| * |T p q| * |U q j| +
        (1 + 2 * γ + γ ^ 2) * |L i p| * BT p q * |U q j|)

/-- Componentwise bound for the collapsed Aasen solve-chain perturbation from
relative outer-solve perturbations and a supplied middle perturbation budget. -/
theorem higham11_15_aasenChainDeltaA_abs_bound_gamma
    (n : ℕ) (L T U DeltaL DeltaT DeltaU BT : Fin n → Fin n → ℝ)
    (γ : ℝ) (hγ : 0 ≤ γ) (hBT : ∀ p q : Fin n, 0 ≤ BT p q)
    (hDeltaL : ∀ i j : Fin n, |DeltaL i j| ≤ γ * |L i j|)
    (hDeltaT : ∀ i j : Fin n, |DeltaT i j| ≤ BT i j)
    (hDeltaU : ∀ i j : Fin n, |DeltaU i j| ≤ γ * |U i j|) :
    ∀ i j : Fin n,
      |higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j| ≤
        higham11_15_aasenChainDeltaABound n γ BT L T U i j := by
  intro i j
  unfold higham11_15_aasenChainDeltaABound
  apply higham11_15_aasenChainDeltaA_abs_bound_of_entrywise
  intro p q
  exact higham11_15_aasenTripleTerm_abs_bound_gamma
    (L i p) (T p q) (U q j) (DeltaL i p) (DeltaT p q) (DeltaU q j)
    γ (BT p q) hγ (hBT p q) (hDeltaL i p) (hDeltaT p q) (hDeltaU q j)

/-- Nonnegativity of the closed Aasen solve-chain budget. -/
theorem higham11_15_aasenChainDeltaABound_nonneg
    (n : ℕ) (γ : ℝ) (BT L T U : Fin n → Fin n → ℝ)
    (hγ : 0 ≤ γ) (hBT : ∀ p q : Fin n, 0 ≤ BT p q) :
    ∀ i j : Fin n, 0 ≤ higham11_15_aasenChainDeltaABound n γ BT L T U i j := by
  have hcT : 0 ≤ 2 * γ + γ ^ 2 := by
    nlinarith [mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hγ, sq_nonneg γ]
  have hcB : 0 ≤ 1 + 2 * γ + γ ^ 2 := by
    nlinarith [sq_nonneg (γ + 1)]
  intro i j
  unfold higham11_15_aasenChainDeltaABound
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro q _
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg hcT (abs_nonneg _)) (abs_nonneg _))
      (abs_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg hcB (abs_nonneg _)) (hBT p q))
      (abs_nonneg _)

/-- Infinity-norm aggregation for the closed Aasen solve-chain budget.
The componentwise scalar triple-product budget is bounded by two normwise
triple products: the exact `|L||T||U|` contribution and the middle-solve
budget contribution `|L| BT |U|`. -/
theorem higham11_15_aasenChainDeltaABound_infNorm_le
    (n : ℕ) (hn : 0 < n) (γ : ℝ) (BT L T U : Fin n → Fin n → ℝ)
    (hγ : 0 ≤ γ) (hBT : ∀ p q : Fin n, 0 ≤ BT p q) :
    infNorm (higham11_15_aasenChainDeltaABound n γ BT L T U) ≤
      (2 * γ + γ ^ 2) * (infNorm L * infNorm T * infNorm U) +
        (1 + 2 * γ + γ ^ 2) * (infNorm L * infNorm BT * infNorm U) := by
  let cT : ℝ := 2 * γ + γ ^ 2
  let cB : ℝ := 1 + 2 * γ + γ ^ 2
  let M_T : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L) (matMul n (absMatrix n T) (absMatrix n U))
  let M_B : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L) (matMul n BT (absMatrix n U))
  have hcT : 0 ≤ cT := by
    dsimp [cT]
    nlinarith [mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hγ, sq_nonneg γ]
  have hcB : 0 ≤ cB := by
    dsimp [cB]
    nlinarith [sq_nonneg (γ + 1)]
  have hM_T_nonneg : ∀ i j : Fin n, 0 ≤ M_T i j := by
    intro i j
    dsimp [M_T, matMul, absMatrix]
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg (abs_nonneg _)
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hM_B_nonneg : ∀ i j : Fin n, 0 ≤ M_B i j := by
    intro i j
    dsimp [M_B, matMul, absMatrix]
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg (abs_nonneg _)
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (hBT p q) (abs_nonneg _)
  have hbound_nonneg :
      ∀ i j : Fin n, 0 ≤ higham11_15_aasenChainDeltaABound n γ BT L T U i j :=
    higham11_15_aasenChainDeltaABound_nonneg n γ BT L T U hγ hBT
  have hM_T_norm : infNorm M_T ≤ infNorm L * infNorm T * infNorm U := by
    calc infNorm M_T
        = infNorm (matMul n (absMatrix n L) (matMul n (absMatrix n T) (absMatrix n U))) := rfl
      _ ≤ infNorm (absMatrix n L) * infNorm (matMul n (absMatrix n T) (absMatrix n U)) :=
          infNorm_matMul_le hn (absMatrix n L) (matMul n (absMatrix n T) (absMatrix n U))
      _ ≤ infNorm (absMatrix n L) * (infNorm (absMatrix n T) * infNorm (absMatrix n U)) :=
          mul_le_mul_of_nonneg_left
            (infNorm_matMul_le hn (absMatrix n T) (absMatrix n U))
            (infNorm_nonneg (absMatrix n L))
      _ = infNorm L * infNorm T * infNorm U := by
          rw [infNorm_absMatrix hn L, infNorm_absMatrix hn T, infNorm_absMatrix hn U]
          ring
  have hM_B_norm : infNorm M_B ≤ infNorm L * infNorm BT * infNorm U := by
    calc infNorm M_B
        = infNorm (matMul n (absMatrix n L) (matMul n BT (absMatrix n U))) := rfl
      _ ≤ infNorm (absMatrix n L) * infNorm (matMul n BT (absMatrix n U)) :=
          infNorm_matMul_le hn (absMatrix n L) (matMul n BT (absMatrix n U))
      _ ≤ infNorm (absMatrix n L) * (infNorm BT * infNorm (absMatrix n U)) :=
          mul_le_mul_of_nonneg_left
            (infNorm_matMul_le hn BT (absMatrix n U))
            (infNorm_nonneg (absMatrix n L))
      _ = infNorm L * infNorm BT * infNorm U := by
          rw [infNorm_absMatrix hn L, infNorm_absMatrix hn U]
          ring
  have hrow_MT : ∀ i : Fin n, ∑ j : Fin n, M_T i j ≤ infNorm M_T := by
    intro i
    calc ∑ j : Fin n, M_T i j
        = ∑ j : Fin n, |M_T i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hM_T_nonneg i j)]
      _ ≤ infNorm M_T := row_sum_le_infNorm M_T i
  have hrow_MB : ∀ i : Fin n, ∑ j : Fin n, M_B i j ≤ infNorm M_B := by
    intro i
    calc ∑ j : Fin n, M_B i j
        = ∑ j : Fin n, |M_B i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hM_B_nonneg i j)]
      _ ≤ infNorm M_B := row_sum_le_infNorm M_B i
  have hrows : ∀ i : Fin n,
      ∑ j : Fin n, |higham11_15_aasenChainDeltaABound n γ BT L T U i j| ≤
        cT * infNorm M_T + cB * infNorm M_B := by
    intro i
    calc ∑ j : Fin n, |higham11_15_aasenChainDeltaABound n γ BT L T U i j|
        = ∑ j : Fin n, higham11_15_aasenChainDeltaABound n γ BT L T U i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hbound_nonneg i j)]
      _ = cT * (∑ j : Fin n, M_T i j) + cB * (∑ j : Fin n, M_B i j) := by
            simp [higham11_15_aasenChainDeltaABound, M_T, M_B, cT, cB, matMul,
              absMatrix, Finset.sum_add_distrib, Finset.mul_sum, mul_add,
              mul_assoc, mul_left_comm, mul_comm]
      _ ≤ cT * infNorm M_T + cB * infNorm M_B :=
            add_le_add
              (mul_le_mul_of_nonneg_left (hrow_MT i) hcT)
              (mul_le_mul_of_nonneg_left (hrow_MB i) hcB)
  calc infNorm (higham11_15_aasenChainDeltaABound n γ BT L T U)
      ≤ cT * infNorm M_T + cB * infNorm M_B :=
        infNorm_le_of_row_sum_le
          (A := higham11_15_aasenChainDeltaABound n γ BT L T U) hrows
          (add_nonneg (mul_nonneg hcT (infNorm_nonneg M_T))
            (mul_nonneg hcB (infNorm_nonneg M_B)))
    _ ≤ cT * (infNorm L * infNorm T * infNorm U) +
        cB * (infNorm L * infNorm BT * infNorm U) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hM_T_norm hcT)
            (mul_le_mul_of_nonneg_left hM_B_norm hcB)
    _ = (2 * γ + γ ^ 2) * (infNorm L * infNorm T * infNorm U) +
        (1 + 2 * γ + γ ^ 2) * (infNorm L * infNorm BT * infNorm U) := by
          simp [cT, cB]

/-- Any perturbation bounded componentwise by the closed Aasen solve-chain
budget inherits the corresponding two-term normwise budget. -/
theorem higham11_15_infNorm_le_of_aasenChainDeltaABound
    (n : ℕ) (hn : 0 < n) (γ : ℝ) (BT L T U DeltaA : Fin n → Fin n → ℝ)
    (hγ : 0 ≤ γ) (hBT : ∀ p q : Fin n, 0 ≤ BT p q)
    (hDelta : ∀ i j : Fin n,
      |DeltaA i j| ≤ higham11_15_aasenChainDeltaABound n γ BT L T U i j) :
    infNorm DeltaA ≤
      (2 * γ + γ ^ 2) * (infNorm L * infNorm T * infNorm U) +
        (1 + 2 * γ + γ ^ 2) * (infNorm L * infNorm BT * infNorm U) := by
  let bound := higham11_15_aasenChainDeltaABound n γ BT L T U
  have hbound_nonneg : ∀ i j : Fin n, 0 ≤ bound i j := by
    intro i j
    exact higham11_15_aasenChainDeltaABound_nonneg n γ BT L T U hγ hBT i j
  calc infNorm DeltaA
      ≤ infNorm bound := by
          apply infNorm_le_of_row_sum_le
          · intro i
            calc ∑ j : Fin n, |DeltaA i j|
                ≤ ∑ j : Fin n, bound i j :=
                    Finset.sum_le_sum (fun j _ => hDelta i j)
              _ = ∑ j : Fin n, |bound i j| := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [abs_of_nonneg (hbound_nonneg i j)]
              _ ≤ infNorm bound := row_sum_le_infNorm bound i
          · exact infNorm_nonneg bound
    _ ≤ (2 * γ + γ ^ 2) * (infNorm L * infNorm T * infNorm U) +
        (1 + 2 * γ + γ ^ 2) * (infNorm L * infNorm BT * infNorm U) :=
          higham11_15_aasenChainDeltaABound_infNorm_le n hn γ BT L T U hγ hBT

/-- Infinity-norm aggregation for a perturbation controlled by the sum of two
closed Aasen chain budgets.  This is the normwise bridge needed after combining
the Aasen factorization residual with the rounded solve-chain residual. -/
theorem higham11_8_infNorm_le_of_sum_aasenChainDeltaABounds
    (n : ℕ) (hn : 0 < n)
    (γ1 γ2 : ℝ)
    (BT1 L1 T1 U1 BT2 L2 T2 U2 DeltaA : Fin n → Fin n → ℝ)
    (hγ1 : 0 ≤ γ1) (hBT1 : ∀ p q : Fin n, 0 ≤ BT1 p q)
    (hγ2 : 0 ≤ γ2) (hBT2 : ∀ p q : Fin n, 0 ≤ BT2 p q)
    (hDelta : ∀ i j : Fin n,
      |DeltaA i j| ≤
        higham11_15_aasenChainDeltaABound n γ1 BT1 L1 T1 U1 i j +
        higham11_15_aasenChainDeltaABound n γ2 BT2 L2 T2 U2 i j) :
    infNorm DeltaA ≤
      ((2 * γ1 + γ1 ^ 2) * (infNorm L1 * infNorm T1 * infNorm U1) +
        (1 + 2 * γ1 + γ1 ^ 2) * (infNorm L1 * infNorm BT1 * infNorm U1)) +
      ((2 * γ2 + γ2 ^ 2) * (infNorm L2 * infNorm T2 * infNorm U2) +
        (1 + 2 * γ2 + γ2 ^ 2) * (infNorm L2 * infNorm BT2 * infNorm U2)) := by
  let B1 := higham11_15_aasenChainDeltaABound n γ1 BT1 L1 T1 U1
  let B2 := higham11_15_aasenChainDeltaABound n γ2 BT2 L2 T2 U2
  have hB1_nonneg : ∀ i j : Fin n, 0 ≤ B1 i j := by
    intro i j
    exact higham11_15_aasenChainDeltaABound_nonneg n γ1 BT1 L1 T1 U1 hγ1 hBT1 i j
  have hB2_nonneg : ∀ i j : Fin n, 0 ≤ B2 i j := by
    intro i j
    exact higham11_15_aasenChainDeltaABound_nonneg n γ2 BT2 L2 T2 U2 hγ2 hBT2 i j
  have hrow1 : ∀ i : Fin n, ∑ j : Fin n, B1 i j ≤ infNorm B1 := by
    intro i
    calc ∑ j : Fin n, B1 i j
        = ∑ j : Fin n, |B1 i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hB1_nonneg i j)]
      _ ≤ infNorm B1 := row_sum_le_infNorm B1 i
  have hrow2 : ∀ i : Fin n, ∑ j : Fin n, B2 i j ≤ infNorm B2 := by
    intro i
    calc ∑ j : Fin n, B2 i j
        = ∑ j : Fin n, |B2 i j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hB2_nonneg i j)]
      _ ≤ infNorm B2 := row_sum_le_infNorm B2 i
  have hbase : infNorm DeltaA ≤ infNorm B1 + infNorm B2 := by
    apply infNorm_le_of_row_sum_le
    · intro i
      calc ∑ j : Fin n, |DeltaA i j|
          ≤ ∑ j : Fin n, (B1 i j + B2 i j) := by
              apply Finset.sum_le_sum
              intro j _
              simpa [B1, B2] using hDelta i j
        _ = (∑ j : Fin n, B1 i j) + ∑ j : Fin n, B2 i j := by
              rw [Finset.sum_add_distrib]
        _ ≤ infNorm B1 + infNorm B2 := add_le_add (hrow1 i) (hrow2 i)
    · exact add_nonneg (infNorm_nonneg B1) (infNorm_nonneg B2)
  have hnorm1 :
      infNorm B1 ≤
        (2 * γ1 + γ1 ^ 2) * (infNorm L1 * infNorm T1 * infNorm U1) +
          (1 + 2 * γ1 + γ1 ^ 2) * (infNorm L1 * infNorm BT1 * infNorm U1) := by
    simpa [B1] using
      higham11_15_aasenChainDeltaABound_infNorm_le
        n hn γ1 BT1 L1 T1 U1 hγ1 hBT1
  have hnorm2 :
      infNorm B2 ≤
        (2 * γ2 + γ2 ^ 2) * (infNorm L2 * infNorm T2 * infNorm U2) +
          (1 + 2 * γ2 + γ2 ^ 2) * (infNorm L2 * infNorm BT2 * infNorm U2) := by
    simpa [B2] using
      higham11_15_aasenChainDeltaABound_infNorm_le
        n hn γ2 BT2 L2 T2 U2 hγ2 hBT2
  exact hbase.trans (add_le_add hnorm1 hnorm2)

/-- Product budget for the rounded Aasen factorization residual
`L_hat * T_hat * L_hatᵀ - L * T * Lᵀ`, expressed from entrywise budgets for
the outer factor and the tridiagonal middle factor. -/
noncomputable def higham11_8_aasenFactorizationProductBudget (n : ℕ)
    (L T BL BT : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ∑ p : Fin n, ∑ q : Fin n,
      (BL i p * |T p q| * |L j q| +
        |L i p| * BT p q * |L j q| +
        |L i p| * |T p q| * BL j q +
        BL i p * BT p q * |L j q| +
        BL i p * |T p q| * BL j q +
        |L i p| * BT p q * BL j q +
        BL i p * BT p q * BL j q)

/-- Factorization-product perturbation bridge for Aasen's method.  If
`L_hat` and `T_hat` are entrywise close to the exact factors `L` and `T`, then
the residual in the product `L_hat * T_hat * L_hatᵀ` is controlled by the
explicit seven-term product budget. -/
theorem higham11_8_aasen_factorization_product_abs_bound_of_entrywise_factor_bounds
    (n : ℕ) (A L T L_hat T_hat BL BT : Fin n → Fin n → ℝ)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hBL : ∀ i j : Fin n, 0 ≤ BL i j)
    (hBT : ∀ i j : Fin n, 0 ≤ BT i j)
    (hLhat : ∀ i j : Fin n, |L_hat i j - L i j| ≤ BL i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT i j) :
    ∀ i j : Fin n,
      |(∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) -
          A i j| ≤
        higham11_8_aasenFactorizationProductBudget n L T BL BT i j := by
  intro i j
  let DeltaL : Fin n → Fin n → ℝ := fun r c => L_hat r c - L r c
  let DeltaT : Fin n → Fin n → ℝ := fun r c => T_hat r c - T r c
  let U : Fin n → Fin n → ℝ := fun r c => L c r
  let DeltaU : Fin n → Fin n → ℝ := fun r c => L_hat c r - L c r
  have hentry : ∀ p q : Fin n,
      |(L i p + DeltaL i p) * (T p q + DeltaT p q) *
          (U q j + DeltaU q j) - L i p * T p q * U q j| ≤
        BL i p * |T p q| * |U q j| + |L i p| * BT p q * |U q j| +
        |L i p| * |T p q| * BL j q + BL i p * BT p q * |U q j| +
        BL i p * |T p q| * BL j q + |L i p| * BT p q * BL j q +
        BL i p * BT p q * BL j q := by
    intro p q
    exact higham11_15_aasenTripleTerm_abs_bound
      (L i p) (T p q) (U q j) (DeltaL i p) (DeltaT p q) (DeltaU q j)
      (BL i p) (BT p q) (BL j q)
      (hBL i p) (hBT p q)
      (by simpa [DeltaL] using hLhat i p)
      (by simpa [DeltaT] using hThat p q)
      (by simpa [DeltaU] using hLhat j q)
  have hchain :
      |higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j| ≤
        higham11_8_aasenFactorizationProductBudget n L T BL BT i j := by
    unfold higham11_8_aasenFactorizationProductBudget
    simpa [U] using
      higham11_15_aasenChainDeltaA_abs_bound_of_entrywise
        n L T U DeltaL DeltaT DeltaU i j
        (fun p q =>
          BL i p * |T p q| * |U q j| + |L i p| * BT p q * |U q j| +
          |L i p| * |T p q| * BL j q + BL i p * BT p q * |U q j| +
          BL i p * |T p q| * BL j q + |L i p| * BT p q * BL j q +
          BL i p * BT p q * BL j q)
        hentry
  have htarget :
      (∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) -
          A i j =
        higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j := by
    unfold higham11_15_aasenChainDeltaA DeltaL DeltaT DeltaU U
    rw [← hprod i j]
    have hsum :
        (∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) =
          ∑ p : Fin n, ∑ q : Fin n,
            (L i p + (L_hat i p - L i p)) *
              (T p q + (T_hat p q - T p q)) *
              (L j q + (L_hat j q - L j q)) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hsum]
  simpa [htarget] using hchain

/-- Relative-factor specialization of the Aasen factorization product residual.
If `L_hat` is componentwise relatively close to `L` with coefficient `γ`, and
`T_hat` is bounded by the supplied middle budget `BT`, then the product
residual is controlled by the same closed chain budget used for the rounded
solve-chain collapse. -/
theorem higham11_8_aasen_factorization_product_abs_bound_gamma
    (n : ℕ) (A L T L_hat T_hat BT : Fin n → Fin n → ℝ)
    (γ : ℝ) (hγ : 0 ≤ γ) (hBT : ∀ p q : Fin n, 0 ≤ BT p q)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT i j) :
    ∀ i j : Fin n,
      |(∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) -
          A i j| ≤
        higham11_15_aasenChainDeltaABound n γ BT L T (fun r c => L c r) i j := by
  intro i j
  let DeltaL : Fin n → Fin n → ℝ := fun r c => L_hat r c - L r c
  let DeltaT : Fin n → Fin n → ℝ := fun r c => T_hat r c - T r c
  let U : Fin n → Fin n → ℝ := fun r c => L c r
  let DeltaU : Fin n → Fin n → ℝ := fun r c => L_hat c r - L c r
  have hDeltaL : ∀ r c : Fin n, |DeltaL r c| ≤ γ * |L r c| := by
    intro r c
    simpa [DeltaL] using hLhat r c
  have hDeltaT : ∀ r c : Fin n, |DeltaT r c| ≤ BT r c := by
    intro r c
    simpa [DeltaT] using hThat r c
  have hDeltaU : ∀ r c : Fin n, |DeltaU r c| ≤ γ * |U r c| := by
    intro r c
    simpa [DeltaU, U] using hLhat c r
  have hchain :
      |higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j| ≤
        higham11_15_aasenChainDeltaABound n γ BT L T U i j :=
    higham11_15_aasenChainDeltaA_abs_bound_gamma
      n L T U DeltaL DeltaT DeltaU BT γ hγ hBT
      hDeltaL hDeltaT hDeltaU i j
  have htarget :
      (∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) -
          A i j =
        higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j := by
    unfold higham11_15_aasenChainDeltaA DeltaL DeltaT DeltaU U
    rw [← hprod i j]
    have hsum :
        (∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) =
          ∑ p : Fin n, ∑ q : Fin n,
            (L i p + (L_hat i p - L i p)) *
              (T p q + (T_hat p q - T p q)) *
              (L j q + (L_hat j q - L j q)) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hsum]
  simpa [htarget, U] using hchain

/-- Aasen factorization-product residual from source-prefix rounded column
updates.  This combines the global relative `L_hat` bridge for the rounded
next-column recurrences with the factorization-product residual theorem, so
the factorization side no longer needs a separately supplied relative `L_hat`
hypothesis. -/
theorem higham11_8_aasen_factorization_product_abs_bound_of_source_prefix_updates
    (n : ℕ) (fp : FPModel)
    (A L H T L_hat T_hat BT : Fin n → Fin n → ℝ)
    (γ_factor : ℝ) (hγ_factor : 0 ≤ γ_factor)
    (hBT : ∀ p q : Fin n, 0 ≤ BT p q)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT i j) :
    ∀ i j : Fin n,
      |(∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) -
          A i j| ≤
        higham11_15_aasenChainDeltaABound n γ_factor BT L T
          (fun r c => L c r) i j := by
  have hLhat : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_aasen_factorization_product_abs_bound_gamma
      n A L T L_hat T_hat BT γ_factor hγ_factor hBT hprod hLhat hThat

/-- Combine a factorization residual and a solve-chain residual into a single
source backward-error perturbation.  If `A_fact` is close to the source matrix
`A`, and `(A_fact + DeltaS) w = rhs`, then `(A + DeltaA) w = rhs` for a
single perturbation bounded componentwise by the sum of the two budgets. -/
theorem higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
    (n : ℕ) (A A_fact DeltaS B_factor B_solve : Fin n → Fin n → ℝ)
    (rhs w : Fin n → ℝ)
    (hfactor : ∀ i j : Fin n, |A_fact i j - A i j| ≤ B_factor i j)
    (hsolve : ∀ i j : Fin n, |DeltaS i j| ≤ B_solve i j)
    (hsource : ∀ i : Fin n,
      ∑ j : Fin n, (A_fact i j + DeltaS i j) * w j = rhs i) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w j = rhs i) := by
  let DeltaA : Fin n → Fin n → ℝ := fun i j => (A_fact i j - A i j) + DeltaS i j
  refine ⟨DeltaA, ?_, ?_⟩
  · intro i j
    calc |DeltaA i j|
        = |(A_fact i j - A i j) + DeltaS i j| := rfl
      _ ≤ |A_fact i j - A i j| + |DeltaS i j| := abs_add_le _ _
      _ ≤ B_factor i j + B_solve i j := add_le_add (hfactor i j) (hsolve i j)
  · intro i
    calc ∑ j : Fin n, (A i j + DeltaA i j) * w j
        = ∑ j : Fin n, (A_fact i j + DeltaS i j) * w j := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            simp [DeltaA]
            ring
      _ = rhs i := hsource i

/-- Middle-solve componentwise budget used when collapsing the rounded Aasen
solve chain.  This is the `f(γ_n)|L_T||U_T|` budget supplied by the Chapter 9
tridiagonal solve aggregation. -/
noncomputable def higham11_15_aasenMiddleSolveBudget
    (fp : FPModel) (n : ℕ) (L_T_hat U_T_hat : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    higham9_14_f (gamma fp n) *
      ∑ k : Fin n, |L_T_hat i k| * |U_T_hat k j|

/-- Nonnegativity of the middle tridiagonal-solve budget used in the Aasen
solve chain. -/
theorem higham11_15_aasenMiddleSolveBudget_nonneg
    (fp : FPModel) (n : ℕ) (L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ i j : Fin n, 0 ≤ higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat i j := by
  intro i j
  exact mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn))
    (Finset.sum_nonneg
      (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- Infinity-norm aggregation for the middle tridiagonal solve budget.  The
entrywise `f(γ_n)|L_T||U_T|` budget is bounded by
`f(γ_n) ‖L_T‖∞ ‖U_T‖∞`. -/
theorem higham11_15_aasenMiddleSolveBudget_infNorm_le
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (L_T_hat U_T_hat : Fin n → Fin n → ℝ) (hn : gammaValid fp n) :
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
      higham9_14_f (gamma fp n) * (infNorm L_T_hat * infNorm U_T_hat) := by
  let fγ : ℝ := higham9_14_f (gamma fp n)
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)
  have hfγ : 0 ≤ fγ := by
    dsimp [fγ]
    exact higham9_14_f_nonneg (gamma_nonneg fp hn)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    dsimp [W, matMul, absMatrix]
    exact Finset.sum_nonneg
      (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hbudget_eq :
      higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat =
        fun i j => fγ * W i j := by
    ext i j
    simp [higham11_15_aasenMiddleSolveBudget, W, fγ, matMul, absMatrix]
  have hbudget_to_W :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        fγ * infNorm W := by
    rw [hbudget_eq]
    apply infNorm_le_of_row_sum_le
    · intro i
      calc ∑ j : Fin n, |fγ * W i j|
          = ∑ j : Fin n, fγ * W i j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_of_nonneg (mul_nonneg hfγ (hW_nonneg i j))]
        _ = fγ * ∑ j : Fin n, W i j := by
              rw [Finset.mul_sum]
        _ ≤ fγ * infNorm W := by
              apply mul_le_mul_of_nonneg_left _ hfγ
              calc ∑ j : Fin n, W i j
                  = ∑ j : Fin n, |W i j| := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [abs_of_nonneg (hW_nonneg i j)]
                _ ≤ infNorm W := row_sum_le_infNorm W i
    · exact mul_nonneg hfγ (infNorm_nonneg W)
  have hW_norm : infNorm W ≤ infNorm L_T_hat * infNorm U_T_hat := by
    calc infNorm W
        = infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) := rfl
      _ ≤ infNorm (absMatrix n L_T_hat) * infNorm (absMatrix n U_T_hat) :=
          infNorm_matMul_le hn_pos (absMatrix n L_T_hat) (absMatrix n U_T_hat)
      _ = infNorm L_T_hat * infNorm U_T_hat := by
          rw [infNorm_absMatrix hn_pos L_T_hat, infNorm_absMatrix hn_pos U_T_hat]
  exact hbudget_to_W.trans (mul_le_mul_of_nonneg_left hW_norm hfγ)

/-- Direct absolute-product aggregation for the middle tridiagonal solve
budget.  This is the form matching Chapter 9's tridiagonal growth theorem
`|L_T||U_T| ≤ 3|T_hat|`. -/
theorem higham11_15_aasenMiddleSolveBudget_infNorm_le_absLU
    (fp : FPModel) (n : ℕ)
    (L_T_hat U_T_hat : Fin n → Fin n → ℝ) (hn : gammaValid fp n) :
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
      higham9_14_f (gamma fp n) *
        infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) := by
  let fγ : ℝ := higham9_14_f (gamma fp n)
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)
  have hfγ : 0 ≤ fγ := by
    dsimp [fγ]
    exact higham9_14_f_nonneg (gamma_nonneg fp hn)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    dsimp [W, matMul, absMatrix]
    exact Finset.sum_nonneg
      (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hbudget_eq :
      higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat =
        fun i j => fγ * W i j := by
    ext i j
    simp [higham11_15_aasenMiddleSolveBudget, W, fγ, matMul, absMatrix]
  rw [hbudget_eq]
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |fγ * W i j|
        = ∑ j : Fin n, fγ * W i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (mul_nonneg hfγ (hW_nonneg i j))]
      _ = fγ * ∑ j : Fin n, W i j := by
            rw [Finset.mul_sum]
      _ ≤ fγ * infNorm W := by
            apply mul_le_mul_of_nonneg_left _ hfγ
            calc ∑ j : Fin n, W i j
                = ∑ j : Fin n, |W i j| := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [abs_of_nonneg (hW_nonneg i j)]
              _ ≤ infNorm W := row_sum_le_infNorm W i
  · exact mul_nonneg hfγ (infNorm_nonneg W)

/-- Relative form of `higham11_15_aasenMiddleSolveBudget_infNorm_le`.
If the tridiagonal LU factor product is bounded relative to `T_hat`, the
middle-solve budget is bounded relative to `T_hat` with the extra
`f(γ_n)` coefficient. -/
theorem higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (L_T_hat U_T_hat T_hat : Fin n → Fin n → ℝ) (κmid : ℝ)
    (hn : gammaValid fp n)
    (hprod :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmid * infNorm T_hat) :
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
      (higham9_14_f (gamma fp n) * κmid) * infNorm T_hat := by
  let fγ : ℝ := higham9_14_f (gamma fp n)
  have hfγ : 0 ≤ fγ := by
    dsimp [fγ]
    exact higham9_14_f_nonneg (gamma_nonneg fp hn)
  calc
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
        ≤ fγ * (infNorm L_T_hat * infNorm U_T_hat) := by
          simpa [fγ] using
            higham11_15_aasenMiddleSolveBudget_infNorm_le
              fp n hn_pos L_T_hat U_T_hat hn
    _ ≤ fγ * (κmid * infNorm T_hat) :=
          mul_le_mul_of_nonneg_left hprod hfγ
    _ = (higham9_14_f (gamma fp n) * κmid) * infNorm T_hat := by
          simp [fγ, mul_assoc]

/-- Relative form of `higham11_15_aasenMiddleSolveBudget_infNorm_le_absLU`.
If the absolute tridiagonal LU product matrix is bounded relative to `T_hat`,
the middle-solve budget is bounded relative to `T_hat` with the extra
`f(γ_n)` coefficient. -/
theorem higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_norm_bound
    (fp : FPModel) (n : ℕ)
    (L_T_hat U_T_hat T_hat : Fin n → Fin n → ℝ) (κmid : ℝ)
    (hn : gammaValid fp n)
    (habs :
      infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) ≤
        κmid * infNorm T_hat) :
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
      (higham9_14_f (gamma fp n) * κmid) * infNorm T_hat := by
  let fγ : ℝ := higham9_14_f (gamma fp n)
  have hfγ : 0 ≤ fγ := by
    dsimp [fγ]
    exact higham9_14_f_nonneg (gamma_nonneg fp hn)
  calc
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
        ≤ fγ * infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) := by
          simpa [fγ] using
            higham11_15_aasenMiddleSolveBudget_infNorm_le_absLU
              fp n L_T_hat U_T_hat hn
    _ ≤ fγ * (κmid * infNorm T_hat) :=
          mul_le_mul_of_nonneg_left habs hfγ
    _ = (higham9_14_f (gamma fp n) * κmid) * infNorm T_hat := by
          simp [fγ, mul_assoc]

/-- Convert a componentwise relative `|L_T||U_T|` bound into an infinity-norm
bound for the absolute LU product matrix. -/
theorem higham11_15_absLU_infNorm_le_of_componentwise_T_bound
    (n : ℕ) (L_T_hat U_T_hat T_hat : Fin n → Fin n → ℝ) (κmid : ℝ)
    (hκmid : 0 ≤ κmid)
    (hentry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmid * |T_hat i j|) :
    infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) ≤
      κmid * infNorm T_hat := by
  let W : Fin n → Fin n → ℝ := matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)
  have hW_nonneg : ∀ i j : Fin n, 0 ≤ W i j := by
    intro i j
    dsimp [W, matMul, absMatrix]
    exact Finset.sum_nonneg
      (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |W i j|
        = ∑ j : Fin n, W i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_of_nonneg (hW_nonneg i j)]
      _ ≤ ∑ j : Fin n, κmid * |T_hat i j| :=
            Finset.sum_le_sum (fun j _ => by simpa [W] using hentry i j)
      _ = κmid * ∑ j : Fin n, |T_hat i j| := by
            rw [Finset.mul_sum]
      _ ≤ κmid * infNorm T_hat :=
            mul_le_mul_of_nonneg_left (row_sum_le_infNorm T_hat i) hκmid
  · exact mul_nonneg hκmid (infNorm_nonneg T_hat)

/-- Middle-solve budget bound from a componentwise relative bound on the
absolute tridiagonal LU product matrix. -/
theorem higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound
    (fp : FPModel) (n : ℕ)
    (L_T_hat U_T_hat T_hat : Fin n → Fin n → ℝ) (κmid : ℝ)
    (hκmid : 0 ≤ κmid) (hn : gammaValid fp n)
    (hentry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmid * |T_hat i j|) :
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
      (higham9_14_f (gamma fp n) * κmid) * infNorm T_hat :=
  higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_norm_bound
    fp n L_T_hat U_T_hat T_hat κmid hn
    (higham11_15_absLU_infNorm_le_of_componentwise_T_bound
      n L_T_hat U_T_hat T_hat κmid hκmid hentry)

/-- Concrete middle-solve budget bound from Chapter 9's column-dominant
tridiagonal growth theorem `|L_T||U_T| ≤ 3|T_hat|`. -/
theorem higham11_15_aasenMiddleSolveBudget_infNorm_le_of_colDiagDom_LUFactSpec
    (fp : FPModel) (n : ℕ)
    (T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat) :
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
      (higham9_14_f (gamma fp n) * 3) * infNorm T_hat := by
  apply higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound
    fp n L_T_hat U_T_hat T_hat 3 (by norm_num) hn
  intro i j
  simpa [matMul, absMatrix] using
    higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      T_hat L_T_hat U_T_hat hLU hdetT hT_tridiag hColDom i j

/-- Concrete middle-solve budget bound from Chapter 9's row-dominant
tridiagonal growth theorem `|L_T||U_T| ≤ 3|T_hat|`. -/
theorem higham11_15_aasenMiddleSolveBudget_infNorm_le_of_rowDiagDom_LUFactSpec
    (fp : FPModel) (n : ℕ)
    (T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat) :
    infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
      (higham9_14_f (gamma fp n) * 3) * infNorm T_hat := by
  apply higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound
    fp n L_T_hat U_T_hat T_hat 3 (by norm_num) hn
  intro i j
  simpa [matMul, absMatrix] using
    higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec
      T_hat L_T_hat U_T_hat hLU hdetT hT_tridiag hRowDom i j

/-- **Equation (11.15) source backward-error algebra**.  If the three rounded
solve-chain components satisfy perturbed equations and the unperturbed product
is `A = L T U`, then the collapsed product perturbation gives a single source
equation `(A+ΔA)w = rhs`.  The componentwise bound is kept explicit so later
work can plug in the detailed Aasen scalar budget. -/
theorem higham11_15_aasen_chain_source_backward_error_of_components
    (n : ℕ) (A L T U DeltaL DeltaT DeltaU : Fin n → Fin n → ℝ)
    (rhs z y w : Fin n → ℝ) (bound : Fin n → Fin n → ℝ)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * U q j) = A i j)
    (hLz : ∀ i : Fin n,
      ∑ j : Fin n, (L i j + DeltaL i j) * z j = rhs i)
    (hTy : ∀ i : Fin n,
      ∑ j : Fin n, (T i j + DeltaT i j) * y j = z i)
    (hUw : ∀ i : Fin n,
      ∑ j : Fin n, (U i j + DeltaU i j) * w j = y i)
    (hbound : ∀ i j : Fin n,
      |higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU i j| ≤
        bound i j) :
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ bound i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w j = rhs i) := by
  let DeltaA := higham11_15_aasenChainDeltaA n L T U DeltaL DeltaT DeltaU
  refine ⟨DeltaA, hbound, ?_⟩
  intro i
  calc
    ∑ j : Fin n, (A i j + DeltaA i j) * w j
        = ∑ j : Fin n,
            (∑ p : Fin n, ∑ q : Fin n,
              (L i p + DeltaL i p) * (T p q + DeltaT p q) *
                (U q j + DeltaU q j)) * w j := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          unfold DeltaA higham11_15_aasenChainDeltaA
          rw [← hprod i j]
          ring
    _ = ∑ p : Fin n,
          (L i p + DeltaL i p) *
            (∑ q : Fin n, (T p q + DeltaT p q) *
              (∑ j : Fin n, (U q j + DeltaU q j) * w j)) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q _
          ring_nf
    _ = ∑ p : Fin n,
          (L i p + DeltaL i p) *
            (∑ q : Fin n, (T p q + DeltaT p q) * y q) := by
          apply Finset.sum_congr rfl
          intro p _
          congr 1
          apply Finset.sum_congr rfl
          intro q _
          rw [hUw q]
    _ = ∑ p : Fin n, (L i p + DeltaL i p) * z p := by
          apply Finset.sum_congr rfl
          intro p _
          rw [hTy p]
    _ = rhs i := hLz i

/-- **Equation (11.15) rounded source backward-error wrapper**.  This
instantiates the rounded solve-chain component package and the algebraic
collapse theorem.  The only remaining hypothesis is the componentwise budget
for the collapsed chain perturbation `higham11_15_aasenChainDeltaA`; proving
that budget is the next scalar-error aggregation step toward Theorem 11.8. -/
theorem higham11_15_fl_aasen_solve_chain_source_backward_error_of_delta_bound
    (fp : FPModel) (n : ℕ)
    (A Pmat L T L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU bound : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hL_lower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hbound : ∀ DeltaL_outer DeltaU_outer DeltaT : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaL_outer i j| ≤ gamma fp n * |L i j|) →
      (∀ i j : Fin n, |DeltaU_outer i j| ≤ gamma fp n * |L j i|) →
      (∀ i j : Fin n, |DeltaT i j| ≤
        higham9_14_f (gamma fp n) *
          ∑ k : Fin n, |L_T_hat i k| * |U_T_hat k j|) →
      ∀ i j : Fin n,
        |higham11_15_aasenChainDeltaA n L T (fun r c => L c r)
            DeltaL_outer DeltaT DeltaU_outer i j| ≤ bound i j) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L j i
    let w_hat := fl_backSub fp n U_outer y_hat
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ bound i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat
  obtain ⟨DeltaL_outer, DeltaU_outer, _DeltaL_mid, _DeltaU_mid, DeltaT,
      hDeltaL_outer, hDeltaU_outer, hForward_outer, _hMiddle_model,
      hDeltaT_bound, hMiddle_backward, hBack_outer, _hx⟩ :=
    higham11_15_fl_aasen_solve_chain_backward_error_components
      fp n Pmat L T L_T_hat U_T_hat b DeltaT_LU h20
      hL_diag hL_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn
  exact higham11_15_aasen_chain_source_backward_error_of_components
    n A L T U_outer DeltaL_outer DeltaT DeltaU_outer
    rhs z_hat y_hat w_hat bound
    (by
      intro i j
      simpa [U_outer] using hprod i j)
    hForward_outer hMiddle_backward hBack_outer
    (hbound DeltaL_outer DeltaU_outer DeltaT
      hDeltaL_outer (by simpa [U_outer] using hDeltaU_outer) hDeltaT_bound)

/-- **Equation (11.15) rounded source backward-error theorem**, solve-chain
part.  This instantiates the rounded component package, algebraic collapse,
and closed componentwise `higham11_15_aasenChainDeltaABound` budget.  It is the
solve-chain side of the Aasen Theorem 11.8 backward-error proof; the remaining
global work is to combine this with the factorization/recurrence perturbation
budget and simplify the bound to the printed normwise form. -/
theorem higham11_15_fl_aasen_solve_chain_source_backward_error
    (fp : FPModel) (n : ℕ)
    (A Pmat L T L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hL_lower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let bound := higham11_15_aasenChainDeltaABound n (gamma fp n) BT L T U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ bound i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat BT bound
  apply higham11_15_fl_aasen_solve_chain_source_backward_error_of_delta_bound
    fp n A Pmat L T L_T_hat U_T_hat b DeltaT_LU bound h20
    hL_diag hL_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod
  intro DeltaL_outer DeltaU_outer DeltaT hDeltaL_outer hDeltaU_outer hDeltaT
  have hBT_nonneg :
      ∀ p q : Fin n, 0 ≤ higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat p q := by
    intro p q
    exact mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn))
      (Finset.sum_nonneg
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hDeltaT' :
      ∀ i j : Fin n, |DeltaT i j| ≤
        higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat i j := by
    intro i j
    simpa [higham11_15_aasenMiddleSolveBudget] using hDeltaT i j
  have hDeltaU' :
      ∀ i j : Fin n, |DeltaU_outer i j| ≤ gamma fp n * |U_outer i j| := by
    intro i j
    simpa [U_outer] using hDeltaU_outer i j
  intro i j
  simpa [bound, BT, U_outer] using
    higham11_15_aasenChainDeltaA_abs_bound_gamma n L T U_outer
      DeltaL_outer DeltaT DeltaU_outer
      (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
      (gamma fp n) (gamma_nonneg fp hn) hBT_nonneg
      hDeltaL_outer hDeltaT' hDeltaU' i j

/-- Rounded Aasen source backward-error wrapper that combines factorization
and solve-chain residuals.  The first budget controls the residual
`L_hat*T_hat*L_hatᵀ - A` from relative factor perturbations; the second is the
closed solve-chain budget for solving with the computed factors. -/
theorem higham11_8_fl_aasen_factor_solve_source_backward_error
    (fp : FPModel) (n : ℕ)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor : ℝ) (hγ_factor : 0 ≤ γ_factor)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat BT_solve B_factor B_solve
  let A_fact : Fin n → Fin n → ℝ :=
    fun i j => ∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q
  have hprod_fact : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) =
        A_fact i j := by
    intro i j
    rfl
  obtain ⟨DeltaS, hDeltaS, hsource⟩ :=
    higham11_15_fl_aasen_solve_chain_source_backward_error
      fp n A_fact Pmat L_hat T_hat L_T_hat U_T_hat b DeltaT_LU h20
      hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn
      hprod_fact
  apply higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
    n A A_fact DeltaS B_factor B_solve rhs w_hat
  · intro i j
    simpa [A_fact, B_factor] using
      higham11_8_aasen_factorization_product_abs_bound_gamma
        n A L T L_hat T_hat BT_factor γ_factor hγ_factor hBT_factor
        hprod hLhat hThat i j
  · exact hDeltaS
  · exact hsource

/-- Rounded Aasen source backward-error wrapper from source-prefix recurrence
updates.  This removes the standalone relative `L_hat` hypothesis from
`higham11_8_fl_aasen_factor_solve_source_backward_error`: the factorization
residual is supplied directly by the rounded source-prefix next-column update
bridge, while the concrete middle-factor budget for `T_hat` remains explicit. -/
theorem higham11_8_fl_aasen_factor_solve_source_backward_error_of_source_prefix_updates
    (fp : FPModel) (n : ℕ)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor : ℝ) (hγ_factor : 0 ≤ γ_factor)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat BT_solve B_factor B_solve
  let A_fact : Fin n → Fin n → ℝ :=
    fun i j => ∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q
  have hprod_fact : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L_hat i p * T_hat p q * L_hat j q) =
        A_fact i j := by
    intro i j
    rfl
  obtain ⟨DeltaS, hDeltaS, hsource⟩ :=
    higham11_15_fl_aasen_solve_chain_source_backward_error
      fp n A_fact Pmat L_hat T_hat L_T_hat U_T_hat b DeltaT_LU h20
      hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn
      hprod_fact
  apply higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals
    n A A_fact DeltaS B_factor B_solve rhs w_hat
  · intro i j
    simpa [A_fact, B_factor] using
      higham11_8_aasen_factorization_product_abs_bound_of_source_prefix_updates
        n fp A L H T L_hat T_hat BT_factor γ_factor hγ_factor hBT_factor
        hrec hHnz hvalSum hvalUpdate hLhat_update hLhat_fixed_successor
        hLhat_fixed_other hbudget_rel hprod hThat i j
  · exact hDeltaS
  · exact hsource

/-- **Equation (11.15) exact solve-chain bridge**, unpermuted case.  If the
exact Aasen product is `A = L T Lᵀ` and the three exact solves in the chain are
satisfied with identity permutation, then the resulting `x` solves `A x = b`.
This is the algebraic base that the later rounded solve-chain perturbation must
approximate. -/
theorem higham11_15_aasenSolveChain_identity_solve_of_product (n : ℕ)
    (A L T : Fin n → Fin n → ℝ) (b z y w x : Fin n → ℝ)
    (hprod : ∀ i j : Fin n,
      (∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * T k₁ k₂ * L j k₂) = A i j)
    (hchain : higham11_15_aasenSolveChain n (fun i j => if i = j then 1 else 0)
      L T b z y w x) :
    ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i := by
  rcases hchain with ⟨hLz, hTy, hLtw, hx⟩
  have hLz' : ∀ i : Fin n, ∑ j : Fin n, L i j * z j = b i := by
    intro i
    simpa using hLz i
  have hx' : ∀ i : Fin n, x i = w i := by
    intro i
    simpa using hx i
  intro i
  calc
    ∑ j : Fin n, A i j * x j
        = ∑ j : Fin n,
            (∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * T k₁ k₂ * L j k₂) * w j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← hprod i j, hx' j]
    _ = ∑ k₁ : Fin n,
          L i k₁ * (∑ k₂ : Fin n, T k₁ k₂ * (∑ j : Fin n, L j k₂ * w j)) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k₁ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k₂ _
          ring_nf
    _ = ∑ k₁ : Fin n, L i k₁ * (∑ k₂ : Fin n, T k₁ k₂ * y k₂) := by
          apply Finset.sum_congr rfl
          intro k₁ _
          congr 1
          apply Finset.sum_congr rfl
          intro k₂ _
          rw [hLtw k₂]
    _ = ∑ k₁ : Fin n, L i k₁ * z k₁ := by
          apply Finset.sum_congr rfl
          intro k₁ _
          rw [hTy k₁]
    _ = b i := hLz' i

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

/-- Uniform componentwise perturbation bounds imply an infinity-norm bound.
This is the row-sum bridge used when converting componentwise backward-error
estimates into the normwise shape of Theorem 11.8. -/
theorem higham11_8_infNorm_le_card_mul_of_uniform_componentwise_bound (n : ℕ)
    (ΔA : Fin n → Fin n → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hΔ : ∀ i j : Fin n, |ΔA i j| ≤ β) :
    infNorm ΔA ≤ (n : ℝ) * β := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc (∑ j : Fin n, |ΔA i j|)
        ≤ ∑ _j : Fin n, β := Finset.sum_le_sum (fun j _ => hΔ i j)
      _ = (n : ℝ) * β := by
        simp [Finset.sum_const, nsmul_eq_mul]
  · exact mul_nonneg (Nat.cast_nonneg n) hβ

/-- Direct bridge into the printed Theorem 11.8 normwise predicate from a
uniform componentwise perturbation bound and a scalar row-sum budget. -/
theorem higham11_8_aasenNormwiseBackwardBound_of_uniform_componentwise_bound
    (n : ℕ) (ΔA : Fin n → Fin n → ℝ) (β γ15n25 T_inf : ℝ)
    (hβ : 0 ≤ β) (hΔ : ∀ i j : Fin n, |ΔA i j| ≤ β)
    (hbudget : (n : ℝ) * β ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * T_inf) :
    higham11_8_aasenNormwiseBackwardBound n (infNorm ΔA) γ15n25 T_inf :=
  (higham11_8_infNorm_le_card_mul_of_uniform_componentwise_bound n ΔA β hβ hΔ).trans
    hbudget

/-- Relative componentwise perturbation bounds against the computed Aasen
tridiagonal factor imply the corresponding infinity-norm relative bound. -/
theorem higham11_8_infNorm_le_mul_of_componentwise_T_bound (n : ℕ)
    (ΔA T_hat : Fin n → Fin n → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hΔ : ∀ i j : Fin n, |ΔA i j| ≤ η * |T_hat i j|) :
    infNorm ΔA ≤ η * infNorm T_hat :=
  by
    apply infNorm_le_of_row_sum_le
    · intro i
      calc ∑ j : Fin n, |ΔA i j|
          ≤ ∑ j : Fin n, η * |T_hat i j| :=
            Finset.sum_le_sum (fun j _ => hΔ i j)
        _ = η * ∑ j : Fin n, |T_hat i j| := (Finset.mul_sum ..).symm
        _ ≤ η * infNorm T_hat :=
            mul_le_mul_of_nonneg_left (row_sum_le_infNorm T_hat i) hη
    · exact mul_nonneg hη (infNorm_nonneg T_hat)

/-- A relative entrywise factor perturbation controls the perturbed factor's
infinity norm by `(1+γ)` times the source factor norm. -/
theorem higham11_8_infNorm_factor_le_of_relative_entry_bound (n : ℕ)
    (L L_hat : Fin n → Fin n → ℝ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hentry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ * |L i j|) :
    infNorm L_hat ≤ (1 + γ) * infNorm L := by
  have hγ1 : 0 ≤ 1 + γ := by linarith
  apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n L_hat L (1 + γ) hγ1
  intro i j
  calc
    |L_hat i j| = |(L_hat i j - L i j) + L i j| := by ring_nf
    _ ≤ |L_hat i j - L i j| + |L i j| := abs_add_le _ _
    _ ≤ γ * |L i j| + |L i j| := add_le_add (hentry i j) le_rfl
    _ = (1 + γ) * |L i j| := by ring

/-- Transposed form of
`higham11_8_infNorm_factor_le_of_relative_entry_bound`. -/
theorem higham11_8_infNorm_factorTranspose_le_of_relative_entry_bound (n : ℕ)
    (L L_hat : Fin n → Fin n → ℝ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hentry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ * |L i j|) :
    infNorm (fun r c => L_hat c r) ≤
      (1 + γ) * infNorm (fun r c => L c r) :=
  higham11_8_infNorm_factor_le_of_relative_entry_bound n
    (fun r c => L c r) (fun r c => L_hat c r) γ hγ
    (fun i j => by simpa using hentry j i)

/-- Direct bridge from a relative componentwise `T_hat` perturbation budget to
the printed Theorem 11.8 normwise predicate. -/
theorem higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound
    (n : ℕ) (ΔA T_hat : Fin n → Fin n → ℝ) (η γ15n25 : ℝ)
    (hη : 0 ≤ η)
    (hΔ : ∀ i j : Fin n, |ΔA i j| ≤ η * |T_hat i j|)
    (hbudget : η * infNorm T_hat ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat) :
    higham11_8_aasenNormwiseBackwardBound n (infNorm ΔA) γ15n25
      (infNorm T_hat) :=
  (higham11_8_infNorm_le_mul_of_componentwise_T_bound n ΔA T_hat η hη hΔ).trans
    hbudget

/-- Split an entrywise Theorem 11.8 `T_hat` comparison into independent
factorization and solve-chain pieces. -/
theorem higham11_8_componentwise_T_bound_add_of_parts (n : ℕ)
    (B_factor B_solve T_hat : Fin n → Fin n → ℝ)
    (η_factor η_solve η : ℝ)
    (hfactor : ∀ i j : Fin n, B_factor i j ≤ η_factor * |T_hat i j|)
    (hsolve : ∀ i j : Fin n, B_solve i j ≤ η_solve * |T_hat i j|)
    (hη_parts : η_factor + η_solve ≤ η) :
    ∀ i j : Fin n, B_factor i j + B_solve i j ≤ η * |T_hat i j| := by
  intro i j
  calc B_factor i j + B_solve i j
      ≤ η_factor * |T_hat i j| + η_solve * |T_hat i j| :=
          add_le_add (hfactor i j) (hsolve i j)
    _ = (η_factor + η_solve) * |T_hat i j| := by ring
    _ ≤ η * |T_hat i j| :=
          mul_le_mul_of_nonneg_right hη_parts (abs_nonneg _)

/-- Normwise bridge for the closed Aasen solve-chain budget.  Once the closed
componentwise chain budget is majorized by `η |T_hat|`, the existing Theorem
11.8 normwise predicate follows from the relative `T_hat` bridge. -/
theorem higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound
    (n : ℕ) (DeltaA L T U BT T_hat : Fin n → Fin n → ℝ)
    (γ η γ15n25 : ℝ) (hη : 0 ≤ η)
    (hDelta : ∀ i j : Fin n,
      |DeltaA i j| ≤ higham11_15_aasenChainDeltaABound n γ BT L T U i j)
    (hchain_le : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n γ BT L T U i j ≤ η * |T_hat i j|)
    (hbudget : η * infNorm T_hat ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat) :
    higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
      (infNorm T_hat) :=
  higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound
    n DeltaA T_hat η γ15n25 hη
    (fun i j => (hDelta i j).trans (hchain_le i j)) hbudget

/-- Scalar-coefficient version of
`higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound`.  It is often
more convenient to supply `η ≤ (n-1)^2 γ_{15n+25}` and let this theorem multiply
both sides by `‖T_hat‖∞`. -/
theorem higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound_coeff_le
    (n : ℕ) (DeltaA L T U BT T_hat : Fin n → Fin n → ℝ)
    (γ η γ15n25 : ℝ) (hη : 0 ≤ η)
    (hDelta : ∀ i j : Fin n,
      |DeltaA i j| ≤ higham11_15_aasenChainDeltaABound n γ BT L T U i j)
    (hchain_le : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n γ BT L T U i j ≤ η * |T_hat i j|)
    (hη_le : η ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
      (infNorm T_hat) := by
  apply higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound
    n DeltaA L T U BT T_hat γ η γ15n25 hη hDelta hchain_le
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_right hη_le (infNorm_nonneg T_hat)

/-- Direct bridge from the summed factorization and solve-chain closed Aasen
budgets to the printed Theorem 11.8 normwise predicate.  This is the scalar
norm-budget sibling of the entrywise `η |T_hat|` bridge. -/
theorem higham11_8_aasenNormwiseBackwardBound_of_sum_aasenChainDeltaABounds
    (n : ℕ) (hn : 0 < n)
    (γ1 γ2 γ15n25 : ℝ)
    (BT1 L1 T1 U1 BT2 L2 T2 U2 DeltaA T_hat : Fin n → Fin n → ℝ)
    (hγ1 : 0 ≤ γ1) (hBT1 : ∀ p q : Fin n, 0 ≤ BT1 p q)
    (hγ2 : 0 ≤ γ2) (hBT2 : ∀ p q : Fin n, 0 ≤ BT2 p q)
    (hDelta : ∀ i j : Fin n,
      |DeltaA i j| ≤
        higham11_15_aasenChainDeltaABound n γ1 BT1 L1 T1 U1 i j +
        higham11_15_aasenChainDeltaABound n γ2 BT2 L2 T2 U2 i j)
    (hbudget :
      ((2 * γ1 + γ1 ^ 2) * (infNorm L1 * infNorm T1 * infNorm U1) +
          (1 + 2 * γ1 + γ1 ^ 2) * (infNorm L1 * infNorm BT1 * infNorm U1)) +
        ((2 * γ2 + γ2 ^ 2) * (infNorm L2 * infNorm T2 * infNorm U2) +
          (1 + 2 * γ2 + γ2 ^ 2) * (infNorm L2 * infNorm BT2 * infNorm U2)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat) :
    higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
      (infNorm T_hat) :=
  (higham11_8_infNorm_le_of_sum_aasenChainDeltaABounds
    n hn γ1 γ2 BT1 L1 T1 U1 BT2 L2 T2 U2 DeltaA
    hγ1 hBT1 hγ2 hBT2 hDelta).trans hbudget

/-- Split the final Aasen scalar coefficient comparison into four independent
factorization/solve-chain contributions.  This lets later work prove the
printed `(n-1)^2 γ_{15n+25}` budget one scalar piece at a time. -/
theorem higham11_8_aasen_factor_solve_coeff_le_of_parts
    (n : ℕ)
    (γ_factor γ_solve γ15n25 κL κLT κLhat κLhatT κT κBT κmid
      ηFT ηFB ηST ηSB : ℝ)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * κmid * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) +
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * κmid * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
  linarith

/-- Variant of `higham11_8_aasen_factor_solve_coeff_le_of_parts` where the
four coefficient pieces are allocated as shares of the printed
`(n-1)^2 γ_{15n+25}` budget. -/
theorem higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts
    (n : ℕ)
    (γ_factor γ_solve γ15n25 κL κLT κLhat κLhatT κT κBT κmid
      γFT γFB γST γSB : ℝ)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * κmid * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) +
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * κmid * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
  let α : ℝ := ((n - 1 : ℕ) : ℝ) ^ 2
  have hα : 0 ≤ α := by
    dsimp [α]
    exact sq_nonneg _
  have hparts' : α * γFT + α * γFB + α * γST + α * γSB ≤ α * γ15n25 := by
    calc
      α * γFT + α * γFB + α * γST + α * γSB
          = α * (γFT + γFB + γST + γSB) := by ring
      _ ≤ α * γ15n25 := mul_le_mul_of_nonneg_left hparts hα
  exact
    higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor γ_solve
      γ15n25 κL κLT κLhat κLhatT κT κBT κmid
      (α * γFT) (α * γFB) (α * γST) (α * γSB)
      (by simpa [α] using hFT)
      (by simpa [α] using hFB)
      (by simpa [α] using hST)
      (by simpa [α] using hSB)
      (by simpa [α] using hparts')

/-- Monotonicity helper for coefficient terms with multiplier `2γ+γ^2`. -/
theorem higham11_8_two_gamma_plus_sq_mul_le_of_le
    (γ x y η : ℝ) (hγ : 0 ≤ γ) (hxy : x ≤ y)
    (hyη : (2 * γ + γ ^ 2) * y ≤ η) :
    (2 * γ + γ ^ 2) * x ≤ η := by
  have hcoeff : 0 ≤ 2 * γ + γ ^ 2 := by
    nlinarith [mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hγ, sq_nonneg γ]
  exact (mul_le_mul_of_nonneg_left hxy hcoeff).trans hyη

/-- Monotonicity helper for coefficient terms with multiplier `1+2γ+γ^2`. -/
theorem higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_le
    (γ x y η : ℝ) (hxy : x ≤ y)
    (hyη : (1 + 2 * γ + γ ^ 2) * y ≤ η) :
    (1 + 2 * γ + γ ^ 2) * x ≤ η := by
  have hcoeff : 0 ≤ 1 + 2 * γ + γ ^ 2 := by
    nlinarith [sq_nonneg (γ + 1)]
  exact (mul_le_mul_of_nonneg_left hxy hcoeff).trans hyη

/-- Transport a `2γ+γ^2` coefficient bound through a larger gamma radius and
a larger nonnegative product cap. -/
theorem higham11_8_two_gamma_plus_sq_mul_le_of_majorants
    (γ γb x y η : ℝ) (hγ : 0 ≤ γ) (hγle : γ ≤ γb)
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyη : (2 * γb + γb ^ 2) * y ≤ η) :
    (2 * γ + γ ^ 2) * x ≤ η := by
  have hγb : 0 ≤ γb := hγ.trans hγle
  have hsquares : γ ^ 2 ≤ γb ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hγle) (add_nonneg hγb hγ)]
  have hcoeff_le : 2 * γ + γ ^ 2 ≤ 2 * γb + γb ^ 2 := by
    nlinarith
  have hγbcoeff_nonneg : 0 ≤ 2 * γb + γb ^ 2 := by
    nlinarith [mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hγb, sq_nonneg γb]
  have hleft :
      (2 * γ + γ ^ 2) * x ≤ (2 * γb + γb ^ 2) * y := by
    exact mul_le_mul hcoeff_le hxy hx hγbcoeff_nonneg
  exact hleft.trans hyη

/-- Transport a `1+2γ+γ^2` coefficient bound through a larger gamma radius and
a larger nonnegative product cap. -/
theorem higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants
    (γ γb x y η : ℝ) (hγ : 0 ≤ γ) (hγle : γ ≤ γb)
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyη : (1 + 2 * γb + γb ^ 2) * y ≤ η) :
    (1 + 2 * γ + γ ^ 2) * x ≤ η := by
  have hγb : 0 ≤ γb := hγ.trans hγle
  have hsquares : γ ^ 2 ≤ γb ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hγle) (add_nonneg hγb hγ)]
  have hcoeff_le : 1 + 2 * γ + γ ^ 2 ≤ 1 + 2 * γb + γb ^ 2 := by
    nlinarith
  have hγbcoeff_nonneg : 0 ≤ 1 + 2 * γb + γb ^ 2 := by
    nlinarith [sq_nonneg (γb + 1)]
  have hleft :
      (1 + 2 * γ + γ ^ 2) * x ≤ (1 + 2 * γb + γb ^ 2) * y := by
    exact mul_le_mul hcoeff_le hxy hx hγbcoeff_nonneg
  exact hleft.trans hyη

/-- Product-cap version of
`higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts`.  Each of the four
coefficient pieces may first be bounded by a simpler product cap, and the cap
is then allocated to a share of the printed `(n-1)^2γ_{15n+25}` budget. -/
theorem higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_bounds
    (n : ℕ)
    (γ_factor γ_solve γ15n25 κL κLT κLhat κLhatT κT κBT κmid
      ρFT ρFB ρST ρSB γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hγ_solve : 0 ≤ γ_solve)
    (hρFT : κL * κT * κLT ≤ ρFT)
    (hρFB : κL * κBT * κLT ≤ ρFB)
    (hρST : κLhat * κLhatT ≤ ρST)
    (hρSB : κLhat * κmid * κLhatT ≤ ρSB)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * ρFT ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * ρFB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve + γ_solve ^ 2) * ρST ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve + γ_solve ^ 2) * ρSB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) +
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * κmid * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
  exact
    higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts
      n γ_factor γ_solve γ15n25 κL κLT κLhat κLhatT κT κBT κmid
      γFT γFB γST γSB
      (higham11_8_two_gamma_plus_sq_mul_le_of_le γ_factor
        (κL * κT * κLT) ρFT (((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
        hγ_factor hρFT hFT)
      (higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_le γ_factor
        (κL * κBT * κLT) ρFB (((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
        hρFB hFB)
      (higham11_8_two_gamma_plus_sq_mul_le_of_le γ_solve
        (κLhat * κLhatT) ρST (((n - 1 : ℕ) : ℝ) ^ 2 * γST)
        hγ_solve hρST hST)
      (higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_le γ_solve
        (κLhat * κmid * κLhatT) ρSB (((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
        hρSB hSB)
      hparts

/-- Product-cap and gamma-majorant version of
`higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts` for the concrete
middle-solve term `f(γ_solve) * κmidLU`.  The solve-chain middle term may be
estimated at a larger radius `γ_mid_cap`; monotonicity of Chapter 9's
`f(u)=4u+3u²+u³` transports that middle factor back to `γ_solve`. -/
theorem higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants
    (n : ℕ)
    (γ_factor γ_factor_cap γ_solve γ_solve_cap γ_mid_cap γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU
      ρFT ρFB ρST ρSB γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve : 0 ≤ γ_solve) (hγ_solve_le : γ_solve ≤ γ_solve_cap)
    (hγ_mid_le : γ_solve ≤ γ_mid_cap)
    (hκL : 0 ≤ κL) (hκLT : 0 ≤ κLT)
    (hκLhat : 0 ≤ κLhat) (hκLhatT : 0 ≤ κLhatT)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hρFT : κL * κT * κLT ≤ ρFT)
    (hρFB : κL * κBT * κLT ≤ ρFB)
    (hρST : κLhat * κLhatT ≤ ρST)
    (hρSB :
      κLhat * (higham9_14_f γ_mid_cap * κmidLU) * κLhatT ≤ ρSB)
    (hFT :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) +
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
  have hγ_mid : 0 ≤ γ_mid_cap := hγ_solve.trans hγ_mid_le
  have hf_le : higham9_14_f γ_solve ≤ higham9_14_f γ_mid_cap :=
    higham9_14_f_mono_nonneg hγ_solve hγ_mid_le
  have hf_solve : 0 ≤ higham9_14_f γ_solve :=
    higham9_14_f_nonneg hγ_solve
  have hSBprod :
      κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT ≤ ρSB := by
    have hmid :
        higham9_14_f γ_solve * κmidLU ≤
          higham9_14_f γ_mid_cap * κmidLU :=
      mul_le_mul_of_nonneg_right hf_le hκmidLU
    have hleft :
        κLhat * (higham9_14_f γ_solve * κmidLU) ≤
          κLhat * (higham9_14_f γ_mid_cap * κmidLU) :=
      mul_le_mul_of_nonneg_left hmid hκLhat
    exact (mul_le_mul_of_nonneg_right hleft hκLhatT).trans hρSB
  exact
    higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts
      n γ_factor γ_solve γ15n25 κL κLT κLhat κLhatT κT κBT
      (higham9_14_f γ_solve * κmidLU) γFT γFB γST γSB
      (higham11_8_two_gamma_plus_sq_mul_le_of_majorants
        γ_factor γ_factor_cap (κL * κT * κLT) ρFT
        (((n - 1 : ℕ) : ℝ) ^ 2 * γFT) hγ_factor hγ_factor_le
        (mul_nonneg (mul_nonneg hκL hκT) hκLT) hρFT hFT)
      (higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants
        γ_factor γ_factor_cap (κL * κBT * κLT) ρFB
        (((n - 1 : ℕ) : ℝ) ^ 2 * γFB) hγ_factor hγ_factor_le
        (mul_nonneg (mul_nonneg hκL hκBT) hκLT) hρFB hFB)
      (higham11_8_two_gamma_plus_sq_mul_le_of_majorants
        γ_solve γ_solve_cap (κLhat * κLhatT) ρST
        (((n - 1 : ℕ) : ℝ) ^ 2 * γST) hγ_solve hγ_solve_le
        (mul_nonneg hκLhat hκLhatT) hρST hST)
      (higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants
        γ_solve γ_solve_cap
        (κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT) ρSB
        (((n - 1 : ℕ) : ℝ) ^ 2 * γSB) hγ_solve hγ_solve_le
      (mul_nonneg (mul_nonneg hκLhat (mul_nonneg hf_solve hκmidLU)) hκLhatT)
      hSBprod hSB)
      hparts

/-- Product-cap and gamma-majorant version of the Aasen factorization/solve
coefficient reducer with a single aggregate printed-coefficient hypothesis.
This is the summed counterpart of the four-share product-majorant splitter. -/
theorem higham11_8_aasen_factor_solve_coeff_le_of_product_majorants
    (n : ℕ)
    (γ_factor γ_factor_cap γ_solve γ_solve_cap γ_mid_cap γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU
      ρFT ρFB ρST ρSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve : 0 ≤ γ_solve) (hγ_solve_le : γ_solve ≤ γ_solve_cap)
    (hγ_mid_le : γ_solve ≤ γ_mid_cap)
    (hκL : 0 ≤ κL) (hκLT : 0 ≤ κLT)
    (hκLhat : 0 ≤ κLhat) (hκLhatT : 0 ≤ κLhatT)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hρFT : κL * κT * κLT ≤ ρFT)
    (hρFB : κL * κBT * κLT ≤ ρFB)
    (hρST : κLhat * κLhatT ≤ ρST)
    (hρSB :
      κLhat * (higham9_14_f γ_mid_cap * κmidLU) * κLhatT ≤ ρSB)
    (hcoeff :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT +
        (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB +
        (2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST +
        (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) +
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
  have hf_le : higham9_14_f γ_solve ≤ higham9_14_f γ_mid_cap :=
    higham9_14_f_mono_nonneg hγ_solve hγ_mid_le
  have hf_solve : 0 ≤ higham9_14_f γ_solve :=
    higham9_14_f_nonneg hγ_solve
  have hSBprod :
      κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT ≤ ρSB := by
    have hmid :
        higham9_14_f γ_solve * κmidLU ≤
          higham9_14_f γ_mid_cap * κmidLU :=
      mul_le_mul_of_nonneg_right hf_le hκmidLU
    have hleft :
        κLhat * (higham9_14_f γ_solve * κmidLU) ≤
          κLhat * (higham9_14_f γ_mid_cap * κmidLU) :=
      mul_le_mul_of_nonneg_left hmid hκLhat
    exact (mul_le_mul_of_nonneg_right hleft hκLhatT).trans hρSB
  exact
    higham11_8_aasen_factor_solve_coeff_le_of_parts
      n γ_factor γ_solve γ15n25 κL κLT κLhat κLhatT κT κBT
      (higham9_14_f γ_solve * κmidLU)
      ((2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT)
      ((1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB)
      ((2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST)
      ((1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB)
      (higham11_8_two_gamma_plus_sq_mul_le_of_majorants
        γ_factor γ_factor_cap (κL * κT * κLT) ρFT
        ((2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT)
        hγ_factor hγ_factor_le (mul_nonneg (mul_nonneg hκL hκT) hκLT)
        hρFT le_rfl)
      (higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants
        γ_factor γ_factor_cap (κL * κBT * κLT) ρFB
        ((1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB)
        hγ_factor hγ_factor_le (mul_nonneg (mul_nonneg hκL hκBT) hκLT)
        hρFB le_rfl)
      (higham11_8_two_gamma_plus_sq_mul_le_of_majorants
        γ_solve γ_solve_cap (κLhat * κLhatT) ρST
        ((2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST)
        hγ_solve hγ_solve_le (mul_nonneg hκLhat hκLhatT) hρST le_rfl)
      (higham11_8_one_plus_two_gamma_plus_sq_mul_le_of_majorants
        γ_solve γ_solve_cap
        (κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT) ρSB
        ((1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB)
        hγ_solve hγ_solve_le
        (mul_nonneg (mul_nonneg hκLhat (mul_nonneg hf_solve hκmidLU)) hκLhatT)
        hSBprod le_rfl)
      (by simpa [add_assoc] using hcoeff)

/-- Concrete-product specialization of
`higham11_8_aasen_factor_solve_coeff_le_of_product_majorants`, where the
product caps are the exact products from the relative Aasen norm budget. -/
theorem higham11_8_aasen_factor_solve_coeff_le_of_concrete_product_majorants
    (n : ℕ)
    (γ_factor γ_factor_cap γ_solve γ_solve_cap γ_mid_cap γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve : 0 ≤ γ_solve) (hγ_solve_le : γ_solve ≤ γ_solve_cap)
    (hγ_mid_le : γ_solve ≤ γ_mid_cap)
    (hκL : 0 ≤ κL) (hκLT : 0 ≤ κLT)
    (hκLhat : 0 ≤ κLhat) (hκLhatT : 0 ≤ κLhatT)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hcoeff :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κBT * κLT) +
        (2 * γ_solve_cap + γ_solve_cap ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) *
          (κLhat * (higham9_14_f γ_mid_cap * κmidLU) * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) +
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
  exact
    higham11_8_aasen_factor_solve_coeff_le_of_product_majorants
      n γ_factor γ_factor_cap γ_solve γ_solve_cap γ_mid_cap γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU
      (κL * κT * κLT) (κL * κBT * κLT) (κLhat * κLhatT)
      (κLhat * (higham9_14_f γ_mid_cap * κmidLU) * κLhatT)
      hγ_factor hγ_factor_le hγ_solve hγ_solve_le hγ_mid_le
      hκL hκLT hκLhat hκLhatT hκT hκBT hκmidLU
      le_rfl le_rfl le_rfl le_rfl
      (by simpa [add_assoc] using hcoeff)

/-- Four-share concrete-product specialization of
`higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants`.
The product caps are instantiated by the exact products from the relative
Aasen norm budget, while the gamma radii may still be enlarged. -/
theorem higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_concrete_product_majorants
    (n : ℕ)
    (γ_factor γ_factor_cap γ_solve γ_solve_cap γ_mid_cap γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU
      γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve : 0 ≤ γ_solve) (hγ_solve_le : γ_solve ≤ γ_solve_cap)
    (hγ_mid_le : γ_solve ≤ γ_mid_cap)
    (hκL : 0 ≤ κL) (hκLT : 0 ≤ κLT)
    (hκLhat : 0 ≤ κLhat) (hκLhatT : 0 ≤ κLhatT)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hFT :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) *
        (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve_cap + γ_solve_cap ^ 2) * (κLhat * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) *
        (κLhat * (higham9_14_f γ_mid_cap * κmidLU) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
      (2 * γ_solve + γ_solve ^ 2) * (κLhat * κLhatT) +
      (1 + 2 * γ_solve + γ_solve ^ 2) *
        (κLhat * (higham9_14_f γ_solve * κmidLU) * κLhatT) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
  exact
    higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants
      n γ_factor γ_factor_cap γ_solve γ_solve_cap γ_mid_cap γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU
      (κL * κT * κLT) (κL * κBT * κLT) (κLhat * κLhatT)
      (κLhat * (higham9_14_f γ_mid_cap * κmidLU) * κLhatT)
      γFT γFB γST γSB
      hγ_factor hγ_factor_le hγ_solve hγ_solve_le hγ_mid_le
      hκL hκLT hκLhat hκLhatT hκT hκBT hκmidLU
      le_rfl le_rfl le_rfl le_rfl hFT hFB hST hSB hparts

/-- Scalar reducer for the norm-budget hypothesis in the Aasen
factorization-plus-solve wrapper.  It isolates the remaining printed
coefficient bookkeeping from primitive infinity-norm bounds for the exact and
computed factors. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * κmid * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  let τ : ℝ := infNorm T_hat
  let M : Fin n → Fin n → ℝ := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
  let cF_T : ℝ := 2 * γ_factor + γ_factor ^ 2
  let cF_B : ℝ := 1 + 2 * γ_factor + γ_factor ^ 2
  let γn : ℝ := gamma fp n
  let cS_T : ℝ := 2 * γn + γn ^ 2
  let cS_B : ℝ := 1 + 2 * γn + γn ^ 2
  have hτ : 0 ≤ τ := by
    dsimp [τ]
    exact infNorm_nonneg T_hat
  have hγn : 0 ≤ γn := by
    dsimp [γn]
    exact gamma_nonneg fp hn
  have hcF_T : 0 ≤ cF_T := by
    dsimp [cF_T]
    nlinarith [mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hγ_factor,
      sq_nonneg γ_factor]
  have hcF_B : 0 ≤ cF_B := by
    dsimp [cF_B]
    nlinarith [sq_nonneg (γ_factor + 1)]
  have hcS_T : 0 ≤ cS_T := by
    dsimp [cS_T, γn]
    nlinarith [mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hγn,
      sq_nonneg γn]
  have hcS_B : 0 ≤ cS_B := by
    dsimp [cS_B, γn]
    nlinarith [sq_nonneg (γn + 1)]
  have hF_T :
      infNorm L * infNorm T * infNorm (fun r c => L c r) ≤
        (κL * κT * κLT) * τ := by
    have h12 : infNorm L * infNorm T ≤ κL * (κT * τ) :=
      mul_le_mul hL (by simpa [τ] using hT) (infNorm_nonneg T) hκL
    have h123 :
        (infNorm L * infNorm T) * infNorm (fun r c => L c r) ≤
          (κL * (κT * τ)) * κLT :=
      mul_le_mul h12 hLT (infNorm_nonneg (fun r c => L c r))
        (mul_nonneg hκL (mul_nonneg hκT hτ))
    calc
      infNorm L * infNorm T * infNorm (fun r c => L c r)
          = (infNorm L * infNorm T) * infNorm (fun r c => L c r) := by ring
      _ ≤ (κL * (κT * τ)) * κLT := h123
      _ = (κL * κT * κLT) * τ := by ring
  have hF_B :
      infNorm L * infNorm BT_factor * infNorm (fun r c => L c r) ≤
        (κL * κBT * κLT) * τ := by
    have h12 : infNorm L * infNorm BT_factor ≤ κL * (κBT * τ) :=
      mul_le_mul hL (by simpa [τ] using hBT) (infNorm_nonneg BT_factor) hκL
    have h123 :
        (infNorm L * infNorm BT_factor) * infNorm (fun r c => L c r) ≤
          (κL * (κBT * τ)) * κLT :=
      mul_le_mul h12 hLT (infNorm_nonneg (fun r c => L c r))
        (mul_nonneg hκL (mul_nonneg hκBT hτ))
    calc
      infNorm L * infNorm BT_factor * infNorm (fun r c => L c r)
          = (infNorm L * infNorm BT_factor) * infNorm (fun r c => L c r) := by ring
      _ ≤ (κL * (κBT * τ)) * κLT := h123
      _ = (κL * κBT * κLT) * τ := by ring
  have hS_T :
      infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r) ≤
        (κLhat * κLhatT) * τ := by
    have hprod :
        infNorm L_hat * infNorm (fun r c => L_hat c r) ≤
          κLhat * κLhatT :=
      mul_le_mul hLhat hLhatT (infNorm_nonneg (fun r c => L_hat c r)) hκLhat
    calc
      infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)
          = (infNorm L_hat * infNorm (fun r c => L_hat c r)) * τ := by
            simp [τ]
            ring
      _ ≤ (κLhat * κLhatT) * τ :=
          mul_le_mul_of_nonneg_right hprod hτ
  have hS_B :
      infNorm L_hat * infNorm M * infNorm (fun r c => L_hat c r) ≤
        (κLhat * κmid * κLhatT) * τ := by
    have h12 : infNorm L_hat * infNorm M ≤ κLhat * (κmid * τ) :=
      mul_le_mul hLhat (by simpa [M, τ] using hmiddle) (infNorm_nonneg M) hκLhat
    have h123 :
        (infNorm L_hat * infNorm M) * infNorm (fun r c => L_hat c r) ≤
          (κLhat * (κmid * τ)) * κLhatT :=
      mul_le_mul h12 hLhatT (infNorm_nonneg (fun r c => L_hat c r))
        (mul_nonneg hκLhat (mul_nonneg hκmid hτ))
    calc
      infNorm L_hat * infNorm M * infNorm (fun r c => L_hat c r)
          = (infNorm L_hat * infNorm M) * infNorm (fun r c => L_hat c r) := by ring
      _ ≤ (κLhat * (κmid * τ)) * κLhatT := h123
      _ = (κLhat * κmid * κLhatT) * τ := by ring
  have hsum :
      (cF_T * (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
        cF_B * (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
      (cS_T * (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
        cS_B * (infNorm L_hat * infNorm M * infNorm (fun r c => L_hat c r))) ≤
        (cF_T * (κL * κT * κLT) +
          cF_B * (κL * κBT * κLT) +
          cS_T * (κLhat * κLhatT) +
          cS_B * (κLhat * κmid * κLhatT)) * τ := by
    calc
      (cF_T * (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
        cF_B * (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
      (cS_T * (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
        cS_B * (infNorm L_hat * infNorm M * infNorm (fun r c => L_hat c r)))
          ≤
        (cF_T * ((κL * κT * κLT) * τ) +
          cF_B * ((κL * κBT * κLT) * τ)) +
        (cS_T * ((κLhat * κLhatT) * τ) +
          cS_B * ((κLhat * κmid * κLhatT) * τ)) :=
            add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_left hF_T hcF_T)
                (mul_le_mul_of_nonneg_left hF_B hcF_B))
              (add_le_add
                (mul_le_mul_of_nonneg_left hS_T hcS_T)
                (mul_le_mul_of_nonneg_left hS_B hcS_B))
      _ = (cF_T * (κL * κT * κLT) +
          cF_B * (κL * κBT * κLT) +
          cS_T * (κLhat * κLhatT) +
          cS_B * (κLhat * κmid * κLhatT)) * τ := by ring
  calc
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r)))
        ≤ (cF_T * (κL * κT * κLT) +
          cF_B * (κL * κBT * κLT) +
          cS_T * (κLhat * κLhatT) +
          cS_B * (κLhat * κmid * κLhatT)) * τ := by
            simpa [cF_T, cF_B, cS_T, cS_B, γn, M] using hsum
    _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
        have hcoeff' :
            cF_T * (κL * κT * κLT) +
              cF_B * (κL * κBT * κLT) +
              cS_T * (κLhat * κLhatT) +
              cS_B * (κLhat * κmid * κLhatT) ≤
              ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 := by
          simpa [cF_T, cF_B, cS_T, cS_B, γn] using hcoeff
        simpa [τ, mul_assoc] using
          mul_le_mul_of_nonneg_right hcoeff' hτ

/-- Scalar reducer variant where the computed-factor norm bounds are derived
from the relative entrywise `L_hat` perturbation and the source-factor norm
bounds. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * κmid * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  have hγ1 : 0 ≤ 1 + γ_factor := by linarith
  have hLhat_norm : infNorm L_hat ≤ (1 + γ_factor) * κL := by
    calc
      infNorm L_hat ≤ (1 + γ_factor) * infNorm L :=
        higham11_8_infNorm_factor_le_of_relative_entry_bound n L L_hat
          γ_factor hγ_factor hLhat_entry
      _ ≤ (1 + γ_factor) * κL := mul_le_mul_of_nonneg_left hL hγ1
  have hLhatT_norm :
      infNorm (fun r c => L_hat c r) ≤
        (1 + γ_factor) * κLT := by
    calc
      infNorm (fun r c => L_hat c r) ≤
          (1 + γ_factor) * infNorm (fun r c => L c r) :=
        higham11_8_infNorm_factorTranspose_le_of_relative_entry_bound n
          L L_hat γ_factor hγ_factor hLhat_entry
      _ ≤ (1 + γ_factor) * κLT := mul_le_mul_of_nonneg_left hLT hγ1
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT ((1 + γ_factor) * κL) ((1 + γ_factor) * κLT) κT κBT κmid
      hγ_factor hn hκL (mul_nonneg hγ1 hκL) hκT hκBT hκmid
      hL hLT hLhat_norm hLhatT_norm hT hBT hmiddle hcoeff

/-- Relative-factor scalar reducer with the final printed coefficient supplied
as four shares of the printed `(n-1)^2 γ_{15n+25}` budget. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_gamma_parts
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmid γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * κmid * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κT κBT κmid hγ_factor hn hκL hκT hκBT hκmid hLhat_entry
      hL hLT hT hBT hmiddle
      (higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT ((1 + γ_factor) * κL)
        ((1 + γ_factor) * κLT) κT κBT κmid γFT γFB γST γSB
        hFT hFB hST hSB hparts)

/-- Scalar norm-budget reducer with the middle tridiagonal-solve budget
discharged from a tridiagonal LU factor-product bound and the final printed
coefficient supplied as four independent scalar pieces. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_middle_factor_product_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  apply higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
    fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
    κL κLT κLhat κLhatT κT κBT (higham9_14_f (gamma fp n) * κmidLU)
    hγ_factor hn hκL hκLhat hκT hκBT
    (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
    hL hLT hLhat hLhatT hT hBT
  · exact
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
        fp n hn_pos L_T_hat U_T_hat T_hat κmidLU hn hmiddle_factors
  · exact
      higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT κLhat κLhatT κT κBT
        (higham9_14_f (gamma fp n) * κmidLU) ηFT ηFB ηST ηSB
        hFT hFB hST hSB hparts

/-- Scalar norm-budget reducer with the middle tridiagonal-solve budget
discharged from an absolute LU product norm bound and the final printed
coefficient supplied as four independent scalar pieces. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_absLU_norm_coeff_parts
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (habs :
      infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) ≤
        κmidLU * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  apply higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
    fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
    κL κLT κLhat κLhatT κT κBT (higham9_14_f (gamma fp n) * κmidLU)
    hγ_factor hn hκL hκLhat hκT hκBT
    (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
    hL hLT hLhat hLhatT hT hBT
  · exact
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_norm_bound
        fp n L_T_hat U_T_hat T_hat κmidLU hn habs
  · exact
      higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT κLhat κLhatT κT κBT
        (higham9_14_f (gamma fp n) * κmidLU) ηFT ηFB ηST ηSB
        hFT hFB hST hSB hparts

/-- Scalar norm-budget reducer with the middle tridiagonal-solve budget
discharged from a componentwise absolute LU product bound against `T_hat`,
and the final printed coefficient supplied as four independent scalar pieces. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hentry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  apply higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
    fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
    κL κLT κLhat κLhatT κT κBT (higham9_14_f (gamma fp n) * κmidLU)
    hγ_factor hn hκL hκLhat hκT hκBT
    (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
    hL hLT hLhat hLhatT hT hBT
  · exact
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound
        fp n L_T_hat U_T_hat T_hat κmidLU hκmidLU hn hentry
  · exact
      higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT κLhat κLhatT κT κBT
        (higham9_14_f (gamma fp n) * κmidLU) ηFT ηFB ηST ηSB
        hFT hFB hST hSB hparts

/-- Scalar norm-budget reducer where the middle tridiagonal-solve budget is
discharged by Chapter 9's column-dominant tridiagonal LU growth theorem,
yielding the concrete middle coefficient `3 * f(γ_n)`. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff_parts
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  apply higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
    fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
    κL κLT κLhat κLhatT κT κBT (higham9_14_f (gamma fp n) * 3)
    hγ_factor hn hκL hκLhat hκT hκBT
    (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) (by norm_num))
    hL hLT hLhat hLhatT hT hBT
  · exact
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_colDiagDom_LUFactSpec
        fp n T_hat L_T_hat U_T_hat hn hLU hdetT hT_tridiag hColDom
  · exact
      higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT κLhat κLhatT κT κBT
        (higham9_14_f (gamma fp n) * 3) ηFT ηFB ηST ηSB
        hFT hFB hST hSB hparts

/-- Column-dominant middle-budget scalar reducer with the final printed
coefficient supplied as one direct sum inequality. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff_parts
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT
      ((2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT))
      ((1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT))
      ((2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT))
      ((1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT))
      hγ_factor hn hκL hκLhat hκT hκBT hLU hdetT hT_tridiag hColDom
      hL hLT hLhat hLhatT hT hBT (le_refl _) (le_refl _) (le_refl _)
      (le_refl _) hcoeff

/-- Scalar norm-budget reducer where the middle tridiagonal-solve budget is
discharged by Chapter 9's row-dominant tridiagonal LU growth theorem, yielding
the concrete middle coefficient `3 * f(γ_n)`. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff_parts
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  apply higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
    fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
    κL κLT κLhat κLhatT κT κBT (higham9_14_f (gamma fp n) * 3)
    hγ_factor hn hκL hκLhat hκT hκBT
    (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) (by norm_num))
    hL hLT hLhat hLhatT hT hBT
  · exact
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_rowDiagDom_LUFactSpec
        fp n T_hat L_T_hat U_T_hat hn hLU hdetT hT_tridiag hRowDom
  · exact
      higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT κLhat κLhatT κT κBT
        (higham9_14_f (gamma fp n) * 3) ηFT ηFB ηST ηSB
        hFT hFB hST hSB hparts

/-- Row-dominant middle-budget scalar reducer with the final printed
coefficient supplied as one direct sum inequality. -/
theorem higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ)
    (L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hn : gammaValid fp n)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL : infNorm L ≤ κL)
    (hLT : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat : infNorm L_hat ≤ κLhat)
    (hLhatT : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT : infNorm T ≤ κT * infNorm T_hat)
    (hBT : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    ((2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
      (1 + 2 * γ_factor + γ_factor ^ 2) *
        (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
    ((2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (infNorm L_hat *
          infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
          infNorm (fun r c => L_hat c r))) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat := by
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff_parts
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT
      ((2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT))
      ((1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT))
      ((2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT))
      ((1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT))
      hγ_factor hn hκL hκLhat hκT hκBT hLU hdetT hT_tridiag hRowDom
      hL hLT hLhat hLhatT hT hBT (le_refl _) (le_refl _) (le_refl _)
      (le_refl _) hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error together
with the printed Theorem 11.8 normwise predicate, using a single scalar
normwise comparison for the summed factorization and solve-chain budgets. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 : ℝ) (hγ_factor : 0 ≤ γ_factor)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hbudget_norm :
      ((2 * γ_factor + γ_factor ^ 2) *
          (infNorm L * infNorm T * infNorm (fun r c => L c r)) +
        (1 + 2 * γ_factor + γ_factor ^ 2) *
          (infNorm L * infNorm BT_factor * infNorm (fun r c => L c r))) +
      ((2 * gamma fp n + (gamma fp n) ^ 2) *
          (infNorm L_hat * infNorm T_hat * infNorm (fun r c => L_hat c r)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (infNorm L_hat *
            infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) *
            infNorm (fun r c => L_hat c r))) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat BT_solve B_factor B_solve
  obtain ⟨DeltaA, hDeltaA, hsource⟩ :=
    higham11_8_fl_aasen_factor_solve_source_backward_error
      fp n A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat hThat
  refine ⟨DeltaA, hDeltaA, hsource, ?_⟩
  apply higham11_8_aasenNormwiseBackwardBound_of_sum_aasenChainDeltaABounds
    n hn_pos γ_factor (gamma fp n) γ15n25
    BT_factor L T (fun r c => L c r)
    BT_solve L_hat T_hat U_outer DeltaA T_hat
    hγ_factor hBT_factor (gamma_nonneg fp hn)
  · intro p q
    simpa [BT_solve] using
      higham11_15_aasenMiddleSolveBudget_nonneg fp n L_T_hat U_T_hat hn p q
  · intro i j
    simpa [B_factor, B_solve, BT_solve, U_outer] using hDeltaA i j
  · simpa [BT_solve, U_outer] using hbudget_norm

/-- Rounded Aasen factorization-plus-solve source backward error together
with the printed Theorem 11.8 normwise predicate, using primitive factor
norm bounds and one scalar coefficient comparison to discharge the norm-budget
hypothesis. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * κmid * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_factor_norm_bounds
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT κmid hγ_factor hn hκL hκLhat hκT
      hκBT hκmid hL_norm hLT_norm hLhat_norm hLhatT_norm hT_norm hBT_norm
      hmiddle_norm hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from the
relative entrywise `L_hat` perturbation and source-factor norm bounds. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * κmid * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κT κBT κmid hγ_factor hn hκL hκT hκBT hκmid hLhat_entry
      hL_norm hLT_norm hT_norm hBT_norm hmiddle_norm hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from the
relative entrywise `L_hat` perturbation and accepting the printed coefficient
as four gamma-share obligations. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds_gamma_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmid γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * κmid * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_relative_factor_norm_bounds_gamma_parts
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κT κBT κmid γFT γFB γST γSB hγ_factor hn hκL hκT
      hκBT hκmid hLhat_entry hL_norm hLT_norm hT_norm hBT_norm
      hmiddle_norm hFT hFB hST hSB hparts

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from a
supplied relative `L_hat` hypothesis and discharging the middle
tridiagonal-solve norm budget from a relative bound on the tridiagonal LU
factor product. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT
      (higham9_14_f (gamma fp n) * κmidLU) hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
        fp n hn_pos L_T_hat U_T_hat T_hat κmidLU hn hmiddle_factors)
      hcoeff

/-- Relative middle-factor-product wrapper variant where the factorization-side
`BT_factor` norm bound is derived from a componentwise bound against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT κmidLU hγ_factor hκL
      hκT hκBT hκmidLU hBT_factor h20 hLhat_diag hLhat_lower
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
      hL_norm hLT_norm hT_norm hBT_norm hmiddle_factors hcoeff

/-- Relative middle-factor-product wrapper with the concrete factorization-side
`T_hat` budget `|T_hat - T| ≤ κBT |T_hat|`, instantiating `BT_factor`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_T_factor
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_middle_factor_product_bound_componentwise_BT
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat
      (fun i j => κBT * |T_hat i j|) b DeltaT_LU γ_factor γ15n25 κL
      κLT κT κBT κmidLU hγ_factor hκL hκT hκBT hκmidLU
      (by
        intro i j
        exact mul_nonneg hκBT (abs_nonneg _))
      h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower
      hT_U_upper hn hprod hLhat_entry hThat_component hL_norm hLT_norm
      hT_norm (fun i j => le_rfl) hmiddle_factors hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from a
supplied relative `L_hat` hypothesis and discharging the middle
tridiagonal-solve budget from an absolute LU product norm bound. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_norm_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (habs :
      infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) ≤
        κmidLU * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT
      (higham9_14_f (gamma fp n) * κmidLU) hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_norm_bound
        fp n L_T_hat U_T_hat T_hat κmidLU hn habs)
      (higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT ((1 + γ_factor) * κL)
        ((1 + γ_factor) * κLT) κT κBT
        (higham9_14_f (gamma fp n) * κmidLU) ηFT ηFB ηST ηSB
        hFT hFB hST hSB hparts)

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from a
supplied relative `L_hat` hypothesis and discharging the middle
tridiagonal-solve budget from a componentwise absolute LU product bound. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hentry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_norm_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB hγ_factor hκL hκT hκBT hκmidLU hBT_factor
      h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower
      hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm hT_norm
      hBT_norm
      (higham11_15_absLU_infNorm_le_of_componentwise_T_bound
        n L_T_hat U_T_hat T_hat κmidLU hκmidLU hentry)
      hFT hFB hST hSB hparts

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from a
supplied relative `L_hat` hypothesis while deriving both `BT_factor` and
middle abs-LU norms from componentwise comparisons against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_componentwise_BT_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_norm_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT κmidLU ηFT ηFB ηST
      ηSB hγ_factor hκL hκT hκBT hκmidLU hBT_factor h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod
      hLhat_entry hThat hL_norm hLT_norm hT_norm hBT_norm
      (higham11_15_absLU_infNorm_le_of_componentwise_T_bound
        n L_T_hat U_T_hat T_hat κmidLU hκmidLU hmiddle_entry)
      hFT hFB hST hSB hparts

/-- Relative abs-LU componentwise-middle wrapper with the concrete
factorization-side `T_hat` budget `|T_hat - T| ≤ κBT |T_hat|`, instantiating
`BT_factor`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_componentwise_BT_absLU_componentwise_T_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat
      (fun i j => κBT * |T_hat i j|) b DeltaT_LU γ_factor γ15n25 κL
      κLT κT κBT κmidLU ηFT ηFB ηST ηSB hγ_factor hκL hκT hκBT
      hκmidLU
      (by
        intro i j
        exact mul_nonneg hκBT (abs_nonneg _))
      h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower
      hT_U_upper hn hprod hLhat_entry hThat_component hL_norm hLT_norm
      hT_norm (fun i j => le_rfl) hmiddle_entry hFT hFB hST hSB hparts

/-- Relative abs-LU componentwise-middle wrapper with the concrete
factorization-side `T_hat` budget, using four shares of the printed
`(n-1)^2 γ_{15n+25}` coefficient. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_gamma_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  let α : ℝ := ((n - 1 : ℕ) : ℝ) ^ 2
  have hα : 0 ≤ α := by
    dsimp [α]
    exact sq_nonneg _
  have hparts' : α * γFT + α * γFB + α * γST + α * γSB ≤ α * γ15n25 := by
    calc
      α * γFT + α * γFB + α * γST + α * γSB
          = α * (γFT + γFB + γST + γSB) := by ring
      _ ≤ α * γ15n25 := mul_le_mul_of_nonneg_left hparts hα
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ15n25 κL κLT κT κBT κmidLU (α * γFT) (α * γFB)
      (α * γST) (α * γSB) hγ_factor hκL hκT hκBT hκmidLU h20
      hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper
      hn hprod hLhat_entry hThat_component hL_norm hLT_norm hT_norm
      hmiddle_entry (by simpa [α] using hFT) (by simpa [α] using hFB)
      (by simpa [α] using hST) (by simpa [α] using hSB)
      (by simpa [α] using hparts')

/-- Relative abs-LU componentwise-middle wrapper with the concrete
factorization-side `T_hat` budget, where the four coefficient shares are
discharged from product caps and larger gamma radii. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU
      ρFT ρFB ρST ρSB γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hρFT : κL * κT * κLT ≤ ρFT)
    (hρFB : κL * κBT * κLT ≤ ρFB)
    (hρST :
      ((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT) ≤ ρST)
    (hρSB :
      ((1 + γ_factor) * κL) * (higham9_14_f γ_mid_cap * κmidLU) *
          ((1 + γ_factor) * κLT) ≤ ρSB)
    (hFT :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hκLT : 0 ≤ κLT := (infNorm_nonneg (fun r c => L c r)).trans hLT_norm
  have hγ1 : 0 ≤ 1 + γ_factor := by linarith
  have hBT_factor : ∀ i j : Fin n, 0 ≤ κBT * |T_hat i j| := by
    intro i j
    exact mul_nonneg hκBT (abs_nonneg _)
  have hBT_norm :
      infNorm (fun i j : Fin n => κBT * |T_hat i j|) ≤
        κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound
      n (fun i j : Fin n => κBT * |T_hat i j|) T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
  have hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        (higham9_14_f (gamma fp n) * κmidLU) * infNorm T_hat :=
    higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound
      fp n L_T_hat U_T_hat T_hat κmidLU hκmidLU hn hmiddle_entry
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat
      (fun i j => κBT * |T_hat i j|) b DeltaT_LU γ_factor γ15n25
      κL κLT κT κBT (higham9_14_f (gamma fp n) * κmidLU)
      hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat_component hL_norm
      hLT_norm hT_norm hBT_norm hmiddle_norm
      (higham11_8_aasen_factor_solve_coeff_le_of_gamma_parts_product_majorants
        n γ_factor γ_factor_cap (gamma fp n) γ_solve_cap γ_mid_cap γ15n25
        κL κLT ((1 + γ_factor) * κL) ((1 + γ_factor) * κLT)
        κT κBT κmidLU ρFT ρFB ρST ρSB γFT γFB γST γSB
        hγ_factor hγ_factor_le (gamma_nonneg fp hn) hγ_solve_le hγ_mid_le
      hκL hκLT (mul_nonneg hγ1 hκL) (mul_nonneg hγ1 hκLT)
      hκT hκBT hκmidLU hρFT hρFB hρST hρSB hFT hFB hST hSB hparts)

/-- Relative abs-LU componentwise-middle wrapper with the concrete
factorization-side `T_hat` budget, discharging the final coefficient from one
aggregate product-cap/gamma-majorant inequality. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU ρFT ρFB ρST ρSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hρFT : κL * κT * κLT ≤ ρFT)
    (hρFB : κL * κBT * κLT ≤ ρFB)
    (hρST :
      ((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT) ≤ ρST)
    (hρSB :
      ((1 + γ_factor) * κL) * (higham9_14_f γ_mid_cap * κmidLU) *
          ((1 + γ_factor) * κLT) ≤ ρSB)
    (hcoeff :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT +
        (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB +
        (2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST +
        (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hκLT : 0 ≤ κLT := (infNorm_nonneg (fun r c => L c r)).trans hLT_norm
  have hγ1 : 0 ≤ 1 + γ_factor := by linarith
  have hBT_factor : ∀ i j : Fin n, 0 ≤ κBT * |T_hat i j| := by
    intro i j
    exact mul_nonneg hκBT (abs_nonneg _)
  have hBT_norm :
      infNorm (fun i j : Fin n => κBT * |T_hat i j|) ≤
        κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound
      n (fun i j : Fin n => κBT * |T_hat i j|) T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
  have hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        (higham9_14_f (gamma fp n) * κmidLU) * infNorm T_hat :=
    higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound
      fp n L_T_hat U_T_hat T_hat κmidLU hκmidLU hn hmiddle_entry
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat
      (fun i j => κBT * |T_hat i j|) b DeltaT_LU γ_factor γ15n25
      κL κLT κT κBT (higham9_14_f (gamma fp n) * κmidLU)
      hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat_component hL_norm
      hLT_norm hT_norm hBT_norm hmiddle_norm
      (higham11_8_aasen_factor_solve_coeff_le_of_product_majorants
        n γ_factor γ_factor_cap (gamma fp n) γ_solve_cap γ_mid_cap γ15n25
        κL κLT ((1 + γ_factor) * κL) ((1 + γ_factor) * κLT)
        κT κBT κmidLU ρFT ρFB ρST ρSB
        hγ_factor hγ_factor_le (gamma_nonneg fp hn) hγ_solve_le hγ_mid_le
        hκL hκLT (mul_nonneg hγ1 hκL) (mul_nonneg hγ1 hκLT)
        hκT hκBT hκmidLU hρFT hρFB hρST hρSB hcoeff)

/-- Relative abs-LU componentwise-middle wrapper with the concrete
factorization-side `T_hat` budget and exact product majorants, leaving only
one aggregate printed-coefficient comparison. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hcoeff :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κBT * κLT) +
        (2 * γ_solve_cap + γ_solve_cap ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) *
          (((1 + γ_factor) * κL) *
            (higham9_14_f γ_mid_cap * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants_coeff
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU
      (κL * κT * κLT) (κL * κBT * κLT)
      (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT))
      (((1 + γ_factor) * κL) * (higham9_14_f γ_mid_cap * κmidLU) *
        ((1 + γ_factor) * κLT))
      hγ_factor hγ_factor_le hγ_solve_le hγ_mid_le hκL hκT hκBT
      hκmidLU h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower
      hT_U_upper hn hprod hLhat_entry hThat_component hL_norm hLT_norm
      hT_norm hmiddle_entry le_rfl le_rfl le_rfl le_rfl
      (by simpa [add_assoc] using hcoeff)

/-- Relative abs-LU componentwise-middle wrapper with the concrete
factorization-side `T_hat` budget and exact product majorants, using four
shares of the printed coefficient. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve_cap + γ_solve_cap ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) *
        (((1 + γ_factor) * κL) *
          (higham9_14_f γ_mid_cap * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU
      (κL * κT * κLT) (κL * κBT * κLT)
      (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT))
      (((1 + γ_factor) * κL) * (higham9_14_f γ_mid_cap * κmidLU) *
        ((1 + γ_factor) * κLT))
      γFT γFB γST γSB hγ_factor hγ_factor_le hγ_solve_le hγ_mid_le
      hκL hκT hκBT hκmidLU h20 hLhat_diag hLhat_lower hT_L_diag
      hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat_component
      hL_norm hLT_norm hT_norm hmiddle_entry le_rfl le_rfl le_rfl le_rfl
      hFT hFB hST hSB hparts

/-- Factor-norm wrapper variant where the factorization-side `BT_factor`
norm bound is derived from a componentwise bound against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * κmid * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid hγ_factor hκL
    hκLhat hκT hκBT hκmid hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
    hL_norm hLT_norm hLhat_norm hLhatT_norm hT_norm
  · apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  · exact hmiddle_norm
  · exact hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, where the middle tridiagonal-solve norm budget is
discharged from a relative bound on the tridiagonal LU factor product. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_middle_factor_product_bound
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
    (higham9_14_f (gamma fp n) * κmidLU)
    hγ_factor hκL hκLhat hκT hκBT
    (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
    hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
    hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
    hLhat_norm hLhatT_norm hT_norm hBT_norm
  · exact
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
        fp n hn_pos L_T_hat U_T_hat T_hat κmidLU hn hmiddle_factors
  · simpa using hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, where the middle tridiagonal-solve budget is
discharged from an absolute LU product norm bound and the final scalar
coefficient is supplied in four pieces. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_norm_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (habs :
      infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) ≤
        κmidLU * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_absLU_norm_coeff_parts
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU ηFT ηFB ηST ηSB hγ_factor hn
      hκL hκLhat hκT hκBT hκmidLU hL_norm hLT_norm hLhat_norm
      hLhatT_norm hT_norm hBT_norm habs hFT hFB hST hSB hparts

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, where the middle tridiagonal-solve budget is
discharged from a componentwise absolute LU product bound and the final scalar
coefficient is supplied in four pieces. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hentry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_absLU_componentwise_T_coeff_parts
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT κmidLU ηFT ηFB ηST ηSB hγ_factor hn
      hκL hκLhat hκT hκBT hκmidLU hL_norm hLT_norm hLhat_norm
      hLhatT_norm hT_norm hBT_norm hentry hFT hFB hST hSB hparts

/-- Rounded Aasen factorization-plus-solve source backward error where both
the factorization-side `BT_factor` norm and the middle tridiagonal-solve norm
are derived from componentwise bounds against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_componentwise_BT_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds_componentwise_BT
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      (higham9_14_f (gamma fp n) * κmidLU)
      hγ_factor hκL hκLhat hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_component
  · exact
      higham11_15_aasenMiddleSolveBudget_infNorm_le_of_absLU_componentwise_T_bound
        fp n L_T_hat U_T_hat T_hat κmidLU hκmidLU hn hmiddle_entry
  · exact
      higham11_8_aasen_factor_solve_coeff_le_of_parts n γ_factor
        (gamma fp n) γ15n25 κL κLT κLhat κLhatT κT κBT
        (higham9_14_f (gamma fp n) * κmidLU) ηFT ηFB ηST ηSB
        hFT hFB hST hSB hparts

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, where the middle tridiagonal-solve budget is
discharged by Chapter 9's column-dominant tridiagonal LU growth theorem and
the final scalar coefficient is supplied in four pieces. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff_parts
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT ηFT ηFB ηST ηSB hγ_factor hn hκL
      hκLhat hκT hκBT hLU hdetT hT_tridiag hColDom hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_norm hFT hFB hST hSB hparts

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, where the middle tridiagonal-solve budget is
discharged by Chapter 9's row-dominant tridiagonal LU growth theorem and the
final scalar coefficient is supplied in four pieces. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff_parts
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT ηFT ηFB ηST ηSB hγ_factor hn hκL
      hκLhat hκT hκBT hLU hdetT hT_tridiag hRowDom hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_norm hFT hFB hST hSB hparts

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, where the middle tridiagonal-solve budget is
discharged by Chapter 9's column-dominant tridiagonal LU growth theorem and
the final scalar coefficient is supplied as one direct sum inequality. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_colDiagDom_middle_coeff
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT hγ_factor hn hκL hκLhat hκT hκBT
      hLU hdetT hT_tridiag hColDom hL_norm hLT_norm hLhat_norm
      hLhatT_norm hT_norm hBT_norm hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, where the middle tridiagonal-solve budget is
discharged by Chapter 9's row-dominant tridiagonal LU growth theorem and the
final scalar coefficient is supplied as one direct sum inequality. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_norm_budget
    fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor γ15n25 hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
  exact
    higham11_8_aasen_factor_solve_norm_budget_of_rowDiagDom_middle_coeff
      fp n L T L_hat T_hat L_T_hat U_T_hat BT_factor γ_factor γ15n25
      κL κLT κLhat κLhatT κT κBT hγ_factor hn hκL hκLhat hκT hκBT
      hLU hdetT hT_tridiag hRowDom hL_norm hLT_norm hLhat_norm hLhatT_norm
      hT_norm hBT_norm hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from a
supplied relative `L_hat` hypothesis and discharging the middle
tridiagonal-solve budget by Chapter 9's column-dominant LU growth theorem. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT
      (higham9_14_f (gamma fp n) * 3) hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) (by norm_num))
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_colDiagDom_LUFactSpec
        fp n T_hat L_T_hat U_T_hat hn hLU hdetT hT_tridiag hColDom)
      hcoeff

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed normwise predicate, deriving the computed-factor norm bounds from a
supplied relative `L_hat` hypothesis and discharging the middle
tridiagonal-solve budget by Chapter 9's row-dominant LU growth theorem. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT
      (higham9_14_f (gamma fp n) * 3) hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) (by norm_num))
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_rowDiagDom_LUFactSpec
        fp n T_hat L_T_hat U_T_hat hn hLU hdetT hT_tridiag hRowDom)
      hcoeff

/-- Relative column-dominant wrapper variant where the factorization-side
`BT_factor` norm bound is derived from a componentwise bound against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_colDiagDom_middle_coeff
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT hγ_factor hκL hκT hκBT
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hLU hdetT
      hT_tridiag hColDom hL_norm hLT_norm hT_norm hBT_norm hcoeff

/-- Relative row-dominant wrapper variant where the factorization-side
`BT_factor` norm bound is derived from a componentwise bound against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_rowDiagDom_middle_coeff
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT hγ_factor hκL hκT hκBT
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hLU hdetT
      hT_tridiag hRowDom hL_norm hLT_norm hT_norm hBT_norm hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates, and the middle tridiagonal-solve budget is
discharged by Chapter 9's column-dominant tridiagonal LU growth theorem. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB hγ_factor hκL hκLhat hκT hκBT hBT_factor h20
      hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn
      hprod hLhat_entry hThat hLU hdetT hT_tridiag hColDom hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_norm hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates, and the middle tridiagonal-solve budget is
discharged by Chapter 9's row-dominant tridiagonal LU growth theorem. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      ηFT ηFB ηST ηSB hγ_factor hκL hκLhat hκT hκBT hBT_factor h20
      hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn
      hprod hLhat_entry hThat hLU hdetT hT_tridiag hRowDom hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_norm hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates, the middle tridiagonal-solve budget is
discharged by Chapter 9's column-dominant tridiagonal LU growth theorem, and
the final scalar coefficient is supplied as one direct sum inequality. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_colDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_colDiagDom_middle_coeff
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT hγ_factor
      hκL hκLhat hκT hκBT hBT_factor h20 hLhat_diag hLhat_lower
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
      hLU hdetT hT_tridiag hColDom hL_norm hLT_norm hLhat_norm hLhatT_norm
      hT_norm hBT_norm hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates, the middle tridiagonal-solve budget is
discharged by Chapter 9's row-dominant tridiagonal LU growth theorem, and the
final scalar coefficient is supplied as one direct sum inequality. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_rowDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * 3) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_rowDiagDom_middle_coeff
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT hγ_factor
      hκL hκLhat hκT hκBT hBT_factor h20 hLhat_diag hLhat_lower
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
      hLU hdetT hT_tridiag hRowDom hL_norm hLT_norm hLhat_norm hLhatT_norm
      hT_norm hBT_norm hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates and the scalar norm budget is discharged
from primitive factor norm bounds. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * κmid * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid hγ_factor hκL
      hκLhat hκT hκBT hκmid hBT_factor h20 hLhat_diag hLhat_lower
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
      hL_norm hLT_norm hLhat_norm hLhatT_norm hT_norm hBT_norm hmiddle_norm
      hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, deriving the relative `L_hat` entrywise hypothesis from the modeled
rounded recurrence updates and deriving the computed-factor norm bounds from
that relative hypothesis. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * κmid * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor γ15n25 κL κLT κT κBT κmid hγ_factor hκL hκT hκBT
      hκmid hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hT_norm hBT_norm hmiddle_norm hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, deriving the relative `L_hat` entrywise hypothesis from the modeled
rounded recurrence updates and accepting the printed coefficient as four
gamma-share obligations. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds_gamma_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmid γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * κmid * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_factor_norm_bounds_gamma_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor γ15n25 κL κLT κT κBT κmid γFT γFB γST γSB hγ_factor
      hκL hκT hκBT hκmid hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag
      hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm
      hLT_norm hT_norm hBT_norm hmiddle_norm hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, deriving the computed-factor norm bounds from the generated
relative `L_hat` hypothesis and discharging the middle tridiagonal-solve norm
budget from a relative bound on the tridiagonal LU factor product. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT
      (higham9_14_f (gamma fp n) * κmidLU) hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
      hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
      hL_norm hLT_norm hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
        fp n hn_pos L_T_hat U_T_hat T_hat κmidLU hn hmiddle_factors)
      hcoeff

/-- Source-prefix relative middle-factor-product wrapper variant where the
factorization-side `BT_factor` norm bound is derived from a componentwise bound
against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT κmidLU hγ_factor hκL
      hκT hκBT hκmidLU hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
      hL_norm hLT_norm hT_norm hBT_norm hmiddle_factors hcoeff

/-- Source-prefix relative middle-factor-product wrapper with the concrete
factorization-side `T_hat` budget `|T_hat - T| ≤ κBT |T_hat|`, instantiating
`BT_factor`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_T_factor
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_middle_factor_product_bound_componentwise_BT
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat
      (fun i j => κBT * |T_hat i j|) b DeltaT_LU γ_factor γ15n25 κL
      κLT κT κBT κmidLU hγ_factor hκL hκT hκBT hκmidLU
      (by
        intro i j
        exact mul_nonneg hκBT (abs_nonneg _))
      hrec hHnz hvalSum hvalUpdate hLhat_update hLhat_fixed_successor
      hLhat_fixed_other hbudget_rel h20 hLhat_diag hLhat_lower hT_L_diag
      hT_U_diag hT_L_lower hT_U_upper hn hprod hThat_component hL_norm
      hLT_norm hT_norm (fun i j => le_rfl) hmiddle_factors hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, deriving the computed-factor norm bounds from the generated
relative `L_hat` hypothesis and discharging the middle tridiagonal-solve
budget from an absolute LU product norm bound. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_norm_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (habs :
      infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) ≤
        κmidLU * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_norm_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB hγ_factor hκL hκT hκBT hκmidLU hBT_factor
      h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower
      hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm hT_norm
      hBT_norm habs hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper with generated relative `L_hat` bounds
and a componentwise absolute LU product bound for the middle tridiagonal solve. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hentry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT κmidLU ηFT ηFB
      ηST ηSB hγ_factor hκL hκT hκBT hκmidLU hBT_factor h20
      hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper
      hn hprod hLhat_entry hThat hL_norm hLT_norm hT_norm hBT_norm hentry
      hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper with generated relative `L_hat` bounds
while deriving both `BT_factor` and abs-LU middle norms from componentwise
comparisons against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_componentwise_BT_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_componentwise_BT_absLU_componentwise_T_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT κmidLU ηFT ηFB
      ηST ηSB hγ_factor hκL hκT hκBT hκmidLU hBT_factor h20
      hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper
      hn hprod hLhat_entry hThat hL_norm hLT_norm hT_norm hBT_component
      hmiddle_entry hFT hFB hST hSB hparts

/-- Source-prefix relative abs-LU componentwise-middle wrapper with the
concrete factorization-side `T_hat` budget `|T_hat - T| ≤ κBT |T_hat|`,
instantiating `BT_factor`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_componentwise_BT_absLU_componentwise_T_coeff_parts
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat
      (fun i j => κBT * |T_hat i j|) b DeltaT_LU γ_factor γ15n25 κL
      κLT κT κBT κmidLU ηFT ηFB ηST ηSB hγ_factor hκL hκT hκBT
      hκmidLU
      (by
        intro i j
        exact mul_nonneg hκBT (abs_nonneg _))
      hrec hHnz hvalSum hvalUpdate hLhat_update hLhat_fixed_successor
      hLhat_fixed_other hbudget_rel h20 hLhat_diag hLhat_lower hT_L_diag
      hT_U_diag hT_L_lower hT_U_upper hn hprod hThat_component hL_norm
      hLT_norm hT_norm (fun i j => le_rfl) hmiddle_entry hFT hFB hST hSB hparts

/-- Source-prefix relative abs-LU componentwise-middle wrapper with the
concrete factorization-side `T_hat` budget, using four shares of the printed
`(n-1)^2 γ_{15n+25}` coefficient. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_gamma_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT κmidLU
      γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  let α : ℝ := ((n - 1 : ℕ) : ℝ) ^ 2
  have hα : 0 ≤ α := by
    dsimp [α]
    exact sq_nonneg _
  have hparts' : α * γFT + α * γFB + α * γST + α * γSB ≤ α * γ15n25 := by
    calc
      α * γFT + α * γFB + α * γST + α * γSB
          = α * (γFT + γFB + γST + γSB) := by ring
      _ ≤ α * γ15n25 := mul_le_mul_of_nonneg_left hparts hα
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_coeff_parts
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ15n25 κL κLT κT κBT κmidLU (α * γFT) (α * γFB)
      (α * γST) (α * γSB) hγ_factor hκL hκT hκBT hκmidLU hrec hHnz
      hvalSum hvalUpdate hLhat_update hLhat_fixed_successor hLhat_fixed_other
      hbudget_rel h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hThat_component hL_norm hLT_norm
      hT_norm hmiddle_entry (by simpa [α] using hFT)
      (by simpa [α] using hFB) (by simpa [α] using hST)
      (by simpa [α] using hSB) (by simpa [α] using hparts')

/-- Source-prefix relative abs-LU componentwise-middle wrapper with the
concrete factorization-side `T_hat` budget, where the four coefficient shares
are discharged from product caps and larger gamma radii. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU
      ρFT ρFB ρST ρSB γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hρFT : κL * κT * κLT ≤ ρFT)
    (hρFB : κL * κBT * κLT ≤ ρFB)
    (hρST :
      ((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT) ≤ ρST)
    (hρSB :
      ((1 + γ_factor) * κL) * (higham9_14_f γ_mid_cap * κmidLU) *
          ((1 + γ_factor) * κLT) ≤ ρSB)
    (hFT :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU ρFT ρFB ρST ρSB γFT γFB γST γSB
      hγ_factor hγ_factor_le hγ_solve_le hγ_mid_le hκL hκT hκBT
      hκmidLU h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower
      hT_U_upper hn hprod hLhat_entry hThat_component hL_norm hLT_norm
      hT_norm hmiddle_entry hρFT hρFB hρST hρSB hFT hFB hST hSB hparts

/-- Source-prefix relative abs-LU componentwise-middle wrapper with the
concrete factorization-side `T_hat` budget, discharging the final coefficient
from one aggregate product-cap/gamma-majorant inequality. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_product_majorants_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU ρFT ρFB ρST ρSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hρFT : κL * κT * κLT ≤ ρFT)
    (hρFB : κL * κBT * κLT ≤ ρFB)
    (hρST :
      ((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT) ≤ ρST)
    (hρSB :
      ((1 + γ_factor) * κL) * (higham9_14_f γ_mid_cap * κmidLU) *
          ((1 + γ_factor) * κLT) ≤ ρSB)
    (hcoeff :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFT +
        (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * ρFB +
        (2 * γ_solve_cap + γ_solve_cap ^ 2) * ρST +
        (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) * ρSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_product_majorants_coeff
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU ρFT ρFB ρST ρSB hγ_factor hγ_factor_le
      hγ_solve_le hγ_mid_le hκL hκT hκBT hκmidLU h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod
      hLhat_entry hThat_component hL_norm hLT_norm hT_norm hmiddle_entry
      hρFT hρFB hρST hρSB hcoeff

/-- Source-prefix relative abs-LU componentwise-middle wrapper with the
concrete factorization-side `T_hat` budget and exact product majorants,
leaving only one aggregate printed-coefficient comparison. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hcoeff :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κBT * κLT) +
        (2 * γ_solve_cap + γ_solve_cap ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) *
          (((1 + γ_factor) * κL) *
            (higham9_14_f γ_mid_cap * κmidLU) *
            ((1 + γ_factor) * κLT)) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU hγ_factor hγ_factor_le hγ_solve_le hγ_mid_le
      hκL hκT hκBT hκmidLU h20 hLhat_diag hLhat_lower hT_L_diag
      hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat_component
      hL_norm hLT_norm hT_norm hmiddle_entry hcoeff

/-- Source-prefix relative abs-LU componentwise-middle wrapper with the
concrete factorization-side `T_hat` budget and exact product majorants, using
four shares of the printed coefficient. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU γFT γFB γST γSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hγ_factor_le : γ_factor ≤ γ_factor_cap)
    (hγ_solve_le : gamma fp n ≤ γ_solve_cap)
    (hγ_mid_le : gamma fp n ≤ γ_mid_cap)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat_component : ∀ i j : Fin n, |T_hat i j - T i j| ≤ κBT * |T_hat i j|)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFT)
    (hFB :
      (1 + 2 * γ_factor_cap + γ_factor_cap ^ 2) * (κL * κBT * κLT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γFB)
    (hST :
      (2 * γ_solve_cap + γ_solve_cap ^ 2) *
        (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γST)
    (hSB :
      (1 + 2 * γ_solve_cap + γ_solve_cap ^ 2) *
        (((1 + γ_factor) * κL) *
          (higham9_14_f γ_mid_cap * κmidLU) *
          ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γSB)
    (hparts : γFT + γFB + γST + γSB ≤ γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_factor : Fin n → Fin n → ℝ := fun i j => κBT * |T_hat i j|
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_relative_absLU_componentwise_T_factor_concrete_product_majorants_gamma_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat b DeltaT_LU
      γ_factor γ_factor_cap γ_solve_cap γ_mid_cap γ15n25
      κL κLT κT κBT κmidLU γFT γFB γST γSB
      hγ_factor hγ_factor_le hγ_solve_le hγ_mid_le hκL hκT hκBT
      hκmidLU h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower
      hT_U_upper hn hprod hLhat_entry hThat_component hL_norm hLT_norm
      hT_norm hmiddle_entry hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, deriving the computed-factor norm bounds from the generated
relative `L_hat` hypothesis and discharging the middle tridiagonal-solve norm
budget by Chapter 9's column-dominant LU growth theorem. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT
      (higham9_14_f (gamma fp n) * 3) hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) (by norm_num))
      hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
      hL_norm hLT_norm hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_colDiagDom_LUFactSpec
        fp n T_hat L_T_hat U_T_hat hn hLU hdetT hT_tridiag hColDom)
      hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, deriving the computed-factor norm bounds from the generated
relative `L_hat` hypothesis and discharging the middle tridiagonal-solve norm
budget by Chapter 9's row-dominant LU growth theorem. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_factor_norm_bounds
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT
      (higham9_14_f (gamma fp n) * 3) hγ_factor hκL hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) (by norm_num))
      hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
      hL_norm hLT_norm hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_rowDiagDom_LUFactSpec
        fp n T_hat L_T_hat U_T_hat hn hLU hdetT hT_tridiag hRowDom)
      hcoeff

/-- Source-prefix relative column-dominant wrapper variant where the
factorization-side `BT_factor` norm bound is derived from a componentwise
bound against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hColDom : IsDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_colDiagDom_middle_coeff
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT hγ_factor hκL hκT hκBT
      hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
      hLU hdetT hT_tridiag hColDom hL_norm hLT_norm hT_norm hBT_norm hcoeff

/-- Source-prefix relative row-dominant wrapper variant where the
factorization-side `BT_factor` norm bound is derived from a componentwise
bound against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κT κBT : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hLU : LUFactSpec n T_hat L_T_hat U_T_hat)
    (hdetT : Matrix.det (Matrix.of T_hat : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hT_tridiag : IsTridiagonal n T_hat)
    (hRowDom : IsRowDiagDominant n T_hat)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * ((1 + γ_factor) * κLT)) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (((1 + γ_factor) * κL) * (higham9_14_f (gamma fp n) * 3) *
            ((1 + γ_factor) * κLT)) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat := by
    apply higham11_8_infNorm_le_mul_of_componentwise_T_bound n BT_factor T_hat κBT hκBT
    intro i j
    rw [abs_of_nonneg (hBT_factor i j)]
    exact hBT_component i j
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_relative_rowDiagDom_middle_coeff
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κT κBT hγ_factor hκL hκT hκBT
      hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
      hLU hdetT hT_tridiag hRowDom hL_norm hLT_norm hT_norm hBT_norm hcoeff

/-- Source-prefix factor-norm wrapper variant where the relative `L_hat`
factor hypothesis is generated from modeled rounded recurrence updates and the
factorization-side `BT_factor` norm bound is derived from a componentwise bound
against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds_componentwise_BT
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmid : 0 ≤ κmid)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_norm :
      infNorm (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat) ≤
        κmid * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * κmid * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_factor_norm_bounds_componentwise_BT
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmid hγ_factor hκL
      hκLhat hκT hκBT hκmid hBT_factor h20 hLhat_diag hLhat_lower
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat_entry hThat
      hL_norm hLT_norm hLhat_norm hLhatT_norm hT_norm hBT_component
      hmiddle_norm hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates and the middle tridiagonal-solve norm
budget is discharged from a relative bound on the tridiagonal LU factor
product. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_middle_factor_product_bound
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hmiddle_factors :
      infNorm L_T_hat * infNorm U_T_hat ≤ κmidLU * infNorm T_hat)
    (hcoeff :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) +
        (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) +
        (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) +
        (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
          (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_factor_norm_bounds
      fp n hn_pos A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT
      (higham9_14_f (gamma fp n) * κmidLU)
      hγ_factor hκL hκLhat hκT hκBT
      (mul_nonneg (higham9_14_f_nonneg (gamma_nonneg fp hn)) hκmidLU)
      hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
      hL_norm hLT_norm hLhat_norm hLhatT_norm hT_norm hBT_norm
      (higham11_15_aasenMiddleSolveBudget_infNorm_le_of_factor_product_bound
        fp n hn_pos L_T_hat U_T_hat T_hat κmidLU hn hmiddle_factors)
      hcoeff

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates and the middle tridiagonal-solve budget is
discharged from an absolute LU product norm bound. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_norm_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (habs :
      infNorm (matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat)) ≤
        κmidLU * infNorm T_hat)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_norm_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB hγ_factor hκL hκLhat hκT hκBT hκmidLU
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_norm habs hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the relative `L_hat` factor hypothesis is generated from the
modeled rounded recurrence updates and the middle tridiagonal-solve budget is
discharged from a componentwise absolute LU product bound. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_norm : infNorm BT_factor ≤ κBT * infNorm T_hat)
    (hentry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_absLU_componentwise_T_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB hγ_factor hκL hκLhat hκT hκBT hκmidLU
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_norm hentry hFT hFB hST hSB hparts

/-- Source-prefix rounded Aasen wrapper where the relative `L_hat` factor
hypothesis is generated from modeled rounded recurrence updates, while both the
factorization-side `BT_factor` norm and middle tridiagonal-solve norm are
derived from componentwise bounds against `T_hat`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_componentwise_BT_absLU_componentwise_T_coeff_parts
    (fp : FPModel) (n : ℕ) (hn_pos : 0 < n)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB : ℝ)
    (hγ_factor : 0 ≤ γ_factor)
    (hκL : 0 ≤ κL) (hκLhat : 0 ≤ κLhat)
    (hκT : 0 ≤ κT) (hκBT : 0 ≤ κBT) (hκmidLU : 0 ≤ κmidLU)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hL_norm : infNorm L ≤ κL)
    (hLT_norm : infNorm (fun r c => L c r) ≤ κLT)
    (hLhat_norm : infNorm L_hat ≤ κLhat)
    (hLhatT_norm : infNorm (fun r c => L_hat c r) ≤ κLhatT)
    (hT_norm : infNorm T ≤ κT * infNorm T_hat)
    (hBT_component : ∀ i j : Fin n, BT_factor i j ≤ κBT * |T_hat i j|)
    (hmiddle_entry : ∀ i j : Fin n,
      matMul n (absMatrix n L_T_hat) (absMatrix n U_T_hat) i j ≤
        κmidLU * |T_hat i j|)
    (hFT :
      (2 * γ_factor + γ_factor ^ 2) * (κL * κT * κLT) ≤ ηFT)
    (hFB :
      (1 + 2 * γ_factor + γ_factor ^ 2) * (κL * κBT * κLT) ≤ ηFB)
    (hST :
      (2 * gamma fp n + (gamma fp n) ^ 2) * (κLhat * κLhatT) ≤ ηST)
    (hSB :
      (1 + 2 * gamma fp n + (gamma fp n) ^ 2) *
        (κLhat * (higham9_14_f (gamma fp n) * κmidLU) * κLhatT) ≤ ηSB)
    (hparts : ηFT + ηFB + ηST + ηSB ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  have hLhat_entry : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j| :=
    higham11_14_fl_aasen_source_prefix_Lhat_global_relative_bound_of_exact_recurrence
      n fp A L H L_hat hrec hHnz hvalSum hvalUpdate γ_factor hγ_factor
      hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
  exact
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_componentwise_BT_absLU_componentwise_T_coeff_parts
      fp n hn_pos A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor
      b DeltaT_LU γ_factor γ15n25 κL κLT κLhat κLhatT κT κBT κmidLU
      ηFT ηFB ηST ηSB hγ_factor hκL hκLhat hκT hκBT hκmidLU
      hBT_factor h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag
      hT_L_lower hT_U_upper hn hprod hLhat_entry hThat hL_norm hLT_norm
      hLhat_norm hLhatT_norm hT_norm hBT_component hmiddle_entry
      hFT hFB hST hSB hparts

/-- Rounded Aasen solve-chain source equation plus the printed Theorem 11.8
normwise shape, under an explicit comparison from the closed chain budget to
`η |T_hat|`.  This packages the solve-chain part of the Aasen stability proof;
the remaining global task is to prove the factorization/recurrence comparison
that supplies `hchain_le` with the printed scalar `γ_{15n+25}` budget. -/
theorem higham11_8_fl_aasen_solve_chain_source_normwise_backward_error
    (fp : FPModel) (n : ℕ)
    (A Pmat L T L_T_hat U_T_hat T_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (η γ15n25 : ℝ) (hη : 0 ≤ η)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hL_lower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hchain_le : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n (gamma fp n)
        (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
        L T (fun r c => L c r) i j ≤ η * |T_hat i j|)
    (hbudget : η * infNorm T_hat ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25 * infNorm T_hat) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let bound := higham11_15_aasenChainDeltaABound n (gamma fp n) BT L T U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ bound i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat BT bound
  obtain ⟨DeltaA, hDelta, hsource⟩ :=
    higham11_15_fl_aasen_solve_chain_source_backward_error
      fp n A Pmat L T L_T_hat U_T_hat b DeltaT_LU h20
      hL_diag hL_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod
  refine ⟨DeltaA, hDelta, hsource, ?_⟩
  exact higham11_8_aasenNormwiseBackwardBound_of_aasenChainDeltaABound
    n DeltaA L T U_outer BT T_hat (gamma fp n) η γ15n25 hη hDelta
    (by
      intro i j
      simpa [BT, U_outer] using hchain_le i j)
    hbudget

/-- Rounded Aasen factorization-plus-solve source backward error together
with the printed Theorem 11.8 normwise predicate, under an explicit comparison
from the summed factorization and solve-chain budgets to `η |T_hat|`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error
    (fp : FPModel) (n : ℕ)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor η γ15n25 : ℝ) (hγ_factor : 0 ≤ γ_factor) (hη : 0 ≤ η)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hbudget_entry : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r) i j +
        higham11_15_aasenChainDeltaABound n (gamma fp n)
          (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
          L_hat T_hat (fun r c => L_hat c r) i j ≤
        η * |T_hat i j|)
    (hη_le : η ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat BT_solve B_factor B_solve
  obtain ⟨DeltaA, hDeltaA, hsource⟩ :=
    higham11_8_fl_aasen_factor_solve_source_backward_error
      fp n A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor hγ_factor hBT_factor h20 hLhat_diag hLhat_lower
      hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat hThat
  refine ⟨DeltaA, hDeltaA, hsource, ?_⟩
  apply higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound
    n DeltaA T_hat η γ15n25 hη
  · intro i j
    have hentry :
        B_factor i j + B_solve i j ≤ η * |T_hat i j| := by
      simpa [B_factor, B_solve, BT_solve, U_outer] using hbudget_entry i j
    exact (hDeltaA i j).trans hentry
  · simpa [mul_assoc] using
      mul_le_mul_of_nonneg_right hη_le (infNorm_nonneg T_hat)

/-- Rounded Aasen factorization-plus-solve source backward error with the
printed Theorem 11.8 normwise predicate, where the remaining entrywise
`η |T_hat|` comparison is supplied as separate factorization and solve-chain
pieces. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_split_entry_budgets
    (fp : FPModel) (n : ℕ)
    (A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor η_factor η_solve η γ15n25 : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hη : 0 ≤ η)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hLhat : ∀ i j : Fin n, |L_hat i j - L i j| ≤ γ_factor * |L i j|)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hbudget_factor : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T
          (fun r c => L c r) i j ≤
        η_factor * |T_hat i j|)
    (hbudget_solve : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n (gamma fp n)
          (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
          L_hat T_hat (fun r c => L_hat c r) i j ≤
        η_solve * |T_hat i j|)
    (hη_parts : η_factor + η_solve ≤ η)
    (hη_le : η ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply higham11_8_fl_aasen_factor_solve_source_normwise_backward_error
    fp n A Pmat L T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
    γ_factor η γ15n25 hγ_factor hη hBT_factor h20 hLhat_diag hLhat_lower
    hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hLhat hThat
  · exact
      higham11_8_componentwise_T_bound_add_of_parts n
        (higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T
          (fun r c => L c r))
        (higham11_15_aasenChainDeltaABound n (gamma fp n)
          (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
          L_hat T_hat (fun r c => L_hat c r))
        T_hat η_factor η_solve η hbudget_factor hbudget_solve hη_parts
  · exact hη_le

/-- Rounded Aasen source-prefix recurrence wrapper plus the printed Theorem
11.8 normwise predicate.  This is the normwise sibling of
`higham11_8_fl_aasen_factor_solve_source_backward_error_of_source_prefix_updates`:
the source equation is generated from the modeled source-prefix updates, and
the remaining open scalar obligation is the explicit comparison from the
summed closed budgets to `η |T_hat|`. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_updates
    (fp : FPModel) (n : ℕ)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor η γ15n25 : ℝ) (hγ_factor : 0 ≤ γ_factor) (hη : 0 ≤ η)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hbudget_entry : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r) i j +
        higham11_15_aasenChainDeltaABound n (gamma fp n)
          (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
          L_hat T_hat (fun r c => L_hat c r) i j ≤
        η * |T_hat i j|)
    (hη_le : η ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  intro rhs z_hat q_hat y_hat U_outer w_hat BT_solve B_factor B_solve
  obtain ⟨DeltaA, hDeltaA, hsource⟩ :=
    higham11_8_fl_aasen_factor_solve_source_backward_error_of_source_prefix_updates
      fp n A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor hγ_factor hBT_factor hrec hHnz hvalSum hvalUpdate hLhat_update
      hLhat_fixed_successor hLhat_fixed_other hbudget_rel h20 hLhat_diag
      hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper hn hprod hThat
  refine ⟨DeltaA, hDeltaA, hsource, ?_⟩
  apply higham11_8_aasenNormwiseBackwardBound_of_componentwise_T_bound
    n DeltaA T_hat η γ15n25 hη
  · intro i j
    have hentry :
        B_factor i j + B_solve i j ≤ η * |T_hat i j| := by
      simpa [B_factor, B_solve, BT_solve, U_outer] using hbudget_entry i j
    exact (hDeltaA i j).trans hentry
  · simpa [mul_assoc] using
      mul_le_mul_of_nonneg_right hη_le (infNorm_nonneg T_hat)

/-- Source-prefix rounded Aasen wrapper with the printed Theorem 11.8 normwise
predicate, where the remaining `η |T_hat|` comparison is supplied as separate
factorization and solve-chain entrywise budgets. -/
theorem higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_split_entry_budgets
    (fp : FPModel) (n : ℕ)
    (A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor :
      Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (DeltaT_LU : Fin n → Fin n → ℝ)
    (γ_factor η_factor η_solve η γ15n25 : ℝ)
    (hγ_factor : 0 ≤ γ_factor) (hη : 0 ≤ η)
    (hBT_factor : ∀ i j : Fin n, 0 ≤ BT_factor i j)
    (hrec : higham11_14_aasenNextColumnEquation n A L H)
    (hHnz : ∀ i next : Fin n, next.val = i.val + 1 → H next i ≠ 0)
    (hvalSum : ∀ i next : Fin n, next.val = i.val + 1 →
      gammaValid fp next.val)
    (hvalUpdate : gammaValid fp 2)
    (hLhat_update : ∀ i next k : Fin n, next.val = i.val + 1 →
      i.val + 2 ≤ k.val →
      L_hat k next =
        fp.fl_div
          (fp.fl_sub (A k i)
            (higham11_14_fl_aasenSourcePrefixDot n fp L H i next k))
          (H next i))
    (hLhat_fixed_successor : ∀ i next k : Fin n, next.val = i.val + 1 →
      ¬ i.val + 2 ≤ k.val → L_hat k next = L k next)
    (hLhat_fixed_other : ∀ k j : Fin n,
      (∀ i : Fin n, j.val ≠ i.val + 1) → L_hat k j = L k j)
    (hbudget_rel : ∀ i next : Fin n, next.val = i.val + 1 →
      ∀ k : Fin n, i.val + 2 ≤ k.val →
      let Bsum : ℝ :=
        gamma fp next.val *
          ∑ j : Fin next.val,
            |L k ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩| *
              |H ⟨j.val, Nat.lt_trans j.isLt next.isLt⟩ i|
      Bsum / |H next i| +
          gamma fp 2 * (|L k next| + Bsum / |H next i|)
        ≤ γ_factor * |L k next|)
    (h20 : higham9_20_tridiag_lu_perturbation_model n T_hat L_T_hat U_T_hat
      DeltaT_LU (gamma fp n))
    (hLhat_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hLhat_lower : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hT_L_diag : ∀ i : Fin n, L_T_hat i i ≠ 0)
    (hT_U_diag : ∀ i : Fin n, U_T_hat i i ≠ 0)
    (hT_L_lower : ∀ i j : Fin n, i.val < j.val → L_T_hat i j = 0)
    (hT_U_upper : ∀ i j : Fin n, j.val < i.val → U_T_hat i j = 0)
    (hn : gammaValid fp n)
    (hprod : ∀ i j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, L i p * T p q * L j q) = A i j)
    (hThat : ∀ i j : Fin n, |T_hat i j - T i j| ≤ BT_factor i j)
    (hbudget_factor : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T
          (fun r c => L c r) i j ≤
        η_factor * |T_hat i j|)
    (hbudget_solve : ∀ i j : Fin n,
      higham11_15_aasenChainDeltaABound n (gamma fp n)
          (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
          L_hat T_hat (fun r c => L_hat c r) i j ≤
        η_solve * |T_hat i j|)
    (hη_parts : η_factor + η_solve ≤ η)
    (hη_le : η ≤ ((n - 1 : ℕ) : ℝ) ^ 2 * γ15n25) :
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z_hat := fl_forwardSub fp n L_hat rhs
    let q_hat := fl_forwardSub fp n L_T_hat z_hat
    let y_hat := fl_backSub fp n U_T_hat q_hat
    let U_outer : Fin n → Fin n → ℝ := fun i j => L_hat j i
    let w_hat := fl_backSub fp n U_outer y_hat
    let BT_solve := higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat
    let B_factor :=
      higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T (fun r c => L c r)
    let B_solve :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT_solve L_hat T_hat U_outer
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ B_factor i j + B_solve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w_hat j = rhs i) ∧
      higham11_8_aasenNormwiseBackwardBound n (infNorm DeltaA) γ15n25
        (infNorm T_hat) := by
  apply
    higham11_8_fl_aasen_factor_solve_source_normwise_backward_error_of_source_prefix_updates
      fp n A Pmat L H T L_hat T_hat L_T_hat U_T_hat BT_factor b DeltaT_LU
      γ_factor η γ15n25 hγ_factor hη hBT_factor hrec hHnz hvalSum
      hvalUpdate hLhat_update hLhat_fixed_successor hLhat_fixed_other hbudget_rel
      h20 hLhat_diag hLhat_lower hT_L_diag hT_U_diag hT_L_lower hT_U_upper
      hn hprod hThat
  · exact
      higham11_8_componentwise_T_bound_add_of_parts n
        (higham11_15_aasenChainDeltaABound n γ_factor BT_factor L T
          (fun r c => L c r))
        (higham11_15_aasenChainDeltaABound n (gamma fp n)
          (higham11_15_aasenMiddleSolveBudget fp n L_T_hat U_T_hat)
          L_hat T_hat (fun r c => L_hat c r))
        T_hat η_factor η_solve η hbudget_factor hbudget_solve hη_parts
  · exact hη_le

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
