-- Analysis/FiniteProbability.lean
--
-- Lightweight finite probability spaces and elementary concentration kernels.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LeanFpAnalysis.FP

open scoped BigOperators

/-!
## Finite probability spaces

This file provides a small real-valued finite probability interface and the
elementary Markov, Chebyshev, and Chernoff kernels used by algorithm-specific
randomized stability analyses.
-/

/-- A lightweight finite probability space, represented by a real mass function
    over a finite type. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : ∑ ω, prob ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event in a finite probability space. -/
noncomputable def eventProb (P : FiniteProbability Ω) (E : Set Ω) : ℝ :=
  by
    classical
    exact ∑ ω, if ω ∈ E then P.prob ω else 0

/-- Expectation of a natural-valued random variable, coerced to `ℝ`. -/
noncomputable def expectationNat (P : FiniteProbability Ω) (X : Ω → ℕ) : ℝ :=
  ∑ ω, P.prob ω * (X ω : ℝ)

/-- Expectation of a real-valued random variable. -/
noncomputable def expectationReal (P : FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.prob ω * X ω

theorem expectationReal_sum {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (X : ι → Ω → ℝ) :
    P.expectationReal (fun ω => ∑ i, X i ω) =
      ∑ i, P.expectationReal (fun ω => X i ω) := by
  classical
  unfold expectationReal
  calc
    ∑ ω, P.prob ω * (∑ i, X i ω)
        = ∑ ω, ∑ i, P.prob ω * X i ω := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ ω, P.prob ω * X i ω := by
            rw [Finset.sum_comm]

theorem expectationReal_const (P : FiniteProbability Ω) (c : ℝ) :
    P.expectationReal (fun _ => c) = c := by
  classical
  unfold expectationReal
  calc
    ∑ ω, P.prob ω * c = (∑ ω, P.prob ω) * c := by
        rw [Finset.sum_mul]
    _ = c := by
        rw [P.prob_sum]
        ring

theorem expectationReal_add (P : FiniteProbability Ω) (X Y : Ω → ℝ) :
    P.expectationReal (fun ω => X ω + Y ω) =
      P.expectationReal X + P.expectationReal Y := by
  classical
  unfold expectationReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expectationReal_sub (P : FiniteProbability Ω) (X Y : Ω → ℝ) :
    P.expectationReal (fun ω => X ω - Y ω) =
      P.expectationReal X - P.expectationReal Y := by
  classical
  unfold expectationReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expectationReal_mul_const (P : FiniteProbability Ω) (X : Ω → ℝ) (c : ℝ) :
    P.expectationReal (fun ω => X ω * c) = P.expectationReal X * c := by
  classical
  unfold expectationReal
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expectationReal_const_mul (P : FiniteProbability Ω) (X : Ω → ℝ) (c : ℝ) :
    P.expectationReal (fun ω => c * X ω) = c * P.expectationReal X := by
  classical
  unfold expectationReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem eventProb_nonneg (P : FiniteProbability Ω) (E : Set Ω) :
    0 ≤ P.eventProb E := by
  classical
  unfold eventProb
  exact Finset.sum_nonneg fun ω _ => by
    by_cases hω : ω ∈ E
    · simp [hω, P.prob_nonneg ω]
    · simp [hω]

theorem eventProb_mono (P : FiniteProbability Ω) {E F : Set Ω}
    (hEF : E ⊆ F) :
    P.eventProb E ≤ P.eventProb F := by
  classical
  unfold eventProb
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : ω ∈ E
  · have hF : ω ∈ F := hEF hE
    simp [hE, hF]
  · by_cases hF : ω ∈ F
    · simp [hE, hF, P.prob_nonneg ω]
    · simp [hE, hF]

theorem eventProb_add_eventProb_compl (P : FiniteProbability Ω) (E : Set Ω) :
    P.eventProb E + P.eventProb Eᶜ = 1 := by
  classical
  unfold eventProb
  rw [← Finset.sum_add_distrib]
  rw [← P.prob_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ E <;> simp [hω]

/-- Finite Markov inequality for natural-valued random variables. -/
theorem eventProb_nat_ge_le_expectationNat_div
    (P : FiniteProbability Ω) (X : Ω → ℕ) {T : ℕ} (hT : 0 < T) :
    P.eventProb {ω | T ≤ X ω} ≤ P.expectationNat X / (T : ℝ) := by
  classical
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  let M : ℝ := ∑ ω, P.prob ω * ((X ω : ℝ) / (T : ℝ))
  have hle : P.eventProb {ω | T ≤ X ω} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | T ≤ X ω}
    · have hXT : (T : ℝ) ≤ X ω := by exact_mod_cast hω
      have hone : 1 ≤ (X ω : ℝ) / (T : ℝ) := by
        rw [one_le_div hTreal]
        exact hXT
      have hmain :
          P.prob ω ≤ P.prob ω * ((X ω : ℝ) / (T : ℝ)) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω * ((X ω : ℝ) / (T : ℝ)) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hX_nonneg : 0 ≤ (X ω : ℝ) / (T : ℝ) :=
        div_nonneg (by exact_mod_cast Nat.zero_le (X ω)) (le_of_lt hTreal)
      have hmain : 0 ≤ P.prob ω * ((X ω : ℝ) / (T : ℝ)) :=
        mul_nonneg (P.prob_nonneg ω) hX_nonneg
      simpa [hω] using hmain
  have hM : M = P.expectationNat X / (T : ℝ) := by
    unfold M expectationNat
    calc
      ∑ ω, P.prob ω * ((X ω : ℝ) / (T : ℝ))
          = ∑ ω, (P.prob ω * (X ω : ℝ)) * (T : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro ω _
              ring_nf
      _ = (∑ ω, P.prob ω * (X ω : ℝ)) * (T : ℝ)⁻¹ := by
              rw [Finset.sum_mul]
      _ = (∑ ω, P.prob ω * (X ω : ℝ)) / (T : ℝ) := by
              rw [div_eq_mul_inv]
  exact hle.trans_eq hM

/-- Lower-tail form of Markov: with probability at least
    `1 - E[X] / (Q+1)`, a natural-valued random variable is at most `Q`. -/
theorem eventProb_nat_le_ge_one_sub_expectationNat_div_succ
    (P : FiniteProbability Ω) (X : Ω → ℕ) (Q : ℕ) :
    1 - P.expectationNat X / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb {ω | X ω ≤ Q} := by
  classical
  let E : Set Ω := {ω | X ω ≤ Q}
  have hT : 0 < Q + 1 := Nat.succ_pos Q
  have htail :=
    eventProb_nat_ge_le_expectationNat_div P X hT
  have hcompl :
      Eᶜ = {ω | Q + 1 ≤ X ω} := by
    ext ω
    simp [E]
  have htailE :
      P.eventProb Eᶜ ≤ P.expectationNat X / ((Q + 1 : ℕ) : ℝ) := by
    simpa [hcompl] using htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

/-- Chebyshev from finite Markov: the probability of a strict deviation from
    `μ` by more than `ε` is bounded by the centered second moment divided by
    `ε²`. -/
theorem eventProb_abs_sub_gt_le_expectationReal_sq_div
    (P : FiniteProbability Ω) (X : Ω → ℝ) (μ ε : ℝ) (hε : 0 < ε) :
    P.eventProb {ω | ε < |X ω - μ|} ≤
      P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 := by
  classical
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  let M : ℝ := ∑ ω, P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2)
  have hle : P.eventProb {ω | ε < |X ω - μ|} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | ε < |X ω - μ|}
    · have hdev : ε < |X ω - μ| := hω
      have hsq : ε ^ 2 ≤ (X ω - μ) ^ 2 := by
        have hsq_abs : ε ^ 2 ≤ |X ω - μ| ^ 2 := by
          nlinarith [le_of_lt hdev, le_of_lt hε, abs_nonneg (X ω - μ)]
        simpa [sq_abs] using hsq_abs
      have hone : 1 ≤ ((X ω - μ) ^ 2) / ε ^ 2 := by
        rw [one_le_div hε2]
        exact hsq
      have hmain :
          P.prob ω ≤ P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hsq_nonneg : 0 ≤ ((X ω - μ) ^ 2) / ε ^ 2 :=
        div_nonneg (sq_nonneg _) (le_of_lt hε2)
      have hmain :
          0 ≤ P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2) :=
        mul_nonneg (P.prob_nonneg ω) hsq_nonneg
      simpa [hω] using hmain
  have hM : M = P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 := by
    unfold M expectationReal
    calc
      ∑ ω, P.prob ω * (((X ω - μ) ^ 2) / ε ^ 2)
          = ∑ ω, (P.prob ω * ((X ω - μ) ^ 2)) * (ε ^ 2)⁻¹ := by
              apply Finset.sum_congr rfl
              intro ω _
              ring_nf
      _ = (∑ ω, P.prob ω * ((X ω - μ) ^ 2)) * (ε ^ 2)⁻¹ := by
              rw [Finset.sum_mul]
      _ = (∑ ω, P.prob ω * ((X ω - μ) ^ 2)) / ε ^ 2 := by
              rw [div_eq_mul_inv]
  exact hle.trans_eq hM

/-- `1 - δ` Chebyshev form: if the centered second moment divided by `ε²` is
    at most `δ`, then the random variable lies within `ε` of `μ` with
    probability at least `1 - δ`. -/
theorem eventProb_abs_sub_le_ge_one_sub_of_second_moment
    (P : FiniteProbability Ω) (X : Ω → ℝ) (μ ε δ : ℝ) (hε : 0 < ε)
    (hmoment : P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 ≤ δ) :
    1 - δ ≤ P.eventProb {ω | |X ω - μ| ≤ ε} := by
  classical
  let E : Set Ω := {ω | |X ω - μ| ≤ ε}
  have htail :=
    eventProb_abs_sub_gt_le_expectationReal_sq_div P X μ ε hε
  have hcompl :
      Eᶜ = {ω | ε < |X ω - μ|} := by
    ext ω
    simp [E, not_le]
  have htailE :
      P.eventProb Eᶜ ≤
        P.expectationReal (fun ω => (X ω - μ) ^ 2) / ε ^ 2 := by
    simpa [hcompl] using htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

/-- Exponential Markov inequality for natural-valued random variables. This is
    the finite-probability kernel behind the Chernoff upper-tail bound. -/
theorem eventProb_nat_ge_le_exp_mul_mgf
    (P : FiniteProbability Ω) (X : Ω → ℕ) {T : ℕ} {lam : ℝ}
    (hlam : 0 < lam) :
    P.eventProb {ω | T ≤ X ω} ≤
      Real.exp (-(lam * (T : ℝ))) *
        P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) := by
  classical
  let M : ℝ :=
    ∑ ω, P.prob ω * Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ))
  have hle : P.eventProb {ω | T ≤ X ω} ≤ M := by
    unfold eventProb M
    apply Finset.sum_le_sum
    intro ω _
    by_cases hω : ω ∈ {ω | T ≤ X ω}
    · have hXT : (T : ℝ) ≤ X ω := by exact_mod_cast hω
      have hlamT : lam * (T : ℝ) ≤ lam * (X ω : ℝ) :=
        mul_le_mul_of_nonneg_left hXT (le_of_lt hlam)
      have hone :
          1 ≤ Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) := by
        calc
          (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
          _ ≤ Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) :=
              Real.exp_le_exp.mpr (by linarith)
      have hmain :
          P.prob ω ≤
            P.prob ω * Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) := by
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω *
              Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) :=
              mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
      simpa [hω] using hmain
    · have hmain :
          0 ≤ P.prob ω *
            Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) :=
        mul_nonneg (P.prob_nonneg ω)
          (le_of_lt (Real.exp_pos _))
      simpa [hω] using hmain
  have hM :
      M =
        Real.exp (-(lam * (T : ℝ))) *
          P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) := by
    unfold M expectationReal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    have hexp :
        Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ)) =
          Real.exp (-(lam * (T : ℝ))) *
            Real.exp (lam * (X ω : ℝ)) := by
      calc
        Real.exp (lam * (X ω : ℝ) - lam * (T : ℝ))
            = Real.exp (-(lam * (T : ℝ)) + lam * (X ω : ℝ)) := by
                congr 1
                ring
        _ = Real.exp (-(lam * (T : ℝ))) *
            Real.exp (lam * (X ω : ℝ)) := by
                rw [Real.exp_add]
    rw [hexp]
    ring
  exact hle.trans_eq hM

/-- Chernoff upper tail from an exponential-moment bound. If
    `E exp(lamX) ≤ exp(μ(exp lam - 1))`, then
    `Pr(T ≤ X) ≤ exp(μ(exp lam - 1) - lamT)`. -/
theorem eventProb_nat_ge_le_chernoff_of_mgf_bound
    (P : FiniteProbability Ω) (X : Ω → ℕ) {T : ℕ} {lam μ : ℝ}
    (hlam : 0 < lam)
    (hmgf :
      P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) ≤
        Real.exp (μ * (Real.exp lam - 1))) :
    P.eventProb {ω | T ≤ X ω} ≤
      Real.exp (μ * (Real.exp lam - 1) - lam * (T : ℝ)) := by
  have hmarkov := eventProb_nat_ge_le_exp_mul_mgf P X (T := T) hlam
  have hmul :
      Real.exp (-(lam * (T : ℝ))) *
          P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) ≤
        Real.exp (-(lam * (T : ℝ))) *
          Real.exp (μ * (Real.exp lam - 1)) :=
    mul_le_mul_of_nonneg_left hmgf (le_of_lt (Real.exp_pos _))
  have hexp :
      Real.exp (-(lam * (T : ℝ))) *
          Real.exp (μ * (Real.exp lam - 1)) =
        Real.exp (μ * (Real.exp lam - 1) - lam * (T : ℝ)) := by
    calc
      Real.exp (-(lam * (T : ℝ))) *
          Real.exp (μ * (Real.exp lam - 1))
          = Real.exp (-(lam * (T : ℝ)) +
              μ * (Real.exp lam - 1)) := by
              rw [← Real.exp_add]
      _ = Real.exp (μ * (Real.exp lam - 1) - lam * (T : ℝ)) := by
              congr 1
              ring
  exact hmarkov.trans (hmul.trans_eq hexp)

/-- Lower-tail complement form of the Chernoff upper-tail bound. -/
theorem eventProb_nat_le_ge_one_sub_chernoff_of_mgf_bound
    (P : FiniteProbability Ω) (X : Ω → ℕ) (Q : ℕ) {lam μ : ℝ}
    (hlam : 0 < lam)
    (hmgf :
      P.expectationReal (fun ω => Real.exp (lam * (X ω : ℝ))) ≤
        Real.exp (μ * (Real.exp lam - 1))) :
    1 - Real.exp (μ * (Real.exp lam - 1) -
        lam * (((Q + 1 : ℕ) : ℝ))) ≤
      P.eventProb {ω | X ω ≤ Q} := by
  classical
  let E : Set Ω := {ω | X ω ≤ Q}
  have htail :=
    eventProb_nat_ge_le_chernoff_of_mgf_bound P X
      (T := Q + 1) hlam hmgf
  have hcompl :
      Eᶜ = {ω | Q + 1 ≤ X ω} := by
    ext ω
    simp [E]
  have htailE :
      P.eventProb Eᶜ ≤
        Real.exp (μ * (Real.exp lam - 1) -
          lam * (((Q + 1 : ℕ) : ℝ))) := by
    simpa [hcompl] using htail
  have hsplit := eventProb_add_eventProb_compl P E
  linarith

end FiniteProbability

end LeanFpAnalysis.FP
