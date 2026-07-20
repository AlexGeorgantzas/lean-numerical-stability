/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import NumStability.Algorithms.FastMatMul
import NumStability.Algorithms.DotProduct
import NumStability.Analysis.Norms
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Basic
import Mathlib.Tactic.NoncommRing

namespace NumStability

open scoped BigOperators Topology
open Filter

/-! # Higham Chapter 23: fast-multiplication identities and error bounds

The chapter's Winograd, Strassen, Winograd--Strassen, bilinear, and 3M
identities are formalized here. Actual rounded evaluators prove Theorem 23.1,
conventional multiplication, and the componentwise and normwise complex
bounds. The generic and recursively rounded citation-dependent results use an
explicit local first-order polynomial expansion with constructive producers;
the final norm bounds are derived rather than assumed.
 -/

section WinogradInnerProduct

/-- Equation (23.2), written as `m` independent adjacent pairs. -/
theorem higham23_eq23_2_winograd_identity {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) :
    ∑ i : Fin m,
        ((xOdd i + yEven i) * (xEven i + yOdd i) -
          xOdd i * xEven i - yOdd i * yEven i) =
      ∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i) := by
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The literal rounded Winograd inner-product path: form two rounded pair
sums, accumulate the three rounded dot products, and perform the two printed
subtractions. -/
noncomputable def higham23FlWinogradInnerProduct (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) : ℝ :=
  let p := fl_dotProduct fp m
    (fun i ↦ fp.fl_add (xOdd i) (yEven i))
    (fun i ↦ fp.fl_add (xEven i) (yOdd i))
  let q := fl_dotProduct fp m xOdd xEven
  let r := fl_dotProduct fp m yOdd yEven
  fp.fl_sub (fp.fl_sub p q) r

/-- Source-shaped analogue of (3.3) used in Theorem 23.1: every term of the
actual computed path has one relative factor bounded by `gamma_(m+4)`. -/
theorem higham23_winograd_factor_expansion (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ)
    (hvalid : gammaValid fp (m + 4)) :
    ∃ ε α β : Fin m → ℝ,
      (∀ i, |ε i| ≤ gamma fp (m + 4)) ∧
      (∀ i, |α i| ≤ gamma fp (m + 4)) ∧
      (∀ i, |β i| ≤ gamma fp (m + 4)) ∧
      higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven =
        (∑ i : Fin m,
          (xOdd i + yEven i) * (xEven i + yOdd i) * (1 + ε i)) -
        (∑ i : Fin m, xOdd i * xEven i * (1 + α i)) -
        (∑ i : Fin m, yOdd i * yEven i * (1 + β i)) := by
  let sx : Fin m → ℝ := fun i ↦ fp.fl_add (xOdd i) (yEven i)
  let sy : Fin m → ℝ := fun i ↦ fp.fl_add (xEven i) (yOdd i)
  let p := fl_dotProduct fp m sx sy
  let q := fl_dotProduct fp m xOdd xEven
  let r := fl_dotProduct fp m yOdd yEven
  let δx : Fin m → ℝ := fun i ↦
    Classical.choose (fp.model_add (xOdd i) (yEven i))
  let δy : Fin m → ℝ := fun i ↦
    Classical.choose (fp.model_add (xEven i) (yOdd i))
  have hδx : ∀ i, |δx i| ≤ fp.u ∧
      sx i = (xOdd i + yEven i) * (1 + δx i) := by
    intro i
    exact Classical.choose_spec (fp.model_add (xOdd i) (yEven i))
  have hδy : ∀ i, |δy i| ≤ fp.u ∧
      sy i = (xEven i + yOdd i) * (1 + δy i) := by
    intro i
    exact Classical.choose_spec (fp.model_add (xEven i) (yOdd i))
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hvalid
  obtain ⟨ηp, hηp, hp⟩ := dotProduct_backward_error fp m sx sy hm
  obtain ⟨ηq, hηq, hq⟩ := dotProduct_backward_error fp m xOdd xEven hm
  obtain ⟨ηr, hηr, hr⟩ := dotProduct_backward_error fp m yOdd yEven hm
  change p = _ at hp
  change q = _ at hq
  change r = _ at hr
  let δ1 := Classical.choose (fp.model_sub p q)
  have hδ1 : |δ1| ≤ fp.u ∧ fp.fl_sub p q = (p - q) * (1 + δ1) :=
    Classical.choose_spec (fp.model_sub p q)
  let δ2 := Classical.choose (fp.model_sub (fp.fl_sub p q) r)
  have hδ2 : |δ2| ≤ fp.u ∧
      fp.fl_sub (fp.fl_sub p q) r = (fp.fl_sub p q - r) * (1 + δ2) :=
    Classical.choose_spec (fp.model_sub (fp.fl_sub p q) r)
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hvalid
  have hm2 : gammaValid fp (m + 2) := gammaValid_mono fp (by omega) hvalid
  have hm3 : gammaValid fp (m + 3) := gammaValid_mono fp (by omega) hvalid
  have hu1 : fp.u ≤ gamma fp 1 := u_le_gamma fp one_pos h1
  have hδx1 : ∀ i, |δx i| ≤ gamma fp 1 := fun i ↦ le_trans (hδx i).1 hu1
  have hδy1 : ∀ i, |δy i| ≤ gamma fp 1 := fun i ↦ le_trans (hδy i).1 hu1
  have hδ11 : |δ1| ≤ gamma fp 1 := le_trans hδ1.1 hu1
  have hδ21 : |δ2| ≤ gamma fp 1 := le_trans hδ2.1 hu1
  have hepsExists : ∀ i : Fin m, ∃ e : ℝ,
      |e| ≤ gamma fp (m + 4) ∧
      (1 + δx i) * (1 + δy i) * (1 + ηp i) * (1 + δ1) * (1 + δ2) =
        1 + e := by
    intro i
    obtain ⟨e2, he2, heq2⟩ :=
      gamma_mul fp 1 1 (δx i) (δy i) (hδx1 i) (hδy1 i) h2
    obtain ⟨em2, hem2, heqm2⟩ :=
      gamma_mul fp 2 m e2 (ηp i) he2 (hηp i) (by simpa [Nat.add_comm] using hm2)
    have hem2' : |em2| ≤ gamma fp (m + 2) := by
      simpa [Nat.add_comm] using hem2
    obtain ⟨em3, hem3, heqm3⟩ :=
      gamma_mul fp (m + 2) 1 em2 δ1 hem2' hδ11 (by simpa [Nat.add_assoc] using hm3)
    obtain ⟨em4, hem4, heqm4⟩ :=
      gamma_mul fp (m + 3) 1 em3 δ2 hem3 hδ21 (by simpa [Nat.add_assoc] using hvalid)
    refine ⟨em4, ?_, ?_⟩
    · simpa [Nat.add_assoc] using hem4
    · rw [← heqm4, ← heqm3, ← heqm2, ← heq2]
  choose ε hε hεeq using hepsExists
  have halphaExists : ∀ i : Fin m, ∃ a : ℝ,
      |a| ≤ gamma fp (m + 4) ∧
      (1 + ηq i) * (1 + δ1) * (1 + δ2) = 1 + a := by
    intro i
    obtain ⟨am1, ham1, heqam1⟩ :=
      gamma_mul fp m 1 (ηq i) δ1 (hηq i) hδ11
        (gammaValid_mono fp (by omega) hvalid)
    obtain ⟨am2, ham2, heqam2⟩ :=
      gamma_mul fp (m + 1) 1 am1 δ2 ham1 hδ21
        (gammaValid_mono fp (by omega) hvalid)
    refine ⟨am2, le_trans ham2 (gamma_mono fp (by omega) hvalid), ?_⟩
    rw [← heqam2, ← heqam1]
  choose α hα hαeq using halphaExists
  have hbetaExists : ∀ i : Fin m, ∃ b : ℝ,
      |b| ≤ gamma fp (m + 4) ∧
      (1 + ηr i) * (1 + δ2) = 1 + b := by
    intro i
    obtain ⟨bm1, hbm1, heqbm1⟩ :=
      gamma_mul fp m 1 (ηr i) δ2 (hηr i) hδ21
        (gammaValid_mono fp (by omega) hvalid)
    exact ⟨bm1, le_trans hbm1 (gamma_mono fp (by omega) hvalid), heqbm1⟩
  choose β hβ hβeq using hbetaExists
  refine ⟨ε, α, β, hε, hα, hβ, ?_⟩
  simp only [higham23FlWinogradInnerProduct]
  change fp.fl_sub (fp.fl_sub p q) r = _
  rw [hδ2.2, hδ1.2, hp, hq, hr]
  have hP :
      (∑ i : Fin m, sx i * sy i * (1 + ηp i)) * (1 + δ1) * (1 + δ2) =
        ∑ i : Fin m,
          (xOdd i + yEven i) * (xEven i + yOdd i) * (1 + ε i) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hδx i).2, (hδy i).2]
    calc
      (xOdd i + yEven i) * (1 + δx i) *
          ((xEven i + yOdd i) * (1 + δy i)) * (1 + ηp i) *
          (1 + δ1) * (1 + δ2) =
        (xOdd i + yEven i) * (xEven i + yOdd i) *
          ((1 + δx i) * (1 + δy i) * (1 + ηp i) *
            (1 + δ1) * (1 + δ2)) := by ring
      _ = _ := by rw [hεeq i]
  have hQ :
      (∑ i : Fin m, xOdd i * xEven i * (1 + ηq i)) * (1 + δ1) * (1 + δ2) =
        ∑ i : Fin m, xOdd i * xEven i * (1 + α i) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      xOdd i * xEven i * (1 + ηq i) * (1 + δ1) * (1 + δ2) =
        xOdd i * xEven i * ((1 + ηq i) * (1 + δ1) * (1 + δ2)) := by ring
      _ = _ := by rw [hαeq i]
  have hR :
      (∑ i : Fin m, yOdd i * yEven i * (1 + ηr i)) * (1 + δ2) =
        ∑ i : Fin m, yOdd i * yEven i * (1 + β i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      yOdd i * yEven i * (1 + ηr i) * (1 + δ2) =
        yOdd i * yEven i * ((1 + ηr i) * (1 + δ2)) := by ring
      _ = _ := by rw [hβeq i]
  calc
    (((∑ i : Fin m, sx i * sy i * (1 + ηp i)) -
        ∑ i : Fin m, xOdd i * xEven i * (1 + ηq i)) * (1 + δ1) -
        ∑ i : Fin m, yOdd i * yEven i * (1 + ηr i)) * (1 + δ2) =
      (∑ i : Fin m, sx i * sy i * (1 + ηp i)) * (1 + δ1) * (1 + δ2) -
        (∑ i : Fin m, xOdd i * xEven i * (1 + ηq i)) * (1 + δ1) * (1 + δ2) -
        (∑ i : Fin m, yOdd i * yEven i * (1 + ηr i)) * (1 + δ2) := by ring
    _ = _ := by rw [hP, hQ, hR]

/-- Theorem 23.1 / equation (23.12), for an even vector length `n = 2m`.
`X` and `Y` are source-facing infinity-norm upper bounds for the odd/even
halves of the two vectors. -/
theorem higham23_theorem23_1_winograd_error (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) (X Y : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hxOdd : ∀ i, |xOdd i| ≤ X) (hxEven : ∀ i, |xEven i| ≤ X)
    (hyOdd : ∀ i, |yOdd i| ≤ Y) (hyEven : ∀ i, |yEven i| ≤ Y)
    (hvalid : gammaValid fp (m + 4)) :
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * (X + Y) ^ 2 := by
  obtain ⟨ε, α, β, hε, hα, hβ, hfl⟩ :=
    higham23_winograd_factor_expansion fp xOdd xEven yOdd yEven hvalid
  let P : Fin m → ℝ := fun i ↦ (xOdd i + yEven i) * (xEven i + yOdd i)
  let Q : Fin m → ℝ := fun i ↦ xOdd i * xEven i
  let R : Fin m → ℝ := fun i ↦ yOdd i * yEven i
  have hid := higham23_eq23_2_winograd_identity xOdd xEven yOdd yEven
  change (∑ i : Fin m, (P i - Q i - R i)) = _ at hid
  have hPe : (∑ i : Fin m, P i * (1 + ε i)) =
      (∑ i : Fin m, P i) + ∑ i : Fin m, P i * ε i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hQa : (∑ i : Fin m, Q i * (1 + α i)) =
      (∑ i : Fin m, Q i) + ∑ i : Fin m, Q i * α i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRb : (∑ i : Fin m, R i * (1 + β i)) =
      (∑ i : Fin m, R i) + ∑ i : Fin m, R i * β i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hplain : (∑ i : Fin m, (P i - Q i - R i)) =
      (∑ i : Fin m, P i) - (∑ i : Fin m, Q i) - (∑ i : Fin m, R i) := by
    simp only [Finset.sum_sub_distrib]
  have hNeg : (∑ i : Fin m, -P i * ε i) = -(∑ i : Fin m, P i * ε i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herr :
      (∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
          higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven =
        ∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i) := by
    rw [← hid, hplain, hfl, hPe, hQa, hRb]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hNeg]
    ring
  rw [herr]
  have hG : 0 ≤ gamma fp (m + 4) := gamma_nonneg fp hvalid
  have hXY : 0 ≤ X + Y := add_nonneg hX hY
  calc
    |∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i)| ≤
        ∑ i : Fin m, |(-P i * ε i + Q i * α i + R i * β i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, gamma fp (m + 4) * (2 * (X + Y) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hP1 : |xOdd i + yEven i| ≤ X + Y :=
        le_trans (abs_add_le _ _) (add_le_add (hxOdd i) (hyEven i))
      have hP2 : |xEven i + yOdd i| ≤ X + Y :=
        le_trans (abs_add_le _ _) (add_le_add (hxEven i) (hyOdd i))
      have hPbound : |P i| ≤ (X + Y) ^ 2 := by
        rw [show P i = (xOdd i + yEven i) * (xEven i + yOdd i) from rfl,
          abs_mul, pow_two]
        exact mul_le_mul hP1 hP2 (abs_nonneg _) hXY
      have hQbound : |Q i| ≤ X ^ 2 := by
        rw [show Q i = xOdd i * xEven i from rfl, abs_mul, pow_two]
        exact mul_le_mul (hxOdd i) (hxEven i) (abs_nonneg _) hX
      have hRbound : |R i| ≤ Y ^ 2 := by
        rw [show R i = yOdd i * yEven i from rfl, abs_mul, pow_two]
        exact mul_le_mul (hyOdd i) (hyEven i) (abs_nonneg _) hY
      calc
        |(-P i * ε i + Q i * α i + R i * β i)| ≤
            |P i| * |ε i| + |Q i| * |α i| + |R i| * |β i| := by
          calc
            |(-P i * ε i + Q i * α i + R i * β i)| ≤
                |(-P i * ε i + Q i * α i)| + |R i * β i| := abs_add_le _ _
            _ ≤ (|-P i * ε i| + |Q i * α i|) + |R i * β i| := by
              linarith [abs_add_le (-P i * ε i) (Q i * α i)]
            _ = _ := by simp only [abs_mul, abs_neg]
        _ ≤ |P i| * gamma fp (m + 4) +
              |Q i| * gamma fp (m + 4) + |R i| * gamma fp (m + 4) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hα i) (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg _))
        _ = gamma fp (m + 4) * (|P i| + |Q i| + |R i|) := by ring
        _ ≤ gamma fp (m + 4) * ((X + Y) ^ 2 + X ^ 2 + Y ^ 2) := by
          gcongr
        _ ≤ gamma fp (m + 4) * (2 * (X + Y) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hG
          nlinarith [mul_nonneg hX hY]
    _ = ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * (X + Y) ^ 2 := by
      simp
      ring

/-- Componentwise form retained before replacing every input by its infinity
norm.  This is the exact-gamma form used again for the 3M bound (23.22). -/
theorem higham23_winograd_componentwise_error (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ)
    (hvalid : gammaValid fp (m + 4)) :
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      gamma fp (m + 4) *
        ∑ i : Fin m,
          (|xOdd i + yEven i| * |xEven i + yOdd i| +
            |xOdd i| * |xEven i| + |yOdd i| * |yEven i|) := by
  obtain ⟨ε, α, β, hε, hα, hβ, hfl⟩ :=
    higham23_winograd_factor_expansion fp xOdd xEven yOdd yEven hvalid
  let P : Fin m → ℝ := fun i ↦ (xOdd i + yEven i) * (xEven i + yOdd i)
  let Q : Fin m → ℝ := fun i ↦ xOdd i * xEven i
  let R : Fin m → ℝ := fun i ↦ yOdd i * yEven i
  have hid := higham23_eq23_2_winograd_identity xOdd xEven yOdd yEven
  change (∑ i : Fin m, (P i - Q i - R i)) = _ at hid
  have hPe : (∑ i : Fin m, P i * (1 + ε i)) =
      (∑ i : Fin m, P i) + ∑ i : Fin m, P i * ε i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hQa : (∑ i : Fin m, Q i * (1 + α i)) =
      (∑ i : Fin m, Q i) + ∑ i : Fin m, Q i * α i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRb : (∑ i : Fin m, R i * (1 + β i)) =
      (∑ i : Fin m, R i) + ∑ i : Fin m, R i * β i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hplain : (∑ i : Fin m, (P i - Q i - R i)) =
      (∑ i : Fin m, P i) - (∑ i : Fin m, Q i) - (∑ i : Fin m, R i) := by
    simp only [Finset.sum_sub_distrib]
  have hNeg : (∑ i : Fin m, -P i * ε i) = -(∑ i : Fin m, P i * ε i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herr :
      (∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
          higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven =
        ∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i) := by
    rw [← hid, hplain, hfl, hPe, hQa, hRb]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hNeg]
    ring
  rw [herr]
  calc
    |∑ i : Fin m, (-P i * ε i + Q i * α i + R i * β i)| ≤
        ∑ i : Fin m, |(-P i * ε i + Q i * α i + R i * β i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m,
        gamma fp (m + 4) * (|P i| + |Q i| + |R i|) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |(-P i * ε i + Q i * α i + R i * β i)| ≤
            |P i| * |ε i| + |Q i| * |α i| + |R i| * |β i| := by
          calc
            |(-P i * ε i + Q i * α i + R i * β i)| ≤
                |(-P i * ε i + Q i * α i)| + |R i * β i| := abs_add_le _ _
            _ ≤ (|-P i * ε i| + |Q i * α i|) + |R i * β i| := by
              linarith [abs_add_le (-P i * ε i) (Q i * α i)]
            _ = _ := by simp only [abs_mul, abs_neg]
        _ ≤ |P i| * gamma fp (m + 4) +
              |Q i| * gamma fp (m + 4) + |R i| * gamma fp (m + 4) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hα i) (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg _))
        _ = _ := by ring
    _ = gamma fp (m + 4) *
        ∑ i : Fin m,
          (|xOdd i + yEven i| * |xEven i + yOdd i| +
            |xOdd i| * |xEven i| + |yOdd i| * |yEven i|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [P, Q, R, abs_mul]

end WinogradInnerProduct

section BalancedScaling

/-- Scalar inequality used in the balanced-scaling consequence after Theorem
23.1.  It converts the sum-of-norms square in (23.12) to the displayed product
bound whenever the two nonzero norms differ by at most a factor `tau`. -/
theorem higham23_balanced_sum_sq_le
    {a b tau : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (htau : 0 < tau)
    (hlower : tau⁻¹ ≤ a / b) (hupper : a / b ≤ tau) :
    (a + b) ^ 2 ≤ 2 * (tau + 1) * a * b := by
  have hab : a ≤ tau * b := (div_le_iff₀ hb).mp hupper
  have hscaled : tau⁻¹ * b ≤ a := (le_div_iff₀ hb).mp hlower
  have htau0 : tau ≠ 0 := ne_of_gt htau
  have hba : b ≤ tau * a := by
    calc
      b = tau * (tau⁻¹ * b) := by field_simp
      _ ≤ tau * a := mul_le_mul_of_nonneg_left hscaled (le_of_lt htau)
  have haa : a * a ≤ tau * a * b := by
    have := mul_le_mul_of_nonneg_left hab ha
    nlinarith
  have hbb : b * b ≤ tau * a * b := by
    have := mul_le_mul_of_nonneg_left hba (le_of_lt hb)
    nlinarith
  nlinarith [sq_nonneg (a + b)]

/-- Balanced-scaling form of Theorem 23.1.  This is the displayed coefficient
after (23.13), specialized to one computed inner product; applying it uniformly
to rows and columns gives the matrix max-entry-norm statement. -/
theorem higham23_balanced_winograd_error (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) (X Y tau : ℝ)
    (hX : 0 ≤ X) (hY : 0 < Y) (htau : 0 < tau)
    (hxOdd : ∀ i, |xOdd i| ≤ X) (hxEven : ∀ i, |xEven i| ≤ X)
    (hyOdd : ∀ i, |yOdd i| ≤ Y) (hyEven : ∀ i, |yEven i| ≤ Y)
    (hlower : tau⁻¹ ≤ X / Y) (hupper : X / Y ≤ tau)
    (hvalid : gammaValid fp (m + 4)) :
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      2 * (tau + 1) * ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * X * Y := by
  have hmain := higham23_theorem23_1_winograd_error fp
    xOdd xEven yOdd yEven X Y hX (le_of_lt hY)
    hxOdd hxEven hyOdd hyEven hvalid
  have hbalance := higham23_balanced_sum_sq_le hX hY htau hlower hupper
  have hcoeff : 0 ≤ ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) :=
    mul_nonneg (by positivity) (gamma_nonneg fp hvalid)
  calc
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * (X + Y) ^ 2 := hmain
    _ ≤ ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) *
        (2 * (tau + 1) * X * Y) :=
      mul_le_mul_of_nonneg_left hbalance hcoeff
    _ = _ := by ring

end BalancedScaling

section GammaAsymptotics

/-- The exact quadratic-and-higher remainder in `gamma_k`. -/
noncomputable def higham23GammaRemainder (k : ℕ) (u : ℝ) : ℝ :=
  (((k : ℝ) * u) ^ 2) / (1 - (k : ℝ) * u)

noncomputable def higham23GammaRemainderCoefficient (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) ^ 2 / (1 - (k : ℝ) * u)

theorem higham23_gamma_split (fp : FPModel) (k : ℕ)
    (hvalid : gammaValid fp k) :
    gamma fp k = (k : ℝ) * fp.u + higham23GammaRemainder k fp.u := by
  simpa [higham23GammaRemainder] using
    gamma_eq_linear_plus_quadratic_remainder fp k hvalid

theorem higham23_gammaRemainder_factor (k : ℕ) (u : ℝ) :
    higham23GammaRemainder k u =
      u ^ 2 * higham23GammaRemainderCoefficient k u := by
  unfold higham23GammaRemainder higham23GammaRemainderCoefficient
  ring

theorem higham23_gammaRemainderCoefficient_continuousAt_zero (k : ℕ) :
    ContinuousAt (higham23GammaRemainderCoefficient k) 0 := by
  unfold higham23GammaRemainderCoefficient
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

/-- The remainder in the source's first-order gamma expansion is genuinely
`O(u²)` as `u → 0`, with the operation count fixed. -/
theorem higham23_gammaRemainder_isBigO_u_sq (k : ℕ) :
    (fun u : ℝ ↦ higham23GammaRemainder k u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hCoeff :
      (fun u : ℝ ↦ higham23GammaRemainderCoefficient k u) =O[𝓝 0]
        (fun _ : ℝ ↦ (1 : ℝ)) :=
    (higham23_gammaRemainderCoefficient_continuousAt_zero k).isBigO_one ℝ
  have hProduct := huSq.mul hCoeff
  simpa only [higham23_gammaRemainder_factor, mul_one] using hProduct

/-- Rewrite any exact-gamma error bound into its printed linear term plus the
explicit quadratic remainder. -/
theorem higham23_error_bound_gamma_split (fp : FPModel) (k : ℕ)
    (error budget : ℝ) (hvalid : gammaValid fp k)
    (h : error ≤ gamma fp k * budget) :
    error ≤ (k : ℝ) * fp.u * budget +
      higham23GammaRemainder k fp.u * budget := by
  rw [higham23_gamma_split fp k hvalid] at h
  nlinarith

end GammaAsymptotics

section ConventionalMatrixMultiplication

/-- Actual conventional rounded matrix multiplication, entrywise as the
repository's left-to-right rounded dot product. -/
noncomputable def higham23FlMatrixMul (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ fl_dotProduct fp n (fun k ↦ A i k) (fun k ↦ B k j)

/-- A source-facing presentation of the max-entry norm inequality. -/
def Higham23MaxEntryNormLe {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bound : ℝ) : Prop :=
  ∀ i j, |A i j| ≤ bound

/-- Equation (23.10), exact-gamma componentwise form for the actual computed
matrix product. -/
theorem higham23_eq23_10_conventional_componentwise (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hvalid : gammaValid fp n)
    (i j : Fin n) :
    |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
      gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
  simpa [higham23FlMatrixMul, Matrix.mul_apply, abs_sub_comm] using
    dotProduct_error_bound fp n (fun k ↦ A i k) (fun k ↦ B k j) hvalid

/-- Equation (23.10) with the printed `nu` term and explicit `O(u²)`
remainder. -/
theorem higham23_eq23_10_conventional_firstOrder (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hvalid : gammaValid fp n)
    (i j : Fin n) :
    |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
      (n : ℝ) * fp.u * (∑ k : Fin n, |A i k| * |B k j|) +
        higham23GammaRemainder n fp.u *
          (∑ k : Fin n, |A i k| * |B k j|) :=
  higham23_error_bound_gamma_split fp n _ _ hvalid
    (higham23_eq23_10_conventional_componentwise fp A B hvalid i j)

/-- Equation (23.17), as the exact max-entry envelope produced from (23.10).
The first summand is the printed `n²u` coefficient; the second is a genuine
quadratic remainder by `higham23_gammaRemainder_isBigO_u_sq`. -/
theorem higham23_eq23_17_conventional_normwise (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (Amax Bmax : ℝ)
    (hAmax : 0 ≤ Amax) (_hBmax : 0 ≤ Bmax)
    (hA : Higham23MaxEntryNormLe A Amax)
    (hB : Higham23MaxEntryNormLe B Bmax)
    (hvalid : gammaValid fp n) :
    Higham23MaxEntryNormLe (A * B - higham23FlMatrixMul fp A B)
      ((n : ℝ) ^ 2 * fp.u * Amax * Bmax +
        higham23GammaRemainder n fp.u * (n : ℝ) * Amax * Bmax) := by
  intro i j
  have hcomp := higham23_eq23_10_conventional_componentwise fp A B hvalid i j
  have hbudget :
      (∑ k : Fin n, |A i k| * |B k j|) ≤ (n : ℝ) * Amax * Bmax := by
    calc
      (∑ k : Fin n, |A i k| * |B k j|) ≤
          ∑ _k : Fin n, Amax * Bmax := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hAmax
      _ = (n : ℝ) * Amax * Bmax := by simp; ring
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hvalid
  have hgammaBound :
      |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
        gamma fp n * ((n : ℝ) * Amax * Bmax) :=
    le_trans hcomp (mul_le_mul_of_nonneg_left hbudget hgamma)
  have hsplit := higham23_error_bound_gamma_split fp n
    |(A * B) i j - higham23FlMatrixMul fp A B i j|
    ((n : ℝ) * Amax * Bmax) hvalid hgammaBound
  simpa [Higham23MaxEntryNormLe, Matrix.sub_apply] using (show
    |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
      (n : ℝ) ^ 2 * fp.u * Amax * Bmax +
        higham23GammaRemainder n fp.u * (n : ℝ) * Amax * Bmax by
      nlinarith)

end ConventionalMatrixMultiplication

section BlockAlgorithms

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- A `2 × 2` block matrix, used only to state the exact algebraic algorithms
without imposing commutativity on the blocks. -/
@[ext] structure Higham23Block2 where
  c11 : R
  c12 : R
  c21 : R
  c22 : R

/-- Conventional `2 × 2` block multiplication, equation (23.3). -/
def higham23BlockMul (A B : Higham23Block2 (R := R)) : Higham23Block2 (R := R) where
  c11 := A.c11 * B.c11 + A.c12 * B.c21
  c12 := A.c11 * B.c12 + A.c12 * B.c22
  c21 := A.c21 * B.c11 + A.c22 * B.c21
  c22 := A.c21 * B.c12 + A.c22 * B.c22

/-- Equation (23.4): Strassen's seven-product construction. -/
def higham23Strassen2 (A B : Higham23Block2 (R := R)) : Higham23Block2 (R := R) :=
  let p1 := (A.c11 + A.c22) * (B.c11 + B.c22)
  let p2 := (A.c21 + A.c22) * B.c11
  let p3 := A.c11 * (B.c12 - B.c22)
  let p4 := A.c22 * (B.c21 - B.c11)
  let p5 := (A.c11 + A.c12) * B.c22
  let p6 := (A.c21 - A.c11) * (B.c11 + B.c12)
  let p7 := (A.c12 - A.c22) * (B.c21 + B.c22)
  { c11 := p1 + p4 - p5 + p7
    c12 := p3 + p5
    c21 := p2 + p4
    c22 := p1 + p3 - p2 + p6 }

/-- Exact correctness of Strassen's formulas (23.4), valid for noncommutative
blocks and hence for matrix blocks. -/
theorem higham23_eq23_4_strassen_correct (A B : Higham23Block2 (R := R)) :
    higham23Strassen2 A B = higham23BlockMul A B := by
  cases A
  cases B
  apply Higham23Block2.ext <;>
    simp [higham23Strassen2, higham23BlockMul] <;>
    noncomm_ring

/-- Equation (23.6): Winograd's 15-addition variant of Strassen's method. -/
def higham23WinogradStrassen2
    (A B : Higham23Block2 (R := R)) : Higham23Block2 (R := R) :=
  let s1 := A.c21 + A.c22
  let s2 := s1 - A.c11
  let s3 := A.c11 - A.c21
  let s4 := A.c12 - s2
  let s5 := B.c12 - B.c11
  let s6 := B.c22 - s5
  let s7 := B.c22 - B.c12
  let s8 := s6 - B.c21
  let m1 := s2 * s6
  let m2 := A.c11 * B.c11
  let m3 := A.c12 * B.c21
  let m4 := s3 * s7
  let m5 := s1 * s5
  let m6 := s4 * B.c22
  let m7 := A.c22 * s8
  let t1 := m1 + m2
  let t2 := t1 + m4
  { c11 := m2 + m3
    c12 := t1 + m5 + m6
    c21 := t2 - m7
    c22 := t2 + m5 }

/-- Exact correctness of Winograd's variant (23.6). -/
theorem higham23_eq23_6_winogradStrassen_correct
    (A B : Higham23Block2 (R := R)) :
    higham23WinogradStrassen2 A B = higham23BlockMul A B := by
  cases A
  cases B
  apply Higham23Block2.ext <;>
    simp [higham23WinogradStrassen2, higham23BlockMul] <;>
    noncomm_ring

/-- Exact recursive operation semantics underlying equation (23.5).  The
second argument is the number of Strassen levels above the conventional
threshold `2^r`; the pair stores multiplication and addition counts. -/
def higham23StrassenCosts (r : ℕ) : ℕ → ℕ × ℕ
  | 0 => (8 ^ r, 4 ^ r * (2 ^ r - 1))
  | depth + 1 =>
      let previous := higham23StrassenCosts r depth
      (7 * previous.1, 7 * previous.2 + 18 * 4 ^ (r + depth))

/-- The multiplication-count solution in (23.5). -/
theorem higham23_strassenCosts_mul (r depth : ℕ) :
    (higham23StrassenCosts r depth).1 = 7 ^ depth * 8 ^ r := by
  induction depth with
  | zero => simp [higham23StrassenCosts]
  | succ depth ih =>
      simp [higham23StrassenCosts, ih, pow_succ]
      ring

/-- Subtraction-free form of the addition-count solution in (23.5). -/
theorem higham23_strassenCosts_add_augmented (r depth : ℕ) :
    (higham23StrassenCosts r depth).2 + 6 * 4 ^ (r + depth) =
      4 ^ r * (2 ^ r + 5) * 7 ^ depth := by
  induction depth with
  | zero =>
      have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      simp only [higham23StrassenCosts, Nat.add_zero, pow_zero,
        Nat.mul_one]
      rw [Nat.mul_comm 6 (4 ^ r), ← Nat.mul_add]
      congr 1
      omega
  | succ depth ih =>
      simp only [higham23StrassenCosts]
      rw [← Nat.add_assoc r depth 1, pow_succ]
      calc
        7 * (higham23StrassenCosts r depth).2 + 18 * 4 ^ (r + depth) +
            6 * (4 ^ (r + depth) * 4) =
            7 * ((higham23StrassenCosts r depth).2 +
              6 * 4 ^ (r + depth)) := by ring
        _ = 7 * (4 ^ r * (2 ^ r + 5) * 7 ^ depth) := by rw [ih]
        _ = 4 ^ r * (2 ^ r + 5) * 7 ^ (depth + 1) := by
          rw [pow_succ]
          ring

/-- Equation (23.5), obtained from the recursive operation semantics. -/
theorem higham23_eq23_5_strassen_costs (r k : ℕ) (hrk : r ≤ k) :
    higham23StrassenCosts r (k - r) =
      (7 ^ (k - r) * 8 ^ r,
        4 ^ r * (2 ^ r + 5) * 7 ^ (k - r) - 6 * 4 ^ k) := by
  apply Prod.ext
  · exact higham23_strassenCosts_mul r (k - r)
  · simp only
    apply Nat.eq_sub_of_add_eq
    have h := higham23_strassenCosts_add_augmented r (k - r)
    rwa [Nat.add_sub_of_le hrk] at h

end BlockAlgorithms

section BilinearAlgorithm

/-- Equations (23.7a)--(23.7b): exact data of a bilinear noncommutative
algorithm.  The scalar coefficient ring is kept separate from the block ring;
the external Bini--Lotti stability constants are not invented here. -/
structure Higham23BilinearAlgorithm (h t : ℕ) where
  U : Fin t → Fin h → Fin h → ℝ
  V : Fin t → Fin h → Fin h → ℝ
  W : Fin h → Fin h → Fin t → ℝ

/-- Equation (23.7b): the `k`th nonscalar product formed from the two
coefficient-weighted input matrices. -/
noncomputable def higham23BilinearProduct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  (∑ i : Fin h, ∑ j : Fin h, alg.U k i j * A i j) *
    (∑ i : Fin h, ∑ j : Fin h, alg.V k i j * B i j)

/-- Equation (23.7a): reconstruct every output entry from the `t` products. -/
noncomputable def higham23BilinearEvaluate {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j ↦ ∑ k : Fin t, alg.W i j k * higham23BilinearProduct alg A B k

/-- The source phrase "algorithm for multiplying" means that the fixed tensor
data reconstruct matrix multiplication for every pair of inputs. -/
def Higham23BilinearAlgorithm.IsCorrect {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) : Prop :=
  ∀ A B : Matrix (Fin h) (Fin h) ℝ,
    higham23BilinearEvaluate alg A B = A * B

/-- Equation (23.7b) is the executable product formula, exposed separately for
source-facing use. -/
theorem higham23_eq23_7b {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) :
    higham23BilinearProduct alg A B k =
      (∑ i : Fin h, ∑ j : Fin h, alg.U k i j * A i j) *
        (∑ i : Fin h, ∑ j : Fin h, alg.V k i j * B i j) := rfl

/-- Equation (23.7a), entrywise. -/
theorem higham23_eq23_7a {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (i j : Fin h) :
    higham23BilinearEvaluate alg A B i j =
      ∑ k : Fin t, alg.W i j k * higham23BilinearProduct alg A B k := rfl

/-- One-level exact reconstruction for tensors satisfying the defining
correctness condition of a bilinear multiplication algorithm. -/
theorem higham23_bilinearEvaluate_correct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (halg : alg.IsCorrect)
    (A B : Matrix (Fin h) (Fin h) ℝ) :
    higham23BilinearEvaluate alg A B = A * B :=
  halg A B

/-! Miller's (23.11) and Bini--Lotti's Theorem 23.4 are cited results whose
rounded arithmetic graphs are not supplied in Chapter 23.  This foundation
does not manufacture target-bearing witnesses; the literal rounded circuits
and their error inductions are provided downstream in `Higham23Remaining`
and `Higham23Bini`. -/

end BilinearAlgorithm

section ThreeM

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- Equations (23.8)--(23.9): the 3M method returns the real and imaginary
parts using three multiplications in `R`. -/
def higham23ThreeM (a1 a2 b1 b2 : R) : R × R :=
  let t1 := a1 * b1
  let t2 := a2 * b2
  (t1 - t2, (a1 + a2) * (b1 + b2) - t1 - t2)

/-- Exact correctness of the 3M identity; the proof does not use
commutativity, so it applies to real matrix blocks. -/
theorem higham23_eq23_9_threeM_correct (a1 a2 b1 b2 : R) :
    higham23ThreeM a1 a2 b1 b2 =
      (a1 * b1 - a2 * b2, a1 * b2 + a2 * b1) := by
  simp [higham23ThreeM]
  noncomm_ring

inductive Higham23TwoDotMode
  | add
  | sub

namespace Higham23TwoDotMode

def sign : Higham23TwoDotMode → ℝ
  | add => 1
  | sub => -1

def rounded (fp : FPModel) : Higham23TwoDotMode → ℝ → ℝ → ℝ
  | add => fp.fl_add
  | sub => fp.fl_sub

theorem model (fp : FPModel) (mode : Higham23TwoDotMode) (x y : ℝ) :
    ∃ δ : ℝ, |δ| ≤ fp.u ∧
      mode.rounded fp x y = (x + mode.sign * y) * (1 + δ) := by
  cases mode with
  | add =>
      obtain ⟨δ, hδ, heq⟩ := fp.model_add x y
      exact ⟨δ, hδ, by simpa [rounded, sign] using heq⟩
  | sub =>
      obtain ⟨δ, hδ, heq⟩ := fp.model_sub x y
      exact ⟨δ, hδ, by simpa [rounded, sign] using heq⟩

end Higham23TwoDotMode

/-- Actual conventional two-dot evaluation used by both the real and
imaginary parts of ordinary complex matrix multiplication. -/
noncomputable def higham23FlTwoDot (fp : FPModel) {n : ℕ}
    (mode : Higham23TwoDotMode)
    (a b c d : Fin n → ℝ) : ℝ :=
  mode.rounded fp (fl_dotProduct fp n a b) (fl_dotProduct fp n c d)

/-- Common exact-gamma bound for a rounded addition or subtraction of two
actual rounded dot products. -/
theorem higham23_flTwoDot_error (fp : FPModel) {n : ℕ}
    (mode : Higham23TwoDotMode) (a b c d : Fin n → ℝ)
    (hvalid : gammaValid fp (n + 1)) :
    |((∑ k : Fin n, a k * b k) +
        mode.sign * (∑ k : Fin n, c k * d k)) -
        higham23FlTwoDot fp mode a b c d| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, (|a k| * |b k| + |c k| * |d k|) := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  obtain ⟨ηp, hηp, hp⟩ := dotProduct_backward_error fp n a b hn
  obtain ⟨ηq, hηq, hq⟩ := dotProduct_backward_error fp n c d hn
  let p := fl_dotProduct fp n a b
  let q := fl_dotProduct fp n c d
  change p = _ at hp
  change q = _ at hq
  obtain ⟨δ, hδ, hrounded⟩ := mode.model fp p q
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hδ1 : |δ| ≤ gamma fp 1 :=
    le_trans hδ (u_le_gamma fp one_pos h1)
  have hαExists : ∀ i : Fin n, ∃ α : ℝ,
      |α| ≤ gamma fp (n + 1) ∧ (1 + ηp i) * (1 + δ) = 1 + α := by
    intro i
    exact gamma_mul fp n 1 (ηp i) δ (hηp i) hδ1 hvalid
  choose α hα hαeq using hαExists
  have hβExists : ∀ i : Fin n, ∃ β : ℝ,
      |β| ≤ gamma fp (n + 1) ∧ (1 + ηq i) * (1 + δ) = 1 + β := by
    intro i
    exact gamma_mul fp n 1 (ηq i) δ (hηq i) hδ1 hvalid
  choose β hβ hβeq using hβExists
  have hPfactor :
      (∑ i : Fin n, a i * b i * (1 + ηp i)) * (1 + δ) =
        ∑ i : Fin n, a i * b i * (1 + α i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      a i * b i * (1 + ηp i) * (1 + δ) =
          a i * b i * ((1 + ηp i) * (1 + δ)) := by ring
      _ = _ := by rw [hαeq i]
  have hQfactor :
      (∑ i : Fin n, c i * d i * (1 + ηq i)) * (1 + δ) =
        ∑ i : Fin n, c i * d i * (1 + β i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      c i * d i * (1 + ηq i) * (1 + δ) =
          c i * d i * ((1 + ηq i) * (1 + δ)) := by ring
      _ = _ := by rw [hβeq i]
  have hcomputed : higham23FlTwoDot fp mode a b c d =
      (∑ i : Fin n, a i * b i * (1 + α i)) +
        mode.sign * (∑ i : Fin n, c i * d i * (1 + β i)) := by
    simp only [higham23FlTwoDot]
    change mode.rounded fp p q = _
    rw [hrounded, hp, hq, add_mul, hPfactor]
    calc
      (∑ i : Fin n, a i * b i * (1 + α i)) +
          (mode.sign * (∑ i : Fin n, c i * d i * (1 + ηq i))) * (1 + δ) =
        (∑ i : Fin n, a i * b i * (1 + α i)) +
          mode.sign * ((∑ i : Fin n, c i * d i * (1 + ηq i)) * (1 + δ)) := by ring
      _ = _ := by rw [hQfactor]
  rw [hcomputed]
  have hA : (∑ i : Fin n, a i * b i * (1 + α i)) =
      (∑ i : Fin n, a i * b i) + ∑ i : Fin n, a i * b i * α i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hB : (∑ i : Fin n, c i * d i * (1 + β i)) =
      (∑ i : Fin n, c i * d i) + ∑ i : Fin n, c i * d i * β i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hA, hB]
  have herr :
      (∑ i : Fin n, a i * b i) + mode.sign * (∑ i : Fin n, c i * d i) -
          ((∑ i : Fin n, a i * b i) + (∑ i : Fin n, a i * b i * α i) +
            mode.sign * ((∑ i : Fin n, c i * d i) +
              ∑ i : Fin n, c i * d i * β i)) =
        -(∑ i : Fin n, a i * b i * α i) -
          mode.sign * (∑ i : Fin n, c i * d i * β i) := by ring
  rw [herr]
  calc
    |-(∑ i : Fin n, a i * b i * α i) -
        mode.sign * (∑ i : Fin n, c i * d i * β i)| ≤
      |∑ i : Fin n, a i * b i * α i| +
        |mode.sign| * |∑ i : Fin n, c i * d i * β i| := by
      calc
        |-(∑ i : Fin n, a i * b i * α i) -
            mode.sign * (∑ i : Fin n, c i * d i * β i)| ≤
          |-(∑ i : Fin n, a i * b i * α i)| +
            |mode.sign * (∑ i : Fin n, c i * d i * β i)| := by
              simpa [sub_eq_add_neg] using
                abs_add_le (-(∑ i : Fin n, a i * b i * α i))
                  (-(mode.sign * (∑ i : Fin n, c i * d i * β i)))
        _ = _ := by simp only [abs_neg, abs_mul]
    _ = |∑ i : Fin n, a i * b i * α i| +
        |∑ i : Fin n, c i * d i * β i| := by
      cases mode <;> simp [Higham23TwoDotMode.sign]
    _ ≤ (∑ i : Fin n, |a i| * |b i| * |α i|) +
        ∑ i : Fin n, |c i| * |d i| * |β i| := by
      apply add_le_add
      · calc
          |∑ i : Fin n, a i * b i * α i| ≤
              ∑ i : Fin n, |a i * b i * α i| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul]
      · calc
          |∑ i : Fin n, c i * d i * β i| ≤
              ∑ i : Fin n, |c i * d i * β i| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul]
    _ ≤ (∑ i : Fin n, |a i| * |b i| * gamma fp (n + 1)) +
        ∑ i : Fin n, |c i| * |d i| * gamma fp (n + 1) := by
      apply add_le_add <;> apply Finset.sum_le_sum <;> intro i _
      · simpa only [abs_mul] using
          mul_le_mul_of_nonneg_left (hα i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · simpa only [abs_mul] using
          mul_le_mul_of_nonneg_left (hβ i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp (n + 1) *
        ∑ i : Fin n, (|a i| * |b i| + |c i| * |d i|) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Actual conventional real part `A1*B1 - A2*B2`. -/
noncomputable def higham23FlConventionalReal (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  higham23FlTwoDot fp .sub A1 B1 A2 B2

/-- Equation (23.20), exact-gamma form. -/
theorem higham23_eq23_20_conventional_real_error (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B1 k - A2 k * B2 k)) -
        higham23FlConventionalReal fp A1 A2 B1 B2| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, (|A1 k| * |B1 k| + |A2 k| * |B2 k|) := by
  simpa [higham23FlConventionalReal, Higham23TwoDotMode.sign,
    Finset.sum_sub_distrib] using
    higham23_flTwoDot_error fp .sub A1 B1 A2 B2 hvalid

/-- Equation (23.20) with its first-order term and explicit `O(u²)`
remainder separated. -/
theorem higham23_eq23_20_conventional_real_firstOrder (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B1 k - A2 k * B2 k)) -
        higham23FlConventionalReal fp A1 A2 B1 B2| ≤
      ((n + 1 : ℕ) : ℝ) * fp.u *
          (∑ k : Fin n, (|A1 k| * |B1 k| + |A2 k| * |B2 k|)) +
        higham23GammaRemainder (n + 1) fp.u *
          (∑ k : Fin n, (|A1 k| * |B1 k| + |A2 k| * |B2 k|)) :=
  higham23_error_bound_gamma_split fp (n + 1) _ _ hvalid
    (higham23_eq23_20_conventional_real_error fp A1 A2 B1 B2 hvalid)

/-- Actual conventional imaginary part `A1*B2 + A2*B1`. -/
noncomputable def higham23FlConventionalImaginary (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  higham23FlTwoDot fp .add A1 B2 A2 B1

/-- Equation (23.21), exact-gamma form. -/
theorem higham23_eq23_21_conventional_imaginary_error (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlConventionalImaginary fp A1 A2 B1 B2| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, (|A1 k| * |B2 k| + |A2 k| * |B1 k|) := by
  simpa [higham23FlConventionalImaginary, Higham23TwoDotMode.sign,
    Finset.sum_add_distrib] using
    higham23_flTwoDot_error fp .add A1 B2 A2 B1 hvalid

/-- Equation (23.21) with explicit quadratic remainder. -/
theorem higham23_eq23_21_conventional_imaginary_firstOrder (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 1)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlConventionalImaginary fp A1 A2 B1 B2| ≤
      ((n + 1 : ℕ) : ℝ) * fp.u *
          (∑ k : Fin n, (|A1 k| * |B2 k| + |A2 k| * |B1 k|)) +
        higham23GammaRemainder (n + 1) fp.u *
          (∑ k : Fin n, (|A1 k| * |B2 k| + |A2 k| * |B1 k|)) :=
  higham23_error_bound_gamma_split fp (n + 1) _ _ hvalid
    (higham23_eq23_21_conventional_imaginary_error fp A1 A2 B1 B2 hvalid)

/-- Actual rounded imaginary-part path of the 3M method for one matrix-product
entry.  It is the same arithmetic graph as the Winograd cancellation identity
after the indicated permutation of the four real input vectors. -/
noncomputable def higham23FlThreeMImaginary (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  higham23FlWinogradInnerProduct fp A1 B1 B2 A2

/-- Exact-gamma version of equation (23.22) for one output entry of the actual
rounded 3M path.  Expanding `gamma_(n+4)` gives the printed first-order
coefficient `(n+4)u`. -/
theorem higham23_eq23_22_threeM_imaginary_error (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 4)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlThreeMImaginary fp A1 A2 B1 B2| ≤
      gamma fp (n + 4) *
        ∑ k : Fin n,
          ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
            |A1 k| * |B1 k| + |A2 k| * |B2 k|) := by
  have hcore := higham23_winograd_componentwise_error fp A1 B1 B2 A2 hvalid
  change
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlWinogradInnerProduct fp A1 B1 B2 A2| ≤ _
  have hleft :
      (∑ k : Fin n, (A1 k * B2 k + B1 k * A2 k)) =
        ∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hleft] at hcore
  refine le_trans hcore ?_
  apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hvalid)
  apply Finset.sum_le_sum
  intro k _
  have hsumA : |A1 k + A2 k| ≤ |A1 k| + |A2 k| := abs_add_le _ _
  have hsumB : |B1 k + B2 k| ≤ |B1 k| + |B2 k| := abs_add_le _ _
  have hprod : |A1 k + A2 k| * |B1 k + B2 k| ≤
      (|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) :=
    mul_le_mul hsumA hsumB (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  nlinarith [abs_nonneg (A1 k), abs_nonneg (A2 k),
    abs_nonneg (B1 k), abs_nonneg (B2 k)]

/-- Equation (23.22) with the printed `(n+4)u` term and a genuine explicit
quadratic remainder. -/
theorem higham23_eq23_22_threeM_imaginary_firstOrder (fp : FPModel) {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (hvalid : gammaValid fp (n + 4)) :
    |(∑ k : Fin n, (A1 k * B2 k + A2 k * B1 k)) -
        higham23FlThreeMImaginary fp A1 A2 B1 B2| ≤
      ((n + 4 : ℕ) : ℝ) * fp.u *
          (∑ k : Fin n,
            ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
              |A1 k| * |B1 k| + |A2 k| * |B2 k|)) +
        higham23GammaRemainder (n + 4) fp.u *
          (∑ k : Fin n,
            ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
              |A1 k| * |B1 k| + |A2 k| * |B2 k|)) :=
  higham23_error_bound_gamma_split fp (n + 4) _ _ hvalid
    (higham23_eq23_22_threeM_imaginary_error fp A1 A2 B1 B2 hvalid)

/-- The componentwise budget in (23.22). -/
noncomputable def higham23ThreeMImaginaryBudget {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n,
    ((|A1 k| + |A2 k|) * (|B1 k| + |B2 k|) +
      |A1 k| * |B1 k| + |A2 k| * |B2 k|)

/-- One product term is invariant under cancellation of a positive middle
diagonal scaling and acquires only the outside row/column scale. -/
theorem higham23_abs_product_diagonal_scaling
    {l r s a b : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) (hs : 0 < s) :
    |l * a * s| * |s⁻¹ * b * r| = l * r * (|a| * |b|) := by
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hl,
    abs_of_nonneg hr, abs_of_pos hs, abs_inv, abs_of_pos hs]
  field_simp [ne_of_gt hs]

/-- Precise prose after (23.22): the complete leading 3M budget scales as
`D1 * budget * D3`; since the explicit gamma remainder multiplies the same
budget, the hidden second-order family has the identical invariance. -/
theorem higham23_threeM_budget_diagonal_scaling {n : ℕ}
    (A1 A2 B1 B2 : Fin n → ℝ) (l r : ℝ) (s : Fin n → ℝ)
    (hl : 0 ≤ l) (hr : 0 ≤ r) (hs : ∀ k, 0 < s k) :
    higham23ThreeMImaginaryBudget
        (fun k ↦ l * A1 k * s k) (fun k ↦ l * A2 k * s k)
        (fun k ↦ (s k)⁻¹ * B1 k * r) (fun k ↦ (s k)⁻¹ * B2 k * r) =
      l * r * higham23ThreeMImaginaryBudget A1 A2 B1 B2 := by
  unfold higham23ThreeMImaginaryBudget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h11 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A1 k) (b := B1 k)
  have h12 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A1 k) (b := B2 k)
  have h21 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A2 k) (b := B1 k)
  have h22 := higham23_abs_product_diagonal_scaling hl hr (hs k)
    (a := A2 k) (b := B2 k)
  rw [mul_add, add_mul]
  nlinarith

/-! ### Normwise complex-multiplication consequences -/

/-- The exact imaginary part of the complex matrix product `A * B`. -/
noncomputable def higham23ComplexProductImaginary {n : ℕ}
    (A B : CMatrix n n) (i j : Fin n) : ℝ :=
  ∑ k : Fin n,
    ((A i k).re * (B k j).im + (A i k).im * (B k j).re)

/-- The conventional rounded path for every entry of the imaginary part. -/
noncomputable def higham23FlConventionalImaginaryMatrix (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (i j : Fin n) : ℝ :=
  higham23FlConventionalImaginary fp
    (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
    (fun k ↦ (B k j).re) (fun k ↦ (B k j).im)

/-- The rounded 3M path for every entry of the imaginary part. -/
noncomputable def higham23FlThreeMImaginaryMatrix (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (i j : Fin n) : ℝ :=
  higham23FlThreeMImaginary fp
    (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
    (fun k ↦ (B k j).re) (fun k ↦ (B k j).im)

/-- A row of the conventional componentwise budget is bounded by twice the
product of the two induced infinity norms. -/
theorem higham23_conventional_imaginary_budget_row_le {n : ℕ}
    (A B : CMatrix n n) (i : Fin n) :
    (∑ j : Fin n, ∑ k : Fin n,
        (|(A i k).re| * |(B k j).im| +
          |(A i k).im| * |(B k j).re|)) ≤
      2 * complexMatrixInfNorm A * complexMatrixInfNorm B := by
  have hBnonneg : 0 ≤ complexMatrixInfNorm B := complexMatrixInfNorm_nonneg B
  have hBre : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).re|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_re_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hBim : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).im|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_im_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hAre : (∑ k : Fin n, |(A i k).re|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_re_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  have hAim : (∑ k : Fin n, |(A i k).im|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_im_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  calc
    (∑ j : Fin n, ∑ k : Fin n,
        (|(A i k).re| * |(B k j).im| + |(A i k).im| * |(B k j).re|)) =
        ∑ k : Fin n,
          (|(A i k).re| * (∑ j : Fin n, |(B k j).im|) +
            |(A i k).im| * (∑ j : Fin n, |(B k j).re|)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ k : Fin n,
        (|(A i k).re| * complexMatrixInfNorm B +
          |(A i k).im| * complexMatrixInfNorm B) := by
      apply Finset.sum_le_sum
      intro k _
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hBim k) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hBre k) (abs_nonneg _))
    _ = ((∑ k : Fin n, |(A i k).re|) +
          ∑ k : Fin n, |(A i k).im|) * complexMatrixInfNorm B := by
      rw [add_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    _ ≤ (complexMatrixInfNorm A + complexMatrixInfNorm A) *
        complexMatrixInfNorm B :=
      mul_le_mul_of_nonneg_right (add_le_add hAre hAim) hBnonneg
    _ = 2 * complexMatrixInfNorm A * complexMatrixInfNorm B := by ring

/-- The elementary `√2` weakening used between (23.22) and (23.24). -/
theorem higham23_abs_re_add_abs_im_le_sqrt_two_mul_norm (z : ℂ) :
    |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg _
  have hxy : |z.re| ^ 2 + |z.im| ^ 2 = ‖z‖ ^ 2 := by
    simpa [Complex.normSq, pow_two] using Complex.normSq_eq_norm_sq z
  have hsq : (|z.re| + |z.im|) ^ 2 ≤
      (Real.sqrt 2 * ‖z‖) ^ 2 := by
    rw [mul_pow, hsqrtSq, ← hxy]
    nlinarith [sq_nonneg (|z.re| - |z.im|)]
  exact (sq_le_sq₀
    (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg hsqrt hnorm)).mp hsq

/-- A row of the 3M budget is bounded by four times the product of the induced
infinity norms, exactly the weakening used for equation (23.24). -/
theorem higham23_threeM_imaginary_budget_row_le {n : ℕ}
    (A B : CMatrix n n) (i : Fin n) :
    (∑ j : Fin n, ∑ k : Fin n,
      ((|(A i k).re| + |(A i k).im|) *
          (|(B k j).re| + |(B k j).im|) +
        |(A i k).re| * |(B k j).re| +
        |(A i k).im| * |(B k j).im|)) ≤
      4 * complexMatrixInfNorm A * complexMatrixInfNorm B := by
  let s : ℝ := Real.sqrt 2
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = 2 := by dsimp [s]; norm_num
  have hAn : 0 ≤ complexMatrixInfNorm A := complexMatrixInfNorm_nonneg A
  have hBn : 0 ≤ complexMatrixInfNorm B := complexMatrixInfNorm_nonneg B
  have hAri : (∑ k : Fin n, (|(A i k).re| + |(A i k).im|)) ≤
      s * complexMatrixInfNorm A := by
    calc
      _ ≤ ∑ k : Fin n, s * ‖A i k‖ := by
        apply Finset.sum_le_sum
        intro k _
        exact higham23_abs_re_add_abs_im_le_sqrt_two_mul_norm (A i k)
      _ = s * (∑ k : Fin n, ‖A i k‖) := by rw [Finset.mul_sum]
      _ ≤ s * complexMatrixInfNorm A :=
        mul_le_mul_of_nonneg_left (complexMatrixInfNorm_row_sum_le A i) hs
  have hBri : ∀ k : Fin n,
      (∑ j : Fin n, (|(B k j).re| + |(B k j).im|)) ≤
        s * complexMatrixInfNorm B := by
    intro k
    calc
      _ ≤ ∑ j : Fin n, s * ‖B k j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact higham23_abs_re_add_abs_im_le_sqrt_two_mul_norm (B k j)
      _ = s * (∑ j : Fin n, ‖B k j‖) := by rw [Finset.mul_sum]
      _ ≤ s * complexMatrixInfNorm B :=
        mul_le_mul_of_nonneg_left (complexMatrixInfNorm_row_sum_le B k) hs
  have hAre : (∑ k : Fin n, |(A i k).re|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_re_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  have hAim : (∑ k : Fin n, |(A i k).im|) ≤ complexMatrixInfNorm A :=
    le_trans (Finset.sum_le_sum (fun k _ ↦ Complex.abs_im_le_norm (A i k)))
      (complexMatrixInfNorm_row_sum_le A i)
  have hBre : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).re|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_re_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hBim : ∀ k : Fin n,
      (∑ j : Fin n, |(B k j).im|) ≤ complexMatrixInfNorm B := by
    intro k
    exact le_trans (Finset.sum_le_sum (fun j _ ↦ Complex.abs_im_le_norm (B k j)))
      (complexMatrixInfNorm_row_sum_le B k)
  have hsplit :
      (∑ j : Fin n, ∑ k : Fin n,
        ((|(A i k).re| + |(A i k).im|) *
            (|(B k j).re| + |(B k j).im|) +
          |(A i k).re| * |(B k j).re| +
          |(A i k).im| * |(B k j).im|)) =
        ∑ k : Fin n,
          ((|(A i k).re| + |(A i k).im|) *
              (∑ j : Fin n, (|(B k j).re| + |(B k j).im|)) +
            |(A i k).re| * (∑ j : Fin n, |(B k j).re|) +
            |(A i k).im| * (∑ j : Fin n, |(B k j).im|)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hsplit]
  calc
    _ ≤ ∑ k : Fin n,
        ((|(A i k).re| + |(A i k).im|) * (s * complexMatrixInfNorm B) +
          |(A i k).re| * complexMatrixInfNorm B +
          |(A i k).im| * complexMatrixInfNorm B) := by
      apply Finset.sum_le_sum
      intro k _
      gcongr
      · exact hBri k
      · exact hBre k
      · exact hBim k
    _ = ((∑ k : Fin n, (|(A i k).re| + |(A i k).im|)) *
          (s * complexMatrixInfNorm B) +
        (∑ k : Fin n, |(A i k).re|) * complexMatrixInfNorm B +
        (∑ k : Fin n, |(A i k).im|) * complexMatrixInfNorm B) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    _ ≤ (s * complexMatrixInfNorm A) * (s * complexMatrixInfNorm B) +
        complexMatrixInfNorm A * complexMatrixInfNorm B +
        complexMatrixInfNorm A * complexMatrixInfNorm B := by
      gcongr
    _ = 4 * complexMatrixInfNorm A * complexMatrixInfNorm B := by
      calc
        _ = (s * s + 2) * complexMatrixInfNorm A * complexMatrixInfNorm B := by ring
        _ = _ := by rw [hs2]; ring

/-- Equation (23.23), in an exact-gamma form for the actual rounded
conventional imaginary-part matrix. -/
theorem higham23_eq23_23_conventional_imaginary_normwise (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (hvalid : gammaValid fp (n + 1)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlConventionalImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      2 * gamma fp (n + 1) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (gamma_nonneg fp hvalid))
        (complexMatrixInfNorm_nonneg A))
      (complexMatrixInfNorm_nonneg B)
  intro i
  calc
    (∑ j : Fin n, ‖((higham23ComplexProductImaginary A B i j -
        higham23FlConventionalImaginaryMatrix fp A B i j : ℝ) : ℂ)‖) =
        ∑ j : Fin n, |higham23ComplexProductImaginary A B i j -
          higham23FlConventionalImaginaryMatrix fp A B i j| := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin n, gamma fp (n + 1) *
        (∑ k : Fin n,
          (|(A i k).re| * |(B k j).im| +
            |(A i k).im| * |(B k j).re|)) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [higham23ComplexProductImaginary,
        higham23FlConventionalImaginaryMatrix] using
        higham23_eq23_21_conventional_imaginary_error fp
          (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
          (fun k ↦ (B k j).re) (fun k ↦ (B k j).im) hvalid
    _ = gamma fp (n + 1) *
        (∑ j : Fin n, ∑ k : Fin n,
          (|(A i k).re| * |(B k j).im| +
            |(A i k).im| * |(B k j).re|)) := by rw [Finset.mul_sum]
    _ ≤ gamma fp (n + 1) *
        (2 * complexMatrixInfNorm A * complexMatrixInfNorm B) :=
      mul_le_mul_of_nonneg_left
        (higham23_conventional_imaginary_budget_row_le A B i)
        (gamma_nonneg fp hvalid)
    _ = 2 * gamma fp (n + 1) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by ring

/-- Equation (23.24), in an exact-gamma form for the actual rounded 3M
imaginary-part matrix. -/
theorem higham23_eq23_24_threeM_imaginary_normwise (fp : FPModel) {n : ℕ}
    (A B : CMatrix n n) (hvalid : gammaValid fp (n + 4)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlThreeMImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      4 * gamma fp (n + 4) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (gamma_nonneg fp hvalid))
        (complexMatrixInfNorm_nonneg A))
      (complexMatrixInfNorm_nonneg B)
  intro i
  calc
    (∑ j : Fin n, ‖((higham23ComplexProductImaginary A B i j -
        higham23FlThreeMImaginaryMatrix fp A B i j : ℝ) : ℂ)‖) =
        ∑ j : Fin n, |higham23ComplexProductImaginary A B i j -
          higham23FlThreeMImaginaryMatrix fp A B i j| := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin n, gamma fp (n + 4) *
        (∑ k : Fin n,
          ((|(A i k).re| + |(A i k).im|) *
              (|(B k j).re| + |(B k j).im|) +
            |(A i k).re| * |(B k j).re| +
            |(A i k).im| * |(B k j).im|)) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [higham23ComplexProductImaginary,
        higham23FlThreeMImaginaryMatrix] using
        higham23_eq23_22_threeM_imaginary_error fp
          (fun k ↦ (A i k).re) (fun k ↦ (A i k).im)
          (fun k ↦ (B k j).re) (fun k ↦ (B k j).im) hvalid
    _ = gamma fp (n + 4) *
        (∑ j : Fin n, ∑ k : Fin n,
          ((|(A i k).re| + |(A i k).im|) *
              (|(B k j).re| + |(B k j).im|) +
            |(A i k).re| * |(B k j).re| +
            |(A i k).im| * |(B k j).im|)) := by rw [Finset.mul_sum]
    _ ≤ gamma fp (n + 4) *
        (4 * complexMatrixInfNorm A * complexMatrixInfNorm B) :=
      mul_le_mul_of_nonneg_left
        (higham23_threeM_imaginary_budget_row_le A B i)
        (gamma_nonneg fp hvalid)
    _ = 4 * gamma fp (n + 4) *
        complexMatrixInfNorm A * complexMatrixInfNorm B := by ring

/-- Equation (23.23) with the printed first-order coefficient and an explicit
quadratic remainder. -/
theorem higham23_eq23_23_conventional_imaginary_normwise_firstOrder
    (fp : FPModel) {n : ℕ} (A B : CMatrix n n)
    (hvalid : gammaValid fp (n + 1)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlConventionalImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      2 * ((n + 1 : ℕ) : ℝ) * fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B +
        2 * higham23GammaRemainder (n + 1) fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B := by
  calc
    _ ≤ 2 * gamma fp (n + 1) *
        complexMatrixInfNorm A * complexMatrixInfNorm B :=
      higham23_eq23_23_conventional_imaginary_normwise fp A B hvalid
    _ = _ := by rw [higham23_gamma_split fp (n + 1) hvalid]; ring

/-- Equation (23.24) with the printed first-order coefficient and explicit
quadratic remainder. -/
theorem higham23_eq23_24_threeM_imaginary_normwise_firstOrder
    (fp : FPModel) {n : ℕ} (A B : CMatrix n n)
    (hvalid : gammaValid fp (n + 4)) :
    complexMatrixInfNorm (fun i j ↦
        ((higham23ComplexProductImaginary A B i j -
          higham23FlThreeMImaginaryMatrix fp A B i j : ℝ) : ℂ)) ≤
      4 * ((n + 4 : ℕ) : ℝ) * fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B +
        4 * higham23GammaRemainder (n + 4) fp.u *
          complexMatrixInfNorm A * complexMatrixInfNorm B := by
  calc
    _ ≤ 4 * gamma fp (n + 4) *
        complexMatrixInfNorm A * complexMatrixInfNorm B :=
      higham23_eq23_24_threeM_imaginary_normwise fp A B hvalid
    _ = _ := by rw [higham23_gamma_split fp (n + 4) hvalid]; ring

end ThreeM

section ErrorRecurrences

/-- Canonical exact coefficient generated by the Strassen proof recurrence,
indexed by recursion depth above the threshold `2^r`. -/
noncomputable def higham23StrassenErrorCoefficient (r : ℕ) : ℕ → ℝ
  | 0 => (4 : ℝ) ^ r
  | depth + 1 =>
      12 * higham23StrassenErrorCoefficient r depth +
        46 * (2 : ℝ) ^ (r + depth)

@[simp]
theorem higham23_strassenErrorCoefficient_zero (r : ℕ) :
    higham23StrassenErrorCoefficient r 0 = (4 : ℝ) ^ r := rfl

/-- Equation (23.16) for the canonical coefficient rather than a supplied
recurrence certificate. -/
theorem higham23_eq23_16_strassen_coefficient (r depth : ℕ) :
    higham23StrassenErrorCoefficient r (depth + 1) =
      12 * higham23StrassenErrorCoefficient r depth +
        46 * (2 : ℝ) ^ (r + depth) := rfl

/-- Closed source coefficient in (23.14), proved as an upper bound for the
exact recurrence. -/
theorem higham23_strassenErrorCoefficient_le (r depth : ℕ) :
    higham23StrassenErrorCoefficient r depth ≤
      (12 : ℝ) ^ depth * ((4 : ℝ) ^ r + 5 * (2 : ℝ) ^ r) -
        5 * (2 : ℝ) ^ (r + depth) := by
  induction depth with
  | zero => simp [higham23StrassenErrorCoefficient]
  | succ depth ih =>
      rw [higham23_eq23_16_strassen_coefficient]
      calc
        12 * higham23StrassenErrorCoefficient r depth +
            46 * (2 : ℝ) ^ (r + depth) ≤
          12 * ((12 : ℝ) ^ depth * ((4 : ℝ) ^ r + 5 * (2 : ℝ) ^ r) -
            5 * (2 : ℝ) ^ (r + depth)) +
              46 * (2 : ℝ) ^ (r + depth) := by nlinarith
        _ ≤ (12 : ℝ) ^ (depth + 1) *
              ((4 : ℝ) ^ r + 5 * (2 : ℝ) ^ r) -
            5 * (2 : ℝ) ^ (r + (depth + 1)) := by
          rw [← Nat.add_assoc, pow_succ, pow_succ]
          have hp : 0 ≤ (2 : ℝ) ^ (r + depth) := by positivity
          nlinarith

/-- Canonical Winograd--Strassen error coefficient. -/
noncomputable def higham23WinogradStrassenErrorCoefficient (r : ℕ) : ℕ → ℝ
  | 0 => (4 : ℝ) ^ r
  | depth + 1 =>
      18 * higham23WinogradStrassenErrorCoefficient r depth +
        89 * (2 : ℝ) ^ (r + depth)

@[simp]
theorem higham23_winogradStrassenErrorCoefficient_zero (r : ℕ) :
    higham23WinogradStrassenErrorCoefficient r 0 = (4 : ℝ) ^ r := rfl

theorem higham23_winogradStrassenErrorCoefficient_step (r depth : ℕ) :
    higham23WinogradStrassenErrorCoefficient r (depth + 1) =
      18 * higham23WinogradStrassenErrorCoefficient r depth +
        89 * (2 : ℝ) ^ (r + depth) := rfl

/-- Closed coefficient displayed in (23.18). -/
theorem higham23_winogradStrassenErrorCoefficient_le (r depth : ℕ) :
    higham23WinogradStrassenErrorCoefficient r depth ≤
      (18 : ℝ) ^ depth * ((4 : ℝ) ^ r + 6 * (2 : ℝ) ^ r) -
        6 * (2 : ℝ) ^ (r + depth) := by
  induction depth with
  | zero => simp [higham23WinogradStrassenErrorCoefficient]
  | succ depth ih =>
      rw [higham23_winogradStrassenErrorCoefficient_step]
      calc
        18 * higham23WinogradStrassenErrorCoefficient r depth +
            89 * (2 : ℝ) ^ (r + depth) ≤
          18 * ((18 : ℝ) ^ depth * ((4 : ℝ) ^ r + 6 * (2 : ℝ) ^ r) -
            6 * (2 : ℝ) ^ (r + depth)) +
              89 * (2 : ℝ) ^ (r + depth) := by nlinarith
        _ ≤ (18 : ℝ) ^ (depth + 1) *
              ((4 : ℝ) ^ r + 6 * (2 : ℝ) ^ r) -
            6 * (2 : ℝ) ^ (r + (depth + 1)) := by
          rw [← Nat.add_assoc, pow_succ, pow_succ]
          have hp : 0 ≤ (2 : ℝ) ^ (r + depth) := by positivity
          nlinarith

/-- The canonical Strassen coefficient is nonnegative at every depth. -/
theorem higham23_strassenErrorCoefficient_nonneg (r depth : ℕ) :
    0 ≤ higham23StrassenErrorCoefficient r depth := by
  induction depth with
  | zero => simp [higham23StrassenErrorCoefficient]
  | succ depth ih =>
      rw [higham23_eq23_16_strassen_coefficient]
      positivity

/-- The canonical Winograd--Strassen coefficient is nonnegative. -/
theorem higham23_winogradStrassenErrorCoefficient_nonneg (r depth : ℕ) :
    0 ≤ higham23WinogradStrassenErrorCoefficient r depth := by
  induction depth with
  | zero => simp [higham23WinogradStrassenErrorCoefficient]
  | succ depth ih =>
      rw [higham23_winogradStrassenErrorCoefficient_step]
      positivity

/-- The closed coefficient printed in equation (23.14), with
`n₀ = 2^r` and recursion depth `depth`. -/
noncomputable def higham23StrassenClosedCoefficient (r depth : ℕ) : ℝ :=
  (12 : ℝ) ^ depth * ((4 : ℝ) ^ r + 5 * (2 : ℝ) ^ r) -
    5 * (2 : ℝ) ^ (r + depth)

/-- The closed coefficient printed in equation (23.18). -/
noncomputable def higham23WinogradStrassenClosedCoefficient
    (r depth : ℕ) : ℝ :=
  (18 : ℝ) ^ depth * ((4 : ℝ) ^ r + 6 * (2 : ℝ) ^ r) -
    6 * (2 : ℝ) ^ (r + depth)

theorem higham23_strassenClosedCoefficient_nonneg (r depth : ℕ) :
    0 ≤ higham23StrassenClosedCoefficient r depth :=
  le_trans (higham23_strassenErrorCoefficient_nonneg r depth)
    (by simpa [higham23StrassenClosedCoefficient] using
      higham23_strassenErrorCoefficient_le r depth)

theorem higham23_winogradStrassenClosedCoefficient_nonneg (r depth : ℕ) :
    0 ≤ higham23WinogradStrassenClosedCoefficient r depth :=
  le_trans (higham23_winogradStrassenErrorCoefficient_nonneg r depth)
    (by simpa [higham23WinogradStrassenClosedCoefficient] using
      higham23_winogradStrassenErrorCoefficient_le r depth)

/-! ## Scalar coefficient foundations for downstream evaluator theorems

The definitions below isolate the source coefficient shapes.  Literal
rounded Strassen, Winograd--Strassen, Miller, Bini--Lotti, and combined
3M--Strassen error theorems are proved in the downstream Chapter 23 modules;
none accepts a target-bearing first-order expansion as a substitute for an
actual evaluator. -/

/-- Algebraic form of the coefficient in (23.19) when `n = h^depth`:
`n^(log_h beta) log_h n = beta^depth * depth`.  The retained `h` argument
records the blocking base even though it cancels from this algebraic form. -/
noncomputable def higham23BiniLottiCoefficient
    (alpha beta : ℝ) (_h depth : ℕ) : ℝ :=
  alpha * beta ^ depth * (depth : ℝ)

theorem higham23_biniLottiCoefficient_nonneg
    (alpha beta : ℝ) (h depth : ℕ)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta) :
    0 ≤ higham23BiniLottiCoefficient alpha beta h depth := by
  unfold higham23BiniLottiCoefficient
  positivity

/-- The scalar coefficient described at the end of §23.2.4 for 3M with
Strassen.  `Higham23ThreeMStrassen` proves it for the implemented combined
evaluator. -/
noncomputable def higham23ThreeMStrassenCoefficient (r depth : ℕ) : ℝ :=
  6 * (higham23StrassenClosedCoefficient r depth + 4)

theorem higham23_threeMStrassenCoefficient_nonneg (r depth : ℕ) :
    0 ≤ higham23ThreeMStrassenCoefficient r depth := by
  unfold higham23ThreeMStrassenCoefficient
  exact mul_nonneg (by norm_num)
    (add_nonneg (higham23_strassenClosedCoefficient_nonneg r depth) (by norm_num))

/-- Equation (23.16), re-exported with the correct chapter label from the
existing recurrence foundation. -/
theorem higham23_eq23_16_strassen_step
    (r : ℕ) (c : ℕ → ℝ) (hrec : StrassenRecurrence r c)
    (k : ℕ) (hk : r < k) :
    c k = 12 * c (k - 1) + 46 * (2 : ℝ) ^ (k - 1) :=
  hrec.step k hk

/-- Recurrence following equation (23.18), for Winograd--Strassen. -/
theorem higham23_winogradStrassen_error_step
    (r : ℕ) (c : ℕ → ℝ) (hrec : WinogradStrassenRecurrence r c)
    (k : ℕ) (hk : r < k) :
    c k = 18 * c (k - 1) + 89 * (2 : ℝ) ^ (k - 1) :=
  hrec.step k hk

end ErrorRecurrences

end NumStability
