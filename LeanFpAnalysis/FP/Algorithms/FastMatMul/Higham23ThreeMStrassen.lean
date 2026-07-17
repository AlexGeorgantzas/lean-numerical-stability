/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QED
-/
import LeanFpAnalysis.FP.Algorithms.FastMatMul.Higham23Bini

namespace LeanFpAnalysis.FP

open scoped Topology
open Filter

/-!
# The combined 3M--Strassen evaluator

This file implements the final construction in Section 23.2.4 literally:
the two complex input sums are rounded, all three real products are computed
by the recursively rounded Strassen evaluator, and both output combinations
are rounded at every scalar leaf.
-/

/-- A complex recursive matrix represented by its real and imaginary parts. -/
abbrev Higham23RecursiveComplex (r depth : ℕ) :=
  Higham23RecursiveMatrix r depth × Higham23RecursiveMatrix r depth

/-- Exact complex multiplication, written in the three-multiplication form. -/
noncomputable def higham23ThreeMExactRecursive (r depth : ℕ)
    (A B : Higham23RecursiveComplex r depth) : Higham23RecursiveComplex r depth :=
  higham23ThreeM A.1 A.2 B.1 B.2

/-- Literal 3M implementation whose three real products are actual recursive
Strassen calls. -/
noncomputable def higham23FlThreeMStrassen (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveComplex r depth) : Higham23RecursiveComplex r depth :=
  let As := higham23RecursiveFlAdd fp r depth A.1 A.2
  let Bs := higham23RecursiveFlAdd fp r depth B.1 B.2
  let P1 := higham23FlStrassenRecursive fp r depth A.1 B.1
  let P2 := higham23FlStrassenRecursive fp r depth A.2 B.2
  let P3 := higham23FlStrassenRecursive fp r depth As Bs
  (higham23RecursiveFlSub fp r depth P1 P2,
    higham23RecursiveFlSub fp r depth
      (higham23RecursiveFlSub fp r depth P3 P1) P2)

def Higham23RecursiveComplexErrorLe (r depth : ℕ)
    (X Y : Higham23RecursiveComplex r depth) (re im : ℝ) : Prop :=
  Higham23RecursiveErrorLe r depth X.1 Y.1 re ∧
    Higham23RecursiveErrorLe r depth X.2 Y.2 im

/-- Leafwise rounded addition can use a direct bound on the exact sum.  This
is the form needed for `|A₁|+|A₂| ≤ √2 |A₁+iA₂|`. -/
theorem higham23_recursiveFlAdd_error_of_sum_norm
    (fp : FPModel) (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (s : ℝ),
      0 ≤ s → Higham23RecursiveMaxNormLe r depth (A + B) s →
      Higham23RecursiveErrorLe r depth (A + B)
        (higham23RecursiveFlAdd fp r depth A B) (fp.u * s)
  | 0, A, B, s, hs, hSum => by
      intro i j
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add (A i j) (B i j)
      change |A i j + B i j - fp.fl_add (A i j) (B i j)| ≤ fp.u * s
      rw [hfl, show A i j + B i j - (A i j + B i j) * (1 + δ) =
        -(A i j + B i j) * δ by ring, abs_mul, abs_neg]
      calc
        |A i j + B i j| * |δ| ≤ s * fp.u :=
          mul_le_mul (hSum i j) hδ (abs_nonneg _) hs
        _ = fp.u * s := by ring
  | depth + 1, A, B, s, hs, hSum => by
      rcases hSum with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h11,
        higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h12,
        higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h21,
        higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h22⟩

theorem higham23_recursiveFlAdd_norm_of_sum_norm
    (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (s : ℝ) (hs : 0 ≤ s)
    (hSum : Higham23RecursiveMaxNormLe r depth (A + B) s) :
    Higham23RecursiveMaxNormLe r depth
      (higham23RecursiveFlAdd fp r depth A B) ((1 + fp.u) * s) := by
  have hErr := higham23_recursiveFlAdd_error_of_sum_norm fp r depth A B s hs hSum
  have hNorm := higham23_recursiveMaxNormLe_of_error r depth _ _ hSum hErr
  convert hNorm using 1 <;> ring

noncomputable def higham23ThreeMStrassenP3Error (n e u : ℝ) : ℝ :=
  2 * (n * u + n * u * (1 + u) + e * (1 + u) ^ 2)

noncomputable def higham23ThreeMStrassenP1Norm (n e : ℝ) : ℝ := n + e

noncomputable def higham23ThreeMStrassenP3Norm (n e u : ℝ) : ℝ :=
  2 * (n + e) * (1 + u) ^ 2

noncomputable def higham23ThreeMStrassenRealMajorant (n e u : ℝ) : ℝ :=
  2 * e + 2 * u * higham23ThreeMStrassenP1Norm n e

noncomputable def higham23ThreeMStrassenImagMajorant (n e u : ℝ) : ℝ :=
  let n1 := higham23ThreeMStrassenP1Norm n e
  let n3 := higham23ThreeMStrassenP3Norm n e u
  higham23ThreeMStrassenP3Error n e u + 2 * e +
    u * (n3 + n1) + u * ((1 + u) * (n3 + n1) + n1)

/-- Exact nonlinear error theorem for the actual combined evaluator.  The
`sA*sB ≤ 2*a*b` hypothesis is the scalar form of the source inequality
`(|A₁|+|A₂|)(|B₁|+|B₂|) ≤ 2|A||B|`. -/
theorem higham23_threeMStrassen_exactMajorant
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveComplex r depth) (a b sA sB : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hA1 : Higham23RecursiveMaxNormLe r depth A.1 a)
    (hA2 : Higham23RecursiveMaxNormLe r depth A.2 a)
    (hB1 : Higham23RecursiveMaxNormLe r depth B.1 b)
    (hB2 : Higham23RecursiveMaxNormLe r depth B.2 b)
    (hAsum : Higham23RecursiveMaxNormLe r depth (A.1 + A.2) sA)
    (hBsum : Higham23RecursiveMaxNormLe r depth (B.1 + B.2) sB)
    (hSumProduct : sA * sB ≤ 2 * a * b) :
    let n : ℝ := ((2 ^ (r + depth) : ℕ) : ℝ)
    let e := higham23StrassenExactMajorant fp r depth
    Higham23RecursiveComplexErrorLe r depth
      (higham23ThreeMExactRecursive r depth A B)
      (higham23FlThreeMStrassen fp r depth A B)
      (higham23ThreeMStrassenRealMajorant n e fp.u * a * b)
      (higham23ThreeMStrassenImagMajorant n e fp.u * a * b) := by
  dsimp only
  let n : ℝ := ((2 ^ (r + depth) : ℕ) : ℝ)
  let e := higham23StrassenExactMajorant fp r depth
  let u := fp.u
  let As := higham23RecursiveFlAdd fp r depth A.1 A.2
  let Bs := higham23RecursiveFlAdd fp r depth B.1 B.2
  let P1 := higham23FlStrassenRecursive fp r depth A.1 B.1
  let P2 := higham23FlStrassenRecursive fp r depth A.2 B.2
  let P3 := higham23FlStrassenRecursive fp r depth As Bs
  let Q := (A.1 + A.2) * (B.1 + B.2)
  let N1 := higham23ThreeMStrassenP1Norm n e
  let T := higham23ThreeMStrassenP3Error n e u
  let N3 := higham23ThreeMStrassenP3Norm n e u
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have he : 0 ≤ e := higham23_strassenExactMajorant_nonneg fp r depth hvalid
  have hu : 0 ≤ u := fp.u_nonneg
  have hu1 : 0 ≤ 1 + u := by linarith
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsprod : 0 ≤ sA * sB := mul_nonneg hsA hsB
  have hN1 : 0 ≤ N1 := by dsimp [N1, higham23ThreeMStrassenP1Norm]; positivity
  have hT : 0 ≤ T := by
    dsimp [T, higham23ThreeMStrassenP3Error]
    positivity
  have hN3 : 0 ≤ N3 := by
    dsimp [N3, higham23ThreeMStrassenP3Norm]
    positivity
  have hAsErr : Higham23RecursiveErrorLe r depth (A.1 + A.2) As (u * sA) := by
    simpa [As, u] using
      higham23_recursiveFlAdd_error_of_sum_norm fp r depth A.1 A.2 sA hsA hAsum
  have hBsErr : Higham23RecursiveErrorLe r depth (B.1 + B.2) Bs (u * sB) := by
    simpa [Bs, u] using
      higham23_recursiveFlAdd_error_of_sum_norm fp r depth B.1 B.2 sB hsB hBsum
  have hAsNorm : Higham23RecursiveMaxNormLe r depth As ((1 + u) * sA) := by
    simpa [As, u] using
      higham23_recursiveFlAdd_norm_of_sum_norm fp r depth A.1 A.2 sA hsA hAsum
  have hBsNorm : Higham23RecursiveMaxNormLe r depth Bs ((1 + u) * sB) := by
    simpa [Bs, u] using
      higham23_recursiveFlAdd_norm_of_sum_norm fp r depth B.1 B.2 sB hsB hBsum
  have hP1err : Higham23RecursiveErrorLe r depth (A.1 * B.1) P1 (e * a * b) := by
    simpa [P1, e] using higham23_theorem23_2_strassen_exactMajorant
      fp r hvalid depth A.1 B.1 a b ha hb hA1 hB1
  have hP2err : Higham23RecursiveErrorLe r depth (A.2 * B.2) P2 (e * a * b) := by
    simpa [P2, e] using higham23_theorem23_2_strassen_exactMajorant
      fp r hvalid depth A.2 B.2 a b ha hb hA2 hB2
  have hP1exact := higham23_recursiveMaxNormLe_mul r depth A.1 B.1 a b ha hb hA1 hB1
  have hP2exact := higham23_recursiveMaxNormLe_mul r depth A.2 B.2 a b ha hb hA2 hB2
  have hP1normRaw := higham23_recursiveMaxNormLe_of_error r depth
    (A.1 * B.1) P1 hP1exact hP1err
  have hP2normRaw := higham23_recursiveMaxNormLe_of_error r depth
    (A.2 * B.2) P2 hP2exact hP2err
  have hP1norm : Higham23RecursiveMaxNormLe r depth P1 (N1 * a * b) := by
    convert hP1normRaw using 1 <;>
      dsimp [N1, n, e, higham23ThreeMStrassenP1Norm] <;> ring
  have hP2norm : Higham23RecursiveMaxNormLe r depth P2 (N1 * a * b) := by
    convert hP2normRaw using 1 <;>
      dsimp [N1, n, e, higham23ThreeMStrassenP1Norm] <;> ring
  have hP3rec : Higham23RecursiveErrorLe r depth (As * Bs) P3
      (e * ((1 + u) * sA) * ((1 + u) * sB)) := by
    simpa [P3, e] using higham23_theorem23_2_strassen_exactMajorant
      fp r hvalid depth As Bs ((1 + u) * sA) ((1 + u) * sB)
      (by positivity) (by positivity) hAsNorm hBsNorm
  have hBsNorm' : Higham23RecursiveMaxNormLe r depth Bs (sB + u * sB) := by
    convert hBsNorm using 1 <;> ring
  have hP3transfer := higham23_recursiveProduct_transfer r depth
    (A.1 + A.2) As (B.1 + B.2) Bs P3
    ((1 + u) * sA) sB (u * sA) (u * sB) e
    (by positivity) hsB (by positivity) (by positivity)
    hAsNorm hBsum hBsNorm'
    (higham23_recursiveErrorLe_symm r depth _ _ hAsErr)
    (higham23_recursiveErrorLe_symm r depth _ _ hBsErr)
    (by convert hP3rec using 1 <;> ring)
  have hP3err : Higham23RecursiveErrorLe r depth Q P3 (T * a * b) := by
    apply higham23_recursiveErrorLe_mono r depth _ _ hP3transfer.1
    have hcore : 0 ≤ n * u + n * u * (1 + u) + e * (1 + u) ^ 2 := by
      positivity
    have hscale := mul_le_mul_of_nonneg_left hSumProduct hcore
    dsimp [Q, T, n, e, u, higham23ThreeMStrassenP3Error] at hscale ⊢
    convert hscale using 1 <;> ring
  have hP3norm : Higham23RecursiveMaxNormLe r depth P3 (N3 * a * b) := by
    apply higham23_recursiveMaxNormLe_mono r depth _ hP3transfer.2
    have hcore : 0 ≤ (n + e) * (1 + u) ^ 2 := by positivity
    have hscale := mul_le_mul_of_nonneg_left hSumProduct hcore
    dsimp [N3, n, e, u, higham23ThreeMStrassenP3Norm] at hscale ⊢
    convert hscale using 1 <;> ring
  have hRealProd := higham23_recursiveErrorLe_sub r depth
    (A.1 * B.1) P1 (A.2 * B.2) P2 hP1err hP2err
  have hRealRound := higham23_recursiveFlSub_error fp r depth P1 P2
    (N1 * a * b) (N1 * a * b) (by positivity) (by positivity) hP1norm hP2norm
  have hRealRaw := higham23_recursiveErrorLe_trans r depth _ _ _ hRealProd hRealRound
  have hReal : Higham23RecursiveErrorLe r depth
      (A.1 * B.1 - A.2 * B.2)
      (higham23RecursiveFlSub fp r depth P1 P2)
      (higham23ThreeMStrassenRealMajorant n e u * a * b) := by
    convert hRealRaw using 1 <;>
      dsimp [N1, higham23ThreeMStrassenRealMajorant,
        higham23ThreeMStrassenP1Norm] <;> ring
  let Q1 := higham23RecursiveFlSub fp r depth P3 P1
  have hQ1prod := higham23_recursiveErrorLe_sub r depth Q P3
    (A.1 * B.1) P1 hP3err hP1err
  have hQ1round := higham23_recursiveFlSub_error fp r depth P3 P1
    (N3 * a * b) (N1 * a * b) (by positivity) (by positivity) hP3norm hP1norm
  have hQ1raw := higham23_recursiveErrorLe_trans r depth _ _ _ hQ1prod hQ1round
  have hQ1 : Higham23RecursiveErrorLe r depth (Q - A.1 * B.1) Q1
      ((T + e + u * (N3 + N1)) * a * b) := by
    convert hQ1raw using 1 <;> dsimp [Q1] <;> ring
  have hQ1normRaw := higham23_recursiveFlSub_norm fp r depth P3 P1
    (N3 * a * b) (N1 * a * b) (by positivity) (by positivity) hP3norm hP1norm
  have hQ1norm : Higham23RecursiveMaxNormLe r depth Q1
      ((1 + u) * (N3 + N1) * a * b) := by
    convert hQ1normRaw using 1 <;> dsimp [Q1] <;> ring
  have hImagProd := higham23_recursiveErrorLe_sub r depth
    (Q - A.1 * B.1) Q1 (A.2 * B.2) P2 hQ1 hP2err
  have hImagRound := higham23_recursiveFlSub_error fp r depth Q1 P2
    ((1 + u) * (N3 + N1) * a * b) (N1 * a * b)
    (by positivity) (by positivity) hQ1norm hP2norm
  have hImagRaw := higham23_recursiveErrorLe_trans r depth _ _ _ hImagProd hImagRound
  have hImag : Higham23RecursiveErrorLe r depth
      (Q - A.1 * B.1 - A.2 * B.2)
      (higham23RecursiveFlSub fp r depth Q1 P2)
      (higham23ThreeMStrassenImagMajorant n e u * a * b) := by
    convert hImagRaw using 1 <;>
      dsimp [higham23ThreeMStrassenImagMajorant, N1, N3, T, Q1] <;> ring
  constructor
  · simpa [Higham23RecursiveComplexErrorLe, higham23ThreeMExactRecursive,
      higham23ThreeM, higham23FlThreeMStrassen, As, Bs, P1, P2, P3,
      n, e, u] using hReal
  · simpa [Higham23RecursiveComplexErrorLe, higham23ThreeMExactRecursive,
      higham23ThreeM, higham23FlThreeMStrassen, As, Bs, P1, P2, P3, Q, Q1,
      n, e, u] using hImag

/-! ### First-order split -/

noncomputable def higham23ThreeMStrassenRealFamily (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenRealMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
    (higham23StrassenMajorantFamily r depth u) u

noncomputable def higham23ThreeMStrassenImagFamily (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenImagMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
    (higham23StrassenMajorantFamily r depth u) u

noncomputable def higham23ThreeMStrassenRealFirstOrder (r depth : ℕ) : ℝ :=
  2 * higham23StrassenErrorCoefficient r depth +
    2 * (((2 ^ (r + depth) : ℕ) : ℝ))

noncomputable def higham23ThreeMStrassenImagFirstOrder (r depth : ℕ) : ℝ :=
  4 * higham23StrassenErrorCoefficient r depth +
    11 * (((2 ^ (r + depth) : ℕ) : ℝ))

noncomputable def higham23ThreeMStrassenRealRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenRealFamily r depth u -
    higham23ThreeMStrassenRealFirstOrder r depth * u

noncomputable def higham23ThreeMStrassenImagRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenImagFamily r depth u -
    higham23ThreeMStrassenImagFirstOrder r depth * u

theorem higham23_threeMStrassenMajorants_eq_families
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    higham23ThreeMStrassenRealMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
        (higham23StrassenExactMajorant fp r depth) fp.u =
      higham23ThreeMStrassenRealFamily r depth fp.u ∧
    higham23ThreeMStrassenImagMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
        (higham23StrassenExactMajorant fp r depth) fp.u =
      higham23ThreeMStrassenImagFamily r depth fp.u := by
  rw [higham23_strassenExactMajorant_eq_family fp r depth hvalid]
  exact ⟨rfl, rfl⟩

theorem higham23_threeMStrassenRemainders_isBigO_u_sq (r depth : ℕ) :
    (fun u : ℝ ↦ higham23ThreeMStrassenRealRemainder r depth u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) ∧
      (fun u : ℝ ↦ higham23ThreeMStrassenImagRemainder r depth u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  let n : ℝ := (((2 ^ (r + depth) : ℕ) : ℝ))
  let c := higham23StrassenErrorCoefficient r depth
  let e : ℝ → ℝ := higham23StrassenMajorantFamily r depth
  let F : ℝ → ℝ := fun u ↦
    higham23ThreeMStrassenP3Norm n (e u) u +
      higham23ThreeMStrassenP1Norm n (e u)
  let G : ℝ → ℝ := fun u ↦
    (1 + u) * F u + higham23ThreeMStrassenP1Norm n (e u)
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_id.isBigO_one ℝ
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [pow_two, mul_one] using hu.mul huOne
  have heR : (fun u : ℝ ↦ e u - c * u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa [e, c, higham23StrassenMajorantRemainder] using
      higham23_strassenMajorantRemainder_isBigO_u_sq r depth
  have he : e =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hsum := (hu.const_mul_left c).add (heR.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [e, c, higham23StrassenMajorantRemainder]
        ring
    · exact Filter.EventuallyEq.rfl
  have heOne := he.trans huOne
  have hue : (fun u : ℝ ↦ u * e u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul he
  have huSqe : (fun u : ℝ ↦ u ^ 2 * e u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [mul_one] using huSq.mul heOne
  have hRealRaw := (heR.const_mul_left 2).add (hue.const_mul_left 2)
  have hReal : (fun u : ℝ ↦ higham23ThreeMStrassenRealRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    apply hRealRaw.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [higham23ThreeMStrassenRealRemainder,
          higham23ThreeMStrassenRealFamily,
          higham23ThreeMStrassenRealFirstOrder,
          higham23ThreeMStrassenRealMajorant,
          higham23ThreeMStrassenP1Norm, n, c, e]
        ring
    · exact Filter.EventuallyEq.rfl
  have hTresRaw :=
    (((huSq.const_mul_left n).add heR).add
      (hue.const_mul_left 2)).add huSqe
  have hTres : (fun u : ℝ ↦
      higham23ThreeMStrassenP3Error n (e u) u - (2 * c + 4 * n) * u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := hTresRaw.const_mul_left 2
    apply h.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [higham23ThreeMStrassenP3Error]
        ring
    · exact Filter.EventuallyEq.rfl
  have hFminus : (fun u : ℝ ↦ F u - 3 * n)
      =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have heuOu := hue.trans huSqOu
    have huSqeOu := huSqe.trans huSqOu
    have hsum :=
      (((he.const_mul_left 3).add (hu.const_mul_left (4 * n))).add
        (heuOu.const_mul_left 4)).add
        ((huSqOu.const_mul_left (2 * n)).add (huSqeOu.const_mul_left 2))
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [F, higham23ThreeMStrassenP3Norm,
          higham23ThreeMStrassenP1Norm]
        ring
    · exact Filter.EventuallyEq.rfl
  have hConst : (fun _ : ℝ ↦ 3 * n) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_const.isBigO_one ℝ
  have hFOne : F =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
    have hsum := (hFminus.trans huOne).add hConst
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by ring
    · exact Filter.EventuallyEq.rfl
  have huF : (fun u : ℝ ↦ u * F u) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [mul_one] using hu.mul hFOne
  have hGminus : (fun u : ℝ ↦ G u - 4 * n)
      =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hsum := (hFminus.add huF).add he
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [G, F, higham23ThreeMStrassenP1Norm]
        ring
    · exact Filter.EventuallyEq.rfl
  have huFminus : (fun u : ℝ ↦ u * (F u - 3 * n))
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul hFminus
  have huGminus : (fun u : ℝ ↦ u * (G u - 4 * n))
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul hGminus
  have hImagRaw := (((hTres.add (heR.const_mul_left 2)).add huFminus).add huGminus)
  have hImag : (fun u : ℝ ↦ higham23ThreeMStrassenImagRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    apply hImagRaw.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [higham23ThreeMStrassenImagRemainder,
          higham23ThreeMStrassenImagFamily,
          higham23ThreeMStrassenImagFirstOrder,
          higham23ThreeMStrassenImagMajorant, F, G, n, c, e]
        ring
    · exact Filter.EventuallyEq.rfl
  exact ⟨hReal, hImag⟩

/-- First-order form for the actual combined evaluator. -/
theorem higham23_threeMStrassen_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveComplex r depth) (a b sA sB : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hA1 : Higham23RecursiveMaxNormLe r depth A.1 a)
    (hA2 : Higham23RecursiveMaxNormLe r depth A.2 a)
    (hB1 : Higham23RecursiveMaxNormLe r depth B.1 b)
    (hB2 : Higham23RecursiveMaxNormLe r depth B.2 b)
    (hAsum : Higham23RecursiveMaxNormLe r depth (A.1 + A.2) sA)
    (hBsum : Higham23RecursiveMaxNormLe r depth (B.1 + B.2) sB)
    (hSumProduct : sA * sB ≤ 2 * a * b) :
    Higham23RecursiveComplexErrorLe r depth
      (higham23ThreeMExactRecursive r depth A B)
      (higham23FlThreeMStrassen fp r depth A B)
      ((higham23ThreeMStrassenRealFirstOrder r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * a * b)
      ((higham23ThreeMStrassenImagFirstOrder r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * a * b) := by
  have hExact := higham23_threeMStrassen_exactMajorant fp r depth hvalid
    A B a b sA sB ha hb hsA hsB hA1 hA2 hB1 hB2 hAsum hBsum hSumProduct
  rcases hExact with ⟨hReal, hImag⟩
  have hFamilies := higham23_threeMStrassenMajorants_eq_families fp r depth hvalid
  rw [hFamilies.1] at hReal
  rw [hFamilies.2] at hImag
  have hRealSplit : higham23ThreeMStrassenRealFamily r depth fp.u =
      higham23ThreeMStrassenRealFirstOrder r depth * fp.u +
        higham23ThreeMStrassenRealRemainder r depth fp.u := by
    unfold higham23ThreeMStrassenRealRemainder
    ring
  have hImagSplit : higham23ThreeMStrassenImagFamily r depth fp.u =
      higham23ThreeMStrassenImagFirstOrder r depth * fp.u +
        higham23ThreeMStrassenImagRemainder r depth fp.u := by
    unfold higham23ThreeMStrassenImagRemainder
    ring
  exact ⟨by simpa [hRealSplit] using hReal, by simpa [hImagSplit] using hImag⟩

theorem higham23_strassenErrorCoefficient_ge_order_sq (r : ℕ) :
    ∀ depth, ((2 : ℝ) ^ (r + depth)) ^ 2 ≤
      higham23StrassenErrorCoefficient r depth
  | 0 => by
      simp [higham23StrassenErrorCoefficient, pow_two, ← mul_pow]
      norm_num
  | depth + 1 => by
      rw [higham23_eq23_16_strassen_coefficient]
      have ih := higham23_strassenErrorCoefficient_ge_order_sq r depth
      have hx : 0 ≤ (2 : ℝ) ^ (r + depth) := by positivity
      have hc := higham23_strassenErrorCoefficient_nonneg r depth
      calc
        ((2 : ℝ) ^ (r + (depth + 1))) ^ 2 =
            4 * ((2 : ℝ) ^ (r + depth)) ^ 2 := by
          rw [show r + (depth + 1) = (r + depth) + 1 by omega, pow_succ]
          ring
        _ ≤ 12 * higham23StrassenErrorCoefficient r depth +
            46 * (2 : ℝ) ^ (r + depth) := by nlinarith

theorem higham23_strassenClosedCoefficient_ge_order_sq (r depth : ℕ) :
    ((2 : ℝ) ^ (r + depth)) ^ 2 ≤ higham23StrassenClosedCoefficient r depth := by
  exact (higham23_strassenErrorCoefficient_ge_order_sq r depth).trans
    (by simpa [higham23StrassenClosedCoefficient] using
      higham23_strassenErrorCoefficient_le r depth)

theorem higham23_threeMStrassenRealFirstOrder_le_source (r depth : ℕ) :
    higham23ThreeMStrassenRealFirstOrder r depth ≤
      higham23ThreeMStrassenCoefficient r depth := by
  let n : ℝ := (2 : ℝ) ^ (r + depth)
  let c := higham23StrassenErrorCoefficient r depth
  let C := higham23StrassenClosedCoefficient r depth
  have hn : 1 ≤ n := by
    dsimp [n]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hC2 : n ^ 2 ≤ C := by
    simpa [n] using higham23_strassenClosedCoefficient_ge_order_sq r depth
  have hcC : c ≤ C := by
    simpa [c, C, higham23StrassenClosedCoefficient] using
      higham23_strassenErrorCoefficient_le r depth
  have hC0 := higham23_strassenClosedCoefficient_nonneg r depth
  dsimp [higham23ThreeMStrassenRealFirstOrder,
    higham23ThreeMStrassenCoefficient, n, c, C]
  norm_num [Nat.cast_pow]
  nlinarith

theorem higham23_threeMStrassenImagFirstOrder_le_source (r depth : ℕ) :
    higham23ThreeMStrassenImagFirstOrder r depth ≤
      higham23ThreeMStrassenCoefficient r depth := by
  let n : ℝ := (2 : ℝ) ^ (r + depth)
  let c := higham23StrassenErrorCoefficient r depth
  let C := higham23StrassenClosedCoefficient r depth
  have hC2 : n ^ 2 ≤ C := by
    simpa [n] using higham23_strassenClosedCoefficient_ge_order_sq r depth
  have hcC : c ≤ C := by
    simpa [c, C, higham23StrassenClosedCoefficient] using
      higham23_strassenErrorCoefficient_le r depth
  have hquad : 11 * n ≤ 2 * n ^ 2 + 24 := by
    nlinarith [sq_nonneg (4 * n - 11)]
  dsimp [higham23ThreeMStrassenImagFirstOrder,
    higham23ThreeMStrassenCoefficient, n, c, C]
  norm_num [Nat.cast_pow]
  nlinarith

/-- The source's combined 3M--Strassen statement: the same (23.14)
coefficient with multiplier six and four added, for the literal evaluator. -/
theorem higham23_threeMStrassen_sourceCoefficient
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveComplex r depth) (a b sA sB : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hA1 : Higham23RecursiveMaxNormLe r depth A.1 a)
    (hA2 : Higham23RecursiveMaxNormLe r depth A.2 a)
    (hB1 : Higham23RecursiveMaxNormLe r depth B.1 b)
    (hB2 : Higham23RecursiveMaxNormLe r depth B.2 b)
    (hAsum : Higham23RecursiveMaxNormLe r depth (A.1 + A.2) sA)
    (hBsum : Higham23RecursiveMaxNormLe r depth (B.1 + B.2) sB)
    (hSumProduct : sA * sB ≤ 2 * a * b) :
    Higham23RecursiveComplexErrorLe r depth
      (higham23ThreeMExactRecursive r depth A B)
      (higham23FlThreeMStrassen fp r depth A B)
      ((higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * a * b)
      ((higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * a * b) := by
  rcases higham23_threeMStrassen_firstOrder fp r depth hvalid
    A B a b sA sB ha hb hsA hsB hA1 hA2 hB1 hB2 hAsum hBsum hSumProduct with
    ⟨hReal, hImag⟩
  constructor
  · apply higham23_recursiveErrorLe_mono r depth _ _ hReal
    have hc := higham23_threeMStrassenRealFirstOrder_le_source r depth
    have hs := mul_le_mul_of_nonneg_right hc fp.u_nonneg
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    calc
      _ = (higham23ThreeMStrassenRealFirstOrder r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * (a * b) := by ring
      _ ≤ (higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * (a * b) :=
        mul_le_mul_of_nonneg_right (add_le_add hs le_rfl) hab
      _ = _ := by ring
  · apply higham23_recursiveErrorLe_mono r depth _ _ hImag
    have hc := higham23_threeMStrassenImagFirstOrder_le_source r depth
    have hs := mul_le_mul_of_nonneg_right hc fp.u_nonneg
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    calc
      _ = (higham23ThreeMStrassenImagFirstOrder r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * (a * b) := by ring
      _ ≤ (higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * (a * b) :=
        mul_le_mul_of_nonneg_right (add_le_add hs le_rfl) hab
      _ = _ := by ring

end LeanFpAnalysis.FP
