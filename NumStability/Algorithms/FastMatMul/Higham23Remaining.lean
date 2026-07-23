/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.FastMatMul.Higham23Recursive

namespace NumStability

open scoped Topology
open Filter

/-!
# Remaining Chapter 23 closure theorems

This file continues the literal recursive analysis of `Higham23Recursive`.
In particular, the Winograd--Strassen result below follows the actual fifteen
rounded additions in (23.6), rather than transferring a scalar recurrence to
an unspecified implementation.
-/

/-- A simultaneously certified error radius and computed max-entry norm. -/
structure Higham23RecursiveCertificate (r depth : ℕ)
    (X Xhat : Higham23RecursiveMatrix r depth) (error norm : ℝ) : Prop where
  error_le : Higham23RecursiveErrorLe r depth X Xhat error
  norm_le : Higham23RecursiveMaxNormLe r depth Xhat norm

theorem higham23_recursiveCertificate_refl (r depth : ℕ)
    (X : Higham23RecursiveMatrix r depth) (x : ℝ)
    (hX : Higham23RecursiveMaxNormLe r depth X x) :
    Higham23RecursiveCertificate r depth X X 0 x :=
  ⟨higham23_recursiveErrorLe_refl r depth X, hX⟩

/-- Certificate composition for one rounded addition. -/
theorem higham23_recursiveCertificate_flAdd
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y Yhat : Higham23RecursiveMatrix r depth)
    (ex nx ey ny : ℝ)
    (hnx : 0 ≤ nx) (hny : 0 ≤ ny)
    (hX : Higham23RecursiveCertificate r depth X Xhat ex nx)
    (hY : Higham23RecursiveCertificate r depth Y Yhat ey ny) :
    Higham23RecursiveCertificate r depth (X + Y)
      (higham23RecursiveFlAdd fp r depth Xhat Yhat)
      (ex + ey + fp.u * (nx + ny)) ((1 + fp.u) * (nx + ny)) := by
  have hlocal := higham23_recursiveFlAdd_error fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le
  have hinput := higham23_recursiveErrorLe_add r depth
    X Xhat Y Yhat hX.error_le hY.error_le
  refine ⟨?_, higham23_recursiveFlAdd_norm fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le⟩
  have h := higham23_recursiveErrorLe_trans r depth _ _ _ hinput hlocal
  exact higham23_recursiveErrorLe_mono r depth _ _ h (by ring_nf; linarith)

/-- Certificate composition for one rounded subtraction. -/
theorem higham23_recursiveCertificate_flSub
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y Yhat : Higham23RecursiveMatrix r depth)
    (ex nx ey ny : ℝ)
    (hnx : 0 ≤ nx) (hny : 0 ≤ ny)
    (hX : Higham23RecursiveCertificate r depth X Xhat ex nx)
    (hY : Higham23RecursiveCertificate r depth Y Yhat ey ny) :
    Higham23RecursiveCertificate r depth (X - Y)
      (higham23RecursiveFlSub fp r depth Xhat Yhat)
      (ex + ey + fp.u * (nx + ny)) ((1 + fp.u) * (nx + ny)) := by
  have hlocal := higham23_recursiveFlSub_error fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le
  have hinput := higham23_recursiveErrorLe_sub r depth
    X Xhat Y Yhat hX.error_le hY.error_le
  refine ⟨?_, higham23_recursiveFlSub_norm fp r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le⟩
  have h := higham23_recursiveErrorLe_trans r depth _ _ _ hinput hlocal
  exact higham23_recursiveErrorLe_mono r depth _ _ h (by ring_nf; linarith)

/-- Feed two prepared-input certificates through a recursively rounded
product whose normalized recursive error coefficient is `e`. -/
theorem higham23_recursiveCertificate_product
    (r depth : ℕ)
    (X Xhat Y Yhat P : Higham23RecursiveMatrix r depth)
    (xExact yExact ex nx ey ny e : ℝ)
    (hxExact : 0 ≤ xExact) (hyExact : 0 ≤ yExact)
    (hex : 0 ≤ ex) (hnx : 0 ≤ nx) (hey : 0 ≤ ey) (hny : 0 ≤ ny)
    (he : 0 ≤ e)
    (hXexact : Higham23RecursiveMaxNormLe r depth X xExact)
    (hYexact : Higham23RecursiveMaxNormLe r depth Y yExact)
    (hX : Higham23RecursiveCertificate r depth X Xhat ex nx)
    (hY : Higham23RecursiveCertificate r depth Y Yhat ey ny)
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Yhat) P
      (e * nx * ny)) :
    let m : ℝ := (2 ^ (r + depth) : ℕ)
    Higham23RecursiveCertificate r depth (X * Y) P
      (m * ex * yExact + m * nx * ey + e * nx * ny)
      ((m + e) * nx * ny) := by
  dsimp only
  let m : ℝ := (2 ^ (r + depth) : ℕ)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hinputComputed := higham23_recursiveErrorLe_mul r depth
    X Xhat Y Yhat nx yExact ex ey hnx hyExact hex hey
    hX.norm_le hYexact
    (higham23_recursiveErrorLe_symm r depth _ _ hX.error_le)
    (higham23_recursiveErrorLe_symm r depth _ _ hY.error_le)
  have hinput := higham23_recursiveErrorLe_symm r depth _ _ hinputComputed
  have herrRaw := higham23_recursiveErrorLe_trans r depth _ _ _ hinput hRec
  have hprodNorm := higham23_recursiveMaxNormLe_mul r depth
    Xhat Yhat nx ny hnx hny hX.norm_le hY.norm_le
  have houtNorm := higham23_recursiveMaxNormLe_of_error r depth
    (Xhat * Yhat) P hprodNorm hRec
  constructor
  · exact higham23_recursiveErrorLe_mono r depth _ _ herrRaw (by
      ring_nf
      linarith)
  · convert houtNorm using 1 <;> dsimp [m] <;> ring

/-! ## Winograd--Strassen radii -/

noncomputable def higham23WinogradN1 (u : ℝ) : ℝ := 2 * (1 + u)
noncomputable def higham23WinogradE1 (u : ℝ) : ℝ := 2 * u
noncomputable def higham23WinogradN2 (u : ℝ) : ℝ :=
  (1 + u) * (higham23WinogradN1 u + 1)
noncomputable def higham23WinogradE2 (u : ℝ) : ℝ :=
  higham23WinogradE1 u + u * (higham23WinogradN1 u + 1)
noncomputable def higham23WinogradN4 (u : ℝ) : ℝ :=
  (1 + u) * (1 + higham23WinogradN2 u)
noncomputable def higham23WinogradE4 (u : ℝ) : ℝ :=
  higham23WinogradE2 u + u * (1 + higham23WinogradN2 u)

noncomputable def higham23WinogradProductError
    (m e nx ny ex ey yExact : ℝ) : ℝ :=
  m * ex * yExact + m * nx * ey + e * nx * ny

noncomputable def higham23WinogradProductNorm
    (m e nx ny : ℝ) : ℝ := (m + e) * nx * ny

noncomputable def higham23WinogradP1Error (m e u : ℝ) : ℝ :=
  higham23WinogradProductError m e
    (higham23WinogradN2 u) (higham23WinogradN2 u)
    (higham23WinogradE2 u) (higham23WinogradE2 u) 3

noncomputable def higham23WinogradP1Norm (m e u : ℝ) : ℝ :=
  higham23WinogradProductNorm m e
    (higham23WinogradN2 u) (higham23WinogradN2 u)

noncomputable def higham23WinogradP4Error (m e u : ℝ) : ℝ :=
  higham23WinogradProductError m e
    (higham23WinogradN1 u) (higham23WinogradN1 u)
    (higham23WinogradE1 u) (higham23WinogradE1 u) 2

noncomputable def higham23WinogradP4Norm (m e u : ℝ) : ℝ :=
  higham23WinogradProductNorm m e
    (higham23WinogradN1 u) (higham23WinogradN1 u)

noncomputable def higham23WinogradP6Error (m e u : ℝ) : ℝ :=
  higham23WinogradProductError m e
    (higham23WinogradN4 u) 1 (higham23WinogradE4 u) 0 1

noncomputable def higham23WinogradP6Norm (m e u : ℝ) : ℝ :=
  higham23WinogradProductNorm m e (higham23WinogradN4 u) 1

noncomputable def higham23WinogradT1Error (m e u : ℝ) : ℝ :=
  higham23WinogradP1Error m e u + e +
    u * (higham23WinogradP1Norm m e u + (m + e))

noncomputable def higham23WinogradT1Norm (m e u : ℝ) : ℝ :=
  (1 + u) * (higham23WinogradP1Norm m e u + (m + e))

noncomputable def higham23WinogradQError (m e u : ℝ) : ℝ :=
  higham23WinogradT1Error m e u + higham23WinogradP4Error m e u +
    u * (higham23WinogradT1Norm m e u + higham23WinogradP4Norm m e u)

noncomputable def higham23WinogradQNorm (m e u : ℝ) : ℝ :=
  (1 + u) * (higham23WinogradT1Norm m e u +
    higham23WinogradP4Norm m e u)

/-- Exact one-level nonlinear majorant generated by the literal dataflow for
`C12` (and identically for `C21`). -/
noncomputable def higham23WinogradStepMajorant (m e u : ℝ) : ℝ :=
  higham23WinogradQError m e u + higham23WinogradP6Error m e u +
    u * (higham23WinogradQNorm m e u + higham23WinogradP6Norm m e u)

noncomputable def higham23WinogradC11Error (m e u : ℝ) : ℝ :=
  e + e + u * ((m + e) + (m + e))

noncomputable def higham23WinogradC22Error (m e u : ℝ) : ℝ :=
  higham23WinogradQError m e u + higham23WinogradP4Error m e u +
    u * (higham23WinogradQNorm m e u + higham23WinogradP4Norm m e u)

noncomputable def higham23WinogradExactMajorant
    (fp : FPModel) (r : ℕ) : ℕ → ℝ
  | 0 => ((2 ^ r : ℕ) : ℝ) * gamma fp (2 ^ r)
  | depth + 1 => higham23WinogradStepMajorant
      ((2 ^ (r + depth) : ℕ) : ℝ)
      (higham23WinogradExactMajorant fp r depth) fp.u

private theorem higham23_winogradRadii_nonneg (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ higham23WinogradN1 u ∧ 0 ≤ higham23WinogradE1 u ∧
    0 ≤ higham23WinogradN2 u ∧ 0 ≤ higham23WinogradE2 u ∧
    0 ≤ higham23WinogradN4 u ∧ 0 ≤ higham23WinogradE4 u := by
  have hN1 : 0 ≤ higham23WinogradN1 u := by
    unfold higham23WinogradN1
    positivity
  have hE1 : 0 ≤ higham23WinogradE1 u := by
    unfold higham23WinogradE1
    positivity
  have hN2 : 0 ≤ higham23WinogradN2 u := by
    unfold higham23WinogradN2
    positivity
  have hE2 : 0 ≤ higham23WinogradE2 u := by
    unfold higham23WinogradE2
    positivity
  have hN4 : 0 ≤ higham23WinogradN4 u := by
    unfold higham23WinogradN4
    positivity
  have hE4 : 0 ≤ higham23WinogradE4 u := by
    unfold higham23WinogradE4
    positivity
  exact ⟨hN1, hE1, hN2, hE2, hN4, hE4⟩

private theorem higham23_winogradScalars_nonneg
    (m e u : ℝ) (hm : 0 ≤ m) (he : 0 ≤ e) (hu : 0 ≤ u) :
    0 ≤ higham23WinogradP1Error m e u ∧
    0 ≤ higham23WinogradP1Norm m e u ∧
    0 ≤ higham23WinogradP4Error m e u ∧
    0 ≤ higham23WinogradP4Norm m e u ∧
    0 ≤ higham23WinogradP6Error m e u ∧
    0 ≤ higham23WinogradP6Norm m e u ∧
    0 ≤ higham23WinogradT1Error m e u ∧
    0 ≤ higham23WinogradT1Norm m e u ∧
    0 ≤ higham23WinogradQError m e u ∧
    0 ≤ higham23WinogradQNorm m e u := by
  rcases higham23_winogradRadii_nonneg u hu with
    ⟨hN1, hE1, hN2, hE2, hN4, hE4⟩
  have hP1E : 0 ≤ higham23WinogradP1Error m e u := by
    unfold higham23WinogradP1Error higham23WinogradProductError
    positivity
  have hP1N : 0 ≤ higham23WinogradP1Norm m e u := by
    unfold higham23WinogradP1Norm higham23WinogradProductNorm
    positivity
  have hP4E : 0 ≤ higham23WinogradP4Error m e u := by
    unfold higham23WinogradP4Error higham23WinogradProductError
    positivity
  have hP4N : 0 ≤ higham23WinogradP4Norm m e u := by
    unfold higham23WinogradP4Norm higham23WinogradProductNorm
    positivity
  have hP6E : 0 ≤ higham23WinogradP6Error m e u := by
    unfold higham23WinogradP6Error higham23WinogradProductError
    positivity
  have hP6N : 0 ≤ higham23WinogradP6Norm m e u := by
    unfold higham23WinogradP6Norm higham23WinogradProductNorm
    positivity
  have hT1E : 0 ≤ higham23WinogradT1Error m e u := by
    unfold higham23WinogradT1Error
    positivity
  have hT1N : 0 ≤ higham23WinogradT1Norm m e u := by
    unfold higham23WinogradT1Norm
    positivity
  have hQE : 0 ≤ higham23WinogradQError m e u := by
    unfold higham23WinogradQError
    positivity
  have hQN : 0 ≤ higham23WinogradQNorm m e u := by
    unfold higham23WinogradQNorm
    positivity
  exact ⟨hP1E, hP1N, hP4E, hP4N, hP6E, hP6N,
    hT1E, hT1N, hQE, hQN⟩

private theorem higham23_winogradP4Error_le_P6Error
    (m e u : ℝ) (hm : 0 ≤ m) (he : 0 ≤ e) (hu : 0 ≤ u) :
    higham23WinogradP4Error m e u ≤ higham23WinogradP6Error m e u := by
  simp only [higham23WinogradP4Error, higham23WinogradP6Error,
    higham23WinogradProductError, higham23WinogradN1, higham23WinogradE1,
    higham23WinogradN2, higham23WinogradE2, higham23WinogradN4,
    higham23WinogradE4]
  ring_nf
  have hmu : 0 ≤ m * u := mul_nonneg hm hu
  have hmu2 : 0 ≤ m * u ^ 2 := mul_nonneg hm (sq_nonneg u)
  have hmu3 : 0 ≤ m * u ^ 3 := by positivity
  have heu : 0 ≤ e * u := mul_nonneg he hu
  have heu2 : 0 ≤ e * u ^ 2 := mul_nonneg he (sq_nonneg u)
  have heu3 : 0 ≤ e * u ^ 3 := by positivity
  nlinarith

private theorem higham23_winogradP4Norm_le_P6Norm
    (m e u : ℝ) (hm : 0 ≤ m) (he : 0 ≤ e) (hu : 0 ≤ u) :
    higham23WinogradP4Norm m e u ≤ higham23WinogradP6Norm m e u := by
  simp only [higham23WinogradP4Norm, higham23WinogradP6Norm,
    higham23WinogradProductNorm, higham23WinogradN1,
    higham23WinogradN2, higham23WinogradN4]
  ring_nf
  have hmu : 0 ≤ m * u := mul_nonneg hm hu
  have hmu2 : 0 ≤ m * u ^ 2 := mul_nonneg hm (sq_nonneg u)
  have hmu3 : 0 ≤ m * u ^ 3 := by positivity
  have heu : 0 ≤ e * u := mul_nonneg he hu
  have heu2 : 0 ≤ e * u ^ 2 := mul_nonneg he (sq_nonneg u)
  have heu3 : 0 ≤ e * u ^ 3 := by positivity
  nlinarith

private theorem higham23_winogradC22Error_le_step
    (m e u : ℝ) (hm : 0 ≤ m) (he : 0 ≤ e) (hu : 0 ≤ u) :
    higham23WinogradC22Error m e u ≤
      higham23WinogradStepMajorant m e u := by
  unfold higham23WinogradC22Error higham23WinogradStepMajorant
  have hE := higham23_winogradP4Error_le_P6Error m e u hm he hu
  have hN := higham23_winogradP4Norm_le_P6Norm m e u hm he hu
  have hround := mul_le_mul_of_nonneg_left
    (add_le_add_left hN (higham23WinogradQNorm m e u)) hu
  linarith

private theorem higham23_winogradC11Error_le_step
    (m e u : ℝ) (hm : 0 ≤ m) (he : 0 ≤ e) (hu : 0 ≤ u) :
    higham23WinogradC11Error m e u ≤
      higham23WinogradStepMajorant m e u := by
  rcases higham23_winogradRadii_nonneg u hu with
    ⟨_hN1, _hE1, hN2, hE2, _hN4, _hE4⟩
  rcases higham23_winogradScalars_nonneg m e u hm he hu with
    ⟨hP1E0, hP1N0, hP4E0, hP4N0, hP6E0, hP6N0,
      hT1E0, hT1N0, hQE0, hQN0⟩
  have hN2one : 1 ≤ higham23WinogradN2 u := by
    simp only [higham23WinogradN2, higham23WinogradN1]
    nlinarith [sq_nonneg u]
  have hN2sq : 1 ≤ higham23WinogradN2 u * higham23WinogradN2 u := by
    nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ (1 : ℝ)) hN2one]
  have hP1E : e ≤ higham23WinogradP1Error m e u := by
    unfold higham23WinogradP1Error higham23WinogradProductError
    have hmain := mul_le_mul_of_nonneg_left hN2sq he
    have hterm1 : 0 ≤ m * higham23WinogradE2 u * 3 := by positivity
    have hterm2 : 0 ≤ m * higham23WinogradN2 u * higham23WinogradE2 u := by
      positivity
    nlinarith
  have hP1N : m + e ≤ higham23WinogradP1Norm m e u := by
    unfold higham23WinogradP1Norm higham23WinogradProductNorm
    have hme : 0 ≤ m + e := add_nonneg hm he
    have hmain := mul_le_mul_of_nonneg_left hN2sq hme
    nlinarith
  have hT1 : higham23WinogradC11Error m e u ≤
      higham23WinogradT1Error m e u := by
    unfold higham23WinogradC11Error higham23WinogradT1Error
    have hround := mul_le_mul_of_nonneg_left
      (add_le_add hP1N (le_refl (m + e))) hu
    linarith
  unfold higham23WinogradStepMajorant higham23WinogradQError
  have hroundQ : 0 ≤ u *
      (higham23WinogradT1Norm m e u + higham23WinogradP4Norm m e u) := by
    positivity
  have hroundOut : 0 ≤ u *
      (higham23WinogradQNorm m e u + higham23WinogradP6Norm m e u) := by
    positivity
  linarith

theorem higham23_winogradExactMajorant_nonneg
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    0 ≤ higham23WinogradExactMajorant fp r depth := by
  induction depth with
  | zero =>
      rw [higham23WinogradExactMajorant]
      exact mul_nonneg (Nat.cast_nonneg _) (gamma_nonneg fp hvalid)
  | succ depth ih =>
      rw [higham23WinogradExactMajorant]
      rcases higham23_winogradScalars_nonneg
        (((2 ^ (r + depth) : ℕ) : ℝ))
        (higham23WinogradExactMajorant fp r depth) fp.u
        (Nat.cast_nonneg _) ih fp.u_nonneg with
        ⟨_, _, _, _, hP6E, hP6N, _, _, hQE, hQN⟩
      unfold higham23WinogradStepMajorant
      exact add_nonneg (add_nonneg hQE hP6E)
        (mul_nonneg fp.u_nonneg (add_nonneg hQN hP6N))

/-- Theorem 23.3 at an exact nonlinear radius, proved against the literal
recursive Winograd--Strassen evaluator. -/
theorem higham23_theorem23_3_winograd_exactMajorant
    (fp : FPModel) (r : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveErrorLe r depth (A * B)
        (higham23FlWinogradStrassenRecursive fp r depth A B)
        (higham23WinogradExactMajorant fp r depth * a * b) := by
  intro depth
  induction depth with
  | zero =>
      intro A B a b ha _hb hA hB
      intro i j
      have hcomp := higham23_eq23_10_conventional_componentwise
        fp A B hvalid i j
      have hsum : (∑ k : Fin (2 ^ r), |A i k| * |B k j|) ≤
          ((2 ^ r : ℕ) : ℝ) * a * b := by
        calc
          (∑ k : Fin (2 ^ r), |A i k| * |B k j|) ≤
              ∑ _k : Fin (2 ^ r), a * b := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
          _ = ((2 ^ r : ℕ) : ℝ) * a * b := by simp; ring
      change |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤ _
      calc
        |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
            gamma fp (2 ^ r) *
              ∑ k : Fin (2 ^ r), |A i k| * |B k j| := hcomp
        _ ≤ gamma fp (2 ^ r) * (((2 ^ r : ℕ) : ℝ) * a * b) :=
          mul_le_mul_of_nonneg_left hsum (gamma_nonneg fp hvalid)
        _ = higham23WinogradExactMajorant fp r 0 * a * b := by
          simp [higham23WinogradExactMajorant]
          ring
  | succ depth ih =>
      intro A B a b ha hb hA hB
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      let u := fp.u
      let m : ℝ := (2 ^ (r + depth) : ℕ)
      let e := higham23WinogradExactMajorant fp r depth
      let N1 := higham23WinogradN1 u
      let E1 := higham23WinogradE1 u
      let N2 := higham23WinogradN2 u
      let E2 := higham23WinogradE2 u
      let N4 := higham23WinogradN4 u
      let E4 := higham23WinogradE4 u
      let P1E := higham23WinogradP1Error m e u
      let P1N := higham23WinogradP1Norm m e u
      let P4E := higham23WinogradP4Error m e u
      let P4N := higham23WinogradP4Norm m e u
      let P6E := higham23WinogradP6Error m e u
      let P6N := higham23WinogradP6Norm m e u
      let T1E := higham23WinogradT1Error m e u
      let T1N := higham23WinogradT1Norm m e u
      let QE := higham23WinogradQError m e u
      let QN := higham23WinogradQNorm m e u
      have he0 : 0 ≤ e := higham23_winogradExactMajorant_nonneg fp r depth hvalid
      have hm0 : 0 ≤ m := by dsimp [m]; positivity
      have hu0 : 0 ≤ u := by exact fp.u_nonneg
      rcases higham23_winogradRadii_nonneg u hu0 with
        ⟨hN10, hE10, hN20, hE20, hN40, hE40⟩
      rcases higham23_winogradScalars_nonneg m e u hm0 he0 hu0 with
        ⟨hP1E0, hP1N0, hP4E0, hP4N0, hP6E0, hP6N0,
          hT1E0, hT1N0, hQE0, hQN0⟩

      let S1 := A.c21 + A.c22
      let S2 := S1 - A.c11
      let S3 := A.c11 - A.c21
      let S4 := A.c12 - S2
      let S5 := B.c12 - B.c11
      let S6 := B.c22 - S5
      let S7 := B.c22 - B.c12
      let S8 := S6 - B.c21
      let s1 := higham23RecursiveFlAdd fp r depth A.c21 A.c22
      let s2 := higham23RecursiveFlSub fp r depth s1 A.c11
      let s3 := higham23RecursiveFlSub fp r depth A.c11 A.c21
      let s4 := higham23RecursiveFlSub fp r depth A.c12 s2
      let s5 := higham23RecursiveFlSub fp r depth B.c12 B.c11
      let s6 := higham23RecursiveFlSub fp r depth B.c22 s5
      let s7 := higham23RecursiveFlSub fp r depth B.c22 B.c12
      let s8 := higham23RecursiveFlSub fp r depth s6 B.c21

      have hA11c := higham23_recursiveCertificate_refl r depth A.c11 a hA11
      have hA12c := higham23_recursiveCertificate_refl r depth A.c12 a hA12
      have hA21c := higham23_recursiveCertificate_refl r depth A.c21 a hA21
      have hA22c := higham23_recursiveCertificate_refl r depth A.c22 a hA22
      have hB11c := higham23_recursiveCertificate_refl r depth B.c11 b hB11
      have hB12c := higham23_recursiveCertificate_refl r depth B.c12 b hB12
      have hB21c := higham23_recursiveCertificate_refl r depth B.c21 b hB21
      have hB22c := higham23_recursiveCertificate_refl r depth B.c22 b hB22

      have hs1raw := higham23_recursiveCertificate_flAdd fp r depth
        A.c21 A.c21 A.c22 A.c22 0 a 0 a ha ha hA21c hA22c
      have hs1 : Higham23RecursiveCertificate r depth S1 s1 (E1 * a) (N1 * a) := by
        convert hs1raw using 1 <;>
          dsimp [S1, s1, E1, N1, u, higham23WinogradE1,
            higham23WinogradN1] <;> ring
      have hs2raw := higham23_recursiveCertificate_flSub fp r depth
        S1 s1 A.c11 A.c11 (E1 * a) (N1 * a) 0 a
        (mul_nonneg hN10 ha) ha hs1 hA11c
      have hs2 : Higham23RecursiveCertificate r depth S2 s2 (E2 * a) (N2 * a) := by
        convert hs2raw using 1 <;>
          dsimp [S2, s2, E2, N2, E1, N1, u,
            higham23WinogradE2, higham23WinogradN2,
            higham23WinogradE1, higham23WinogradN1] <;> ring
      have hs3raw := higham23_recursiveCertificate_flSub fp r depth
        A.c11 A.c11 A.c21 A.c21 0 a 0 a ha ha hA11c hA21c
      have hs3 : Higham23RecursiveCertificate r depth S3 s3 (E1 * a) (N1 * a) := by
        convert hs3raw using 1 <;>
          dsimp [S3, s3, E1, N1, u, higham23WinogradE1,
            higham23WinogradN1] <;> ring
      have hs4raw := higham23_recursiveCertificate_flSub fp r depth
        A.c12 A.c12 S2 s2 0 a (E2 * a) (N2 * a)
        ha (mul_nonneg hN20 ha) hA12c hs2
      have hs4 : Higham23RecursiveCertificate r depth S4 s4 (E4 * a) (N4 * a) := by
        convert hs4raw using 1 <;>
          dsimp [S4, s4, E4, N4, E2, N2, E1, N1, u,
            higham23WinogradE4, higham23WinogradN4,
            higham23WinogradE2, higham23WinogradN2,
            higham23WinogradE1, higham23WinogradN1] <;> ring
      have hs5raw := higham23_recursiveCertificate_flSub fp r depth
        B.c12 B.c12 B.c11 B.c11 0 b 0 b hb hb hB12c hB11c
      have hs5 : Higham23RecursiveCertificate r depth S5 s5 (E1 * b) (N1 * b) := by
        convert hs5raw using 1 <;>
          dsimp [S5, s5, E1, N1, u, higham23WinogradE1,
            higham23WinogradN1] <;> ring
      have hs6raw := higham23_recursiveCertificate_flSub fp r depth
        B.c22 B.c22 S5 s5 0 b (E1 * b) (N1 * b)
        hb (mul_nonneg hN10 hb) hB22c hs5
      have hs6 : Higham23RecursiveCertificate r depth S6 s6 (E2 * b) (N2 * b) := by
        convert hs6raw using 1 <;>
          dsimp [S6, s6, E2, N2, E1, N1, u,
            higham23WinogradE2, higham23WinogradN2,
            higham23WinogradE1, higham23WinogradN1] <;> ring
      have hs7raw := higham23_recursiveCertificate_flSub fp r depth
        B.c22 B.c22 B.c12 B.c12 0 b 0 b hb hb hB22c hB12c
      have hs7 : Higham23RecursiveCertificate r depth S7 s7 (E1 * b) (N1 * b) := by
        convert hs7raw using 1 <;>
          dsimp [S7, s7, E1, N1, u, higham23WinogradE1,
            higham23WinogradN1] <;> ring
      have hs8raw := higham23_recursiveCertificate_flSub fp r depth
        S6 s6 B.c21 B.c21 (E2 * b) (N2 * b) 0 b
        (mul_nonneg hN20 hb) hb hs6 hB21c
      have hs8 : Higham23RecursiveCertificate r depth S8 s8 (E4 * b) (N4 * b) := by
        convert hs8raw using 1 <;>
          dsimp [S8, s8, E4, N4, E2, N2, E1, N1, u,
            higham23WinogradE4, higham23WinogradN4,
            higham23WinogradE2, higham23WinogradN2,
            higham23WinogradE1, higham23WinogradN1] <;> ring

      have hS1 := higham23_recursiveMaxNormLe_add r depth A.c21 A.c22 hA21 hA22
      have hS1' : Higham23RecursiveMaxNormLe r depth S1 (2 * a) := by
        convert hS1 using 1 <;> dsimp [S1] <;> ring
      have hS2raw := higham23_recursiveMaxNormLe_sub r depth S1 A.c11 hS1' hA11
      have hS2 : Higham23RecursiveMaxNormLe r depth S2 (3 * a) := by
        convert hS2raw using 1 <;> dsimp [S2] <;> ring
      have hS3raw := higham23_recursiveMaxNormLe_sub r depth A.c11 A.c21 hA11 hA21
      have hS3 : Higham23RecursiveMaxNormLe r depth S3 (2 * a) := by
        convert hS3raw using 1 <;> dsimp [S3] <;> ring
      have hS4raw := higham23_recursiveMaxNormLe_sub r depth A.c12 S2 hA12 hS2
      have hS4 : Higham23RecursiveMaxNormLe r depth S4 (4 * a) := by
        convert hS4raw using 1 <;> dsimp [S4] <;> ring
      have hS5raw := higham23_recursiveMaxNormLe_sub r depth B.c12 B.c11 hB12 hB11
      have hS5 : Higham23RecursiveMaxNormLe r depth S5 (2 * b) := by
        convert hS5raw using 1 <;> dsimp [S5] <;> ring
      have hS6raw := higham23_recursiveMaxNormLe_sub r depth B.c22 S5 hB22 hS5
      have hS6 : Higham23RecursiveMaxNormLe r depth S6 (3 * b) := by
        convert hS6raw using 1 <;> dsimp [S6] <;> ring
      have hS7raw := higham23_recursiveMaxNormLe_sub r depth B.c22 B.c12 hB22 hB12
      have hS7 : Higham23RecursiveMaxNormLe r depth S7 (2 * b) := by
        convert hS7raw using 1 <;> dsimp [S7] <;> ring
      have hS8raw := higham23_recursiveMaxNormLe_sub r depth S6 B.c21 hS6 hB21
      have hS8 : Higham23RecursiveMaxNormLe r depth S8 (4 * b) := by
        convert hS8raw using 1 <;> dsimp [S8] <;> ring

      let p1 := higham23FlWinogradStrassenRecursive fp r depth s2 s6
      let p2 := higham23FlWinogradStrassenRecursive fp r depth A.c11 B.c11
      let p3 := higham23FlWinogradStrassenRecursive fp r depth A.c12 B.c21
      let p4 := higham23FlWinogradStrassenRecursive fp r depth s3 s7
      let p5 := higham23FlWinogradStrassenRecursive fp r depth s1 s5
      let p6 := higham23FlWinogradStrassenRecursive fp r depth s4 B.c22
      let p7 := higham23FlWinogradStrassenRecursive fp r depth A.c22 s8

      have hp1Rec := ih s2 s6 (N2 * a) (N2 * b)
        (mul_nonneg hN20 ha) (mul_nonneg hN20 hb) hs2.norm_le hs6.norm_le
      have hp1raw := higham23_recursiveCertificate_product r depth
        S2 s2 S6 s6 p1 (3 * a) (3 * b) (E2 * a) (N2 * a)
        (E2 * b) (N2 * b) e (by positivity) (by positivity)
        (mul_nonneg hE20 ha) (mul_nonneg hN20 ha)
        (mul_nonneg hE20 hb) (mul_nonneg hN20 hb) he0
        hS2 hS6 hs2 hs6 (by simpa [p1, e] using hp1Rec)
      have hp1 : Higham23RecursiveCertificate r depth (S2 * S6) p1
          (P1E * a * b) (P1N * a * b) := by
        convert hp1raw using 1 <;>
          dsimp [P1E, P1N, m, e, E2, N2,
            higham23WinogradP1Error, higham23WinogradP1Norm,
            higham23WinogradProductError, higham23WinogradProductNorm] <;> ring

      have hp2Rec := ih A.c11 B.c11 a b ha hb hA11 hB11
      have hp2raw := higham23_recursiveCertificate_product r depth
        A.c11 A.c11 B.c11 B.c11 p2 a b 0 a 0 b e
        ha hb (by norm_num) ha (by norm_num) hb he0
        hA11 hB11 hA11c hB11c (by simpa [p2, e] using hp2Rec)
      have hp2 : Higham23RecursiveCertificate r depth (A.c11 * B.c11) p2
          (e * a * b) ((m + e) * a * b) := by
        convert hp2raw using 1 <;> dsimp [m] <;> ring

      have hp3Rec := ih A.c12 B.c21 a b ha hb hA12 hB21
      have hp3raw := higham23_recursiveCertificate_product r depth
        A.c12 A.c12 B.c21 B.c21 p3 a b 0 a 0 b e
        ha hb (by norm_num) ha (by norm_num) hb he0
        hA12 hB21 hA12c hB21c (by simpa [p3, e] using hp3Rec)
      have hp3 : Higham23RecursiveCertificate r depth (A.c12 * B.c21) p3
          (e * a * b) ((m + e) * a * b) := by
        convert hp3raw using 1 <;> dsimp [m] <;> ring

      have hp4Rec := ih s3 s7 (N1 * a) (N1 * b)
        (mul_nonneg hN10 ha) (mul_nonneg hN10 hb) hs3.norm_le hs7.norm_le
      have hp4raw := higham23_recursiveCertificate_product r depth
        S3 s3 S7 s7 p4 (2 * a) (2 * b) (E1 * a) (N1 * a)
        (E1 * b) (N1 * b) e (by positivity) (by positivity)
        (mul_nonneg hE10 ha) (mul_nonneg hN10 ha)
        (mul_nonneg hE10 hb) (mul_nonneg hN10 hb) he0
        hS3 hS7 hs3 hs7 (by simpa [p4, e] using hp4Rec)
      have hp4 : Higham23RecursiveCertificate r depth (S3 * S7) p4
          (P4E * a * b) (P4N * a * b) := by
        convert hp4raw using 1 <;>
          dsimp [P4E, P4N, m, e, E1, N1,
            higham23WinogradP4Error, higham23WinogradP4Norm,
            higham23WinogradProductError, higham23WinogradProductNorm] <;> ring

      have hp5Rec := ih s1 s5 (N1 * a) (N1 * b)
        (mul_nonneg hN10 ha) (mul_nonneg hN10 hb) hs1.norm_le hs5.norm_le
      have hp5raw := higham23_recursiveCertificate_product r depth
        S1 s1 S5 s5 p5 (2 * a) (2 * b) (E1 * a) (N1 * a)
        (E1 * b) (N1 * b) e (by positivity) (by positivity)
        (mul_nonneg hE10 ha) (mul_nonneg hN10 ha)
        (mul_nonneg hE10 hb) (mul_nonneg hN10 hb) he0
        hS1' hS5 hs1 hs5 (by simpa [p5, e] using hp5Rec)
      have hp5 : Higham23RecursiveCertificate r depth (S1 * S5) p5
          (P4E * a * b) (P4N * a * b) := by
        convert hp5raw using 1 <;>
          dsimp [P4E, P4N, m, e, E1, N1,
            higham23WinogradP4Error, higham23WinogradP4Norm,
            higham23WinogradProductError, higham23WinogradProductNorm] <;> ring

      have hp6Rec := ih s4 B.c22 (N4 * a) b
        (mul_nonneg hN40 ha) hb hs4.norm_le hB22
      have hp6raw := higham23_recursiveCertificate_product r depth
        S4 s4 B.c22 B.c22 p6 (4 * a) b (E4 * a) (N4 * a)
        0 b e (by positivity) hb (mul_nonneg hE40 ha)
        (mul_nonneg hN40 ha) (by norm_num) hb he0
        hS4 hB22 hs4 hB22c (by simpa [p6, e] using hp6Rec)
      have hp6 : Higham23RecursiveCertificate r depth (S4 * B.c22) p6
          (P6E * a * b) (P6N * a * b) := by
        convert hp6raw using 1 <;>
          dsimp [P6E, P6N, m, e, E4, N4,
            higham23WinogradP6Error, higham23WinogradP6Norm,
            higham23WinogradProductError, higham23WinogradProductNorm] <;> ring

      have hp7Rec := ih A.c22 s8 a (N4 * b)
        ha (mul_nonneg hN40 hb) hA22 hs8.norm_le
      have hp7raw := higham23_recursiveCertificate_product r depth
        A.c22 A.c22 S8 s8 p7 a (4 * b) 0 a (E4 * b) (N4 * b) e
        ha (by positivity) (by norm_num) ha (mul_nonneg hE40 hb)
        (mul_nonneg hN40 hb) he0 hA22 hS8 hA22c hs8
        (by simpa [p7, e] using hp7Rec)
      have hp7 : Higham23RecursiveCertificate r depth (A.c22 * S8) p7
          (P6E * a * b) (P6N * a * b) := by
        convert hp7raw using 1 <;>
          dsimp [P6E, P6N, m, e, E4, N4,
            higham23WinogradP6Error, higham23WinogradP6Norm,
            higham23WinogradProductError, higham23WinogradProductNorm] <;> ring

      let t1 := higham23RecursiveFlAdd fp r depth p1 p2
      let t2 := higham23RecursiveFlAdd fp r depth t1 p4
      let q12 := higham23RecursiveFlAdd fp r depth t1 p5
      have ht1raw := higham23_recursiveCertificate_flAdd fp r depth
        (S2 * S6) p1 (A.c11 * B.c11) p2
        (P1E * a * b) (P1N * a * b) (e * a * b) ((m + e) * a * b)
        (by positivity) (by positivity) hp1 hp2
      have ht1 : Higham23RecursiveCertificate r depth
          (S2 * S6 + A.c11 * B.c11) t1 (T1E * a * b) (T1N * a * b) := by
        convert ht1raw using 1 <;>
          dsimp [t1, T1E, T1N, P1E, P1N, u,
            higham23WinogradT1Error, higham23WinogradT1Norm] <;> ring
      have ht2raw := higham23_recursiveCertificate_flAdd fp r depth
        (S2 * S6 + A.c11 * B.c11) t1 (S3 * S7) p4
        (T1E * a * b) (T1N * a * b) (P4E * a * b) (P4N * a * b)
        (by positivity) (by positivity) ht1 hp4
      have ht2 : Higham23RecursiveCertificate r depth
          (S2 * S6 + A.c11 * B.c11 + S3 * S7) t2
          (QE * a * b) (QN * a * b) := by
        convert ht2raw using 1 <;>
          dsimp [t2, QE, QN, T1E, T1N, P4E, P4N, u,
            higham23WinogradQError, higham23WinogradQNorm] <;> ring
      have hqraw := higham23_recursiveCertificate_flAdd fp r depth
        (S2 * S6 + A.c11 * B.c11) t1 (S1 * S5) p5
        (T1E * a * b) (T1N * a * b) (P4E * a * b) (P4N * a * b)
        (by positivity) (by positivity) ht1 hp5
      have hq : Higham23RecursiveCertificate r depth
          (S2 * S6 + A.c11 * B.c11 + S1 * S5) q12
          (QE * a * b) (QN * a * b) := by
        convert hqraw using 1 <;>
          dsimp [q12, QE, QN, T1E, T1N, P4E, P4N, u,
            higham23WinogradQError, higham23WinogradQNorm] <;> ring

      have hc11raw := higham23_recursiveCertificate_flAdd fp r depth
        (A.c11 * B.c11) p2 (A.c12 * B.c21) p3
        (e * a * b) ((m + e) * a * b) (e * a * b) ((m + e) * a * b)
        (by positivity) (by positivity) hp2 hp3
      have hc11 : Higham23RecursiveCertificate r depth
          (A.c11 * B.c11 + A.c12 * B.c21)
          (higham23RecursiveFlAdd fp r depth p2 p3)
          (higham23WinogradC11Error m e u * a * b)
          ((1 + u) * (((m + e) * a * b) + ((m + e) * a * b))) := by
        convert hc11raw using 1 <;>
          dsimp [higham23WinogradC11Error, u] <;> ring
      have hc12raw := higham23_recursiveCertificate_flAdd fp r depth
        (S2 * S6 + A.c11 * B.c11 + S1 * S5) q12 (S4 * B.c22) p6
        (QE * a * b) (QN * a * b) (P6E * a * b) (P6N * a * b)
        (by positivity) (by positivity) hq hp6
      have hc12 : Higham23RecursiveCertificate r depth
          (S2 * S6 + A.c11 * B.c11 + S1 * S5 + S4 * B.c22)
          (higham23RecursiveFlAdd fp r depth q12 p6)
          (higham23WinogradStepMajorant m e u * a * b)
          ((1 + u) * (QN + P6N) * a * b) := by
        convert hc12raw using 1 <;>
          dsimp [higham23WinogradStepMajorant, u, QE, QN, P6E, P6N] <;> ring
      have hc21raw := higham23_recursiveCertificate_flSub fp r depth
        (S2 * S6 + A.c11 * B.c11 + S3 * S7) t2 (A.c22 * S8) p7
        (QE * a * b) (QN * a * b) (P6E * a * b) (P6N * a * b)
        (by positivity) (by positivity) ht2 hp7
      have hc21 : Higham23RecursiveCertificate r depth
          (S2 * S6 + A.c11 * B.c11 + S3 * S7 - A.c22 * S8)
          (higham23RecursiveFlSub fp r depth t2 p7)
          (higham23WinogradStepMajorant m e u * a * b)
          ((1 + u) * (QN + P6N) * a * b) := by
        convert hc21raw using 1 <;>
          dsimp [higham23WinogradStepMajorant, u, QE, QN, P6E, P6N] <;> ring
      have hc22raw := higham23_recursiveCertificate_flAdd fp r depth
        (S2 * S6 + A.c11 * B.c11 + S3 * S7) t2 (S1 * S5) p5
        (QE * a * b) (QN * a * b) (P4E * a * b) (P4N * a * b)
        (by positivity) (by positivity) ht2 hp5
      have hc22 : Higham23RecursiveCertificate r depth
          (S2 * S6 + A.c11 * B.c11 + S3 * S7 + S1 * S5)
          (higham23RecursiveFlAdd fp r depth t2 p5)
          (higham23WinogradC22Error m e u * a * b)
          ((1 + u) * (QN + P4N) * a * b) := by
        convert hc22raw using 1 <;>
          dsimp [higham23WinogradC22Error, u, QE, QN, P4E, P4N] <;> ring

      have hab0 : 0 ≤ a * b := mul_nonneg ha hb
      have hC11step := higham23_winogradC11Error_le_step m e u hm0 he0 hu0
      have hC22step := higham23_winogradC22Error_le_step m e u hm0 he0 hu0
      have hstepEq : higham23WinogradStepMajorant m e u * a * b =
          higham23WinogradExactMajorant fp r (depth + 1) * a * b := by
        dsimp [higham23WinogradExactMajorant, m, e, u]
      have hcorrect := higham23_eq23_6_winogradStrassen_correct A B
      have h11 : Higham23RecursiveErrorLe r depth (A * B).c11
          (higham23FlWinogradStrassenRecursive fp r (depth + 1) A B).c11
          (higham23WinogradExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c11) hcorrect
        change (higham23WinogradStrassen2 A B).c11 = (A * B).c11 at hc
        have hrad : higham23WinogradC11Error m e u * a * b ≤
            higham23WinogradStepMajorant m e u * a * b := by
          calc
            higham23WinogradC11Error m e u * a * b =
                higham23WinogradC11Error m e u * (a * b) := by ring
            _ ≤ higham23WinogradStepMajorant m e u * (a * b) :=
              mul_le_mul_of_nonneg_right hC11step hab0
            _ = higham23WinogradStepMajorant m e u * a * b := by ring
        have hm11 := higham23_recursiveErrorLe_mono r depth _ _ hc11.error_le
          hrad
        rw [← hc, ← hstepEq]
        simpa [higham23WinogradStrassen2,
          higham23FlWinogradStrassenRecursive, S1, S2, S3, S4, S5, S6, S7, S8,
          s1, s2, s3, s4, s5, s6, s7, s8, p1, p2, p3, p4, p5, p6, p7,
          t1, t2, q12] using hm11
      have h12 : Higham23RecursiveErrorLe r depth (A * B).c12
          (higham23FlWinogradStrassenRecursive fp r (depth + 1) A B).c12
          (higham23WinogradExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c12) hcorrect
        change (higham23WinogradStrassen2 A B).c12 = (A * B).c12 at hc
        rw [← hc, ← hstepEq]
        simpa [higham23WinogradStrassen2,
          higham23FlWinogradStrassenRecursive, S1, S2, S3, S4, S5, S6, S7, S8,
          s1, s2, s3, s4, s5, s6, s7, s8, p1, p2, p3, p4, p5, p6, p7,
          t1, t2, q12] using hc12.error_le
      have h21 : Higham23RecursiveErrorLe r depth (A * B).c21
          (higham23FlWinogradStrassenRecursive fp r (depth + 1) A B).c21
          (higham23WinogradExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c21) hcorrect
        change (higham23WinogradStrassen2 A B).c21 = (A * B).c21 at hc
        rw [← hc, ← hstepEq]
        simpa [higham23WinogradStrassen2,
          higham23FlWinogradStrassenRecursive, S1, S2, S3, S4, S5, S6, S7, S8,
          s1, s2, s3, s4, s5, s6, s7, s8, p1, p2, p3, p4, p5, p6, p7,
          t1, t2, q12] using hc21.error_le
      have h22 : Higham23RecursiveErrorLe r depth (A * B).c22
          (higham23FlWinogradStrassenRecursive fp r (depth + 1) A B).c22
          (higham23WinogradExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c22) hcorrect
        change (higham23WinogradStrassen2 A B).c22 = (A * B).c22 at hc
        have hrad : higham23WinogradC22Error m e u * a * b ≤
            higham23WinogradStepMajorant m e u * a * b := by
          calc
            higham23WinogradC22Error m e u * a * b =
                higham23WinogradC22Error m e u * (a * b) := by ring
            _ ≤ higham23WinogradStepMajorant m e u * (a * b) :=
              mul_le_mul_of_nonneg_right hC22step hab0
            _ = higham23WinogradStepMajorant m e u * a * b := by ring
        have hm22 := higham23_recursiveErrorLe_mono r depth _ _ hc22.error_le
          hrad
        rw [← hc, ← hstepEq]
        simpa [higham23WinogradStrassen2,
          higham23FlWinogradStrassenRecursive, S1, S2, S3, S4, S5, S6, S7, S8,
          s1, s2, s3, s4, s5, s6, s7, s8, p1, p2, p3, p4, p5, p6, p7,
          t1, t2, q12] using hm22
      exact ⟨h11, h12, h21, h22⟩

/-! ## The 18/89 linearization in (23.18) -/

noncomputable def higham23WinogradStepResidual (m e u : ℝ) : ℝ :=
  higham23WinogradStepMajorant m e u - (89 * m * u + 18 * e)

private noncomputable def higham23WinogradStepMQuadratic (u : ℝ) : ℝ :=
  197 + 256 * u + 211 * u ^ 2 + 109 * u ^ 3 + 32 * u ^ 4 + 4 * u ^ 5

private noncomputable def higham23WinogradStepEQuadratic (u : ℝ) : ℝ :=
  89 + 197 * u + 256 * u ^ 2 + 211 * u ^ 3 + 109 * u ^ 4 +
    32 * u ^ 5 + 4 * u ^ 6

theorem higham23_winogradStepResidual_factor (m e u : ℝ) :
    higham23WinogradStepResidual m e u =
      m * u ^ 2 * higham23WinogradStepMQuadratic u +
        e * u * higham23WinogradStepEQuadratic u := by
  unfold higham23WinogradStepResidual higham23WinogradStepMajorant
    higham23WinogradQError higham23WinogradQNorm
    higham23WinogradT1Error higham23WinogradT1Norm
    higham23WinogradP1Error higham23WinogradP1Norm
    higham23WinogradP4Error higham23WinogradP4Norm
    higham23WinogradP6Error higham23WinogradP6Norm
    higham23WinogradProductError higham23WinogradProductNorm
    higham23WinogradN1 higham23WinogradE1
    higham23WinogradN2 higham23WinogradE2
    higham23WinogradN4 higham23WinogradE4
    higham23WinogradStepMQuadratic higham23WinogradStepEQuadratic
  simp only [higham23WinogradN1, higham23WinogradE1,
    higham23WinogradN2, higham23WinogradE2,
    higham23WinogradN4, higham23WinogradE4]
  ring

private theorem higham23_winogradStepMQuadratic_continuousAt :
    ContinuousAt higham23WinogradStepMQuadratic 0 := by
  unfold higham23WinogradStepMQuadratic
  fun_prop

private theorem higham23_winogradStepEQuadratic_continuousAt :
    ContinuousAt higham23WinogradStepEQuadratic 0 := by
  unfold higham23WinogradStepEQuadratic
  fun_prop

theorem higham23_winogradStepResidual_isBigO_u_sq
    (m : ℝ) (e : ℝ → ℝ)
    (he : e =O[𝓝 0] (fun u : ℝ ↦ u)) :
    (fun u : ℝ ↦ higham23WinogradStepResidual m (e u) u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hMCoeff :
      (fun u : ℝ ↦ m * higham23WinogradStepMQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    (continuousAt_const.mul higham23_winogradStepMQuadratic_continuousAt).isBigO_one ℝ
  have hMTerm :
      (fun u : ℝ ↦ m * u ^ 2 * higham23WinogradStepMQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := huSq.mul hMCoeff
    simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using h
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have hECoeff :
      (fun u : ℝ ↦ higham23WinogradStepEQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    higham23_winogradStepEQuadratic_continuousAt.isBigO_one ℝ
  have hETerm :
      (fun u : ℝ ↦ e u * u * higham23WinogradStepEQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := (he.mul hu).mul hECoeff
    simpa only [pow_two, mul_one, mul_assoc] using h
  have h := hMTerm.add hETerm
  apply h.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      exact (higham23_winogradStepResidual_factor m (e u) u).symm
  · exact Filter.EventuallyEq.rfl

noncomputable def higham23WinogradMajorantFamily (r : ℕ) : ℕ → ℝ → ℝ
  | 0, u =>
      (4 : ℝ) ^ r * u +
        ((2 ^ r : ℕ) : ℝ) * higham23GammaRemainder (2 ^ r) u
  | depth + 1, u =>
      higham23WinogradStepMajorant ((2 ^ (r + depth) : ℕ) : ℝ)
        (higham23WinogradMajorantFamily r depth u) u

noncomputable def higham23WinogradMajorantRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23WinogradMajorantFamily r depth u -
    higham23WinogradStrassenErrorCoefficient r depth * u

theorem higham23_winogradExactMajorant_eq_family
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    higham23WinogradExactMajorant fp r depth =
      higham23WinogradMajorantFamily r depth fp.u := by
  induction depth with
  | zero =>
      rw [higham23WinogradExactMajorant, higham23WinogradMajorantFamily,
        higham23_gamma_split fp (2 ^ r) hvalid]
      norm_num [Nat.cast_pow]
      have hp : (2 : ℝ) ^ r * (2 : ℝ) ^ r = (4 : ℝ) ^ r := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) ^ r *
              ((2 : ℝ) ^ r * fp.u + higham23GammaRemainder (2 ^ r) fp.u) =
            ((2 : ℝ) ^ r * (2 : ℝ) ^ r) * fp.u +
              (2 : ℝ) ^ r * higham23GammaRemainder (2 ^ r) fp.u := by ring
        _ = _ := by rw [hp]
  | succ depth ih =>
      rw [higham23WinogradExactMajorant, higham23WinogradMajorantFamily, ih]

theorem higham23_winogradMajorantRemainder_isBigO_u_sq (r depth : ℕ) :
    (fun u : ℝ ↦ higham23WinogradMajorantRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  induction depth with
  | zero =>
      have h := (higham23_gammaRemainder_isBigO_u_sq (2 ^ r)).const_mul_left
        (((2 ^ r : ℕ) : ℝ))
      simpa only [higham23WinogradMajorantRemainder,
        higham23WinogradMajorantFamily,
        higham23_winogradStrassenErrorCoefficient_zero,
        add_sub_cancel_left] using h
  | succ depth ih =>
      let e : ℝ → ℝ := higham23WinogradMajorantFamily r depth
      let c := higham23WinogradStrassenErrorCoefficient r depth
      let m : ℝ := ((2 ^ (r + depth) : ℕ) : ℝ)
      have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        Asymptotics.isBigO_refl _ _
      have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
        continuousAt_id.isBigO_one ℝ
      have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
        simpa only [pow_two, mul_one] using hu.mul huOne
      have hLinear : (fun u : ℝ ↦ c * u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        hu.const_mul_left c
      have he : e =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hsum := hLinear.add (ih.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by
            dsimp [e, c, higham23WinogradMajorantRemainder]
            ring
        · exact Filter.EventuallyEq.rfl
      have hStep := higham23_winogradStepResidual_isBigO_u_sq m e he
      have hPrevious := ih.const_mul_left (18 : ℝ)
      have h := hStep.add hPrevious
      apply h.congr'
      · exact Filter.Eventually.of_forall fun u ↦ by
          dsimp [higham23WinogradMajorantRemainder,
            higham23WinogradMajorantFamily, e, c, m]
          rw [higham23_winogradStrassenErrorCoefficient_step]
          unfold higham23WinogradStepResidual
          norm_num [Nat.cast_pow, pow_add]
          ring
      · exact Filter.EventuallyEq.rfl

theorem higham23_theorem23_3_winograd_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlWinogradStrassenRecursive fp r depth A B)
      ((higham23WinogradStrassenErrorCoefficient r depth * fp.u +
          higham23WinogradMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_3_winograd_exactMajorant fp r hvalid
    depth A B a b ha hb hA hB
  rw [higham23_winogradExactMajorant_eq_family fp r depth hvalid] at h
  have hsplit : higham23WinogradMajorantFamily r depth fp.u =
      higham23WinogradStrassenErrorCoefficient r depth * fp.u +
        higham23WinogradMajorantRemainder r depth fp.u := by
    unfold higham23WinogradMajorantRemainder
    ring
  rwa [hsplit] at h

/-- Theorem 23.3 in the closed form printed in (23.18). -/
theorem higham23_theorem23_3_winograd_closedCoefficient_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlWinogradStrassenRecursive fp r depth A B)
      ((higham23WinogradStrassenClosedCoefficient r depth * fp.u +
          higham23WinogradMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_3_winograd_firstOrder fp r depth hvalid
    A B a b ha hb hA hB
  apply higham23_recursiveErrorLe_mono r depth _ _ h
  have hc := higham23_winogradStrassenErrorCoefficient_le r depth
  have hs : 0 ≤ fp.u * a * b :=
    mul_nonneg (mul_nonneg fp.u_nonneg ha) hb
  have hm := mul_le_mul_of_nonneg_right hc hs
  dsimp [higham23WinogradStrassenClosedCoefficient] at hm ⊢
  nlinarith

/-! ## Miller's finite bilinear polynomial circuit (23.11) -/

/-- Flatten a square matrix in the same fixed order used by the rounded
linear forms below. -/
def higham23MillerFlatten {h : ℕ}
    (A : Matrix (Fin h) (Fin h) ℝ) (q : Fin (h * h)) : ℝ :=
  A (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

def higham23MillerFlattenU {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t)
    (q : Fin (h * h)) : ℝ :=
  alg.U k (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

def higham23MillerFlattenV {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t)
    (q : Fin (h * h)) : ℝ :=
  alg.V k (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

noncomputable def higham23MillerUWeight {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h), |higham23MillerFlattenU alg k q|

noncomputable def higham23MillerVWeight {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h), |higham23MillerFlattenV alg k q|

noncomputable def higham23MillerExactU {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h),
    higham23MillerFlattenU alg k q * higham23MillerFlatten A q

noncomputable def higham23MillerExactV {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  ∑ q : Fin (h * h),
    higham23MillerFlattenV alg k q * higham23MillerFlatten B q

/-- The literal rounded linear forms: coefficient multiplications and their
left-to-right accumulation are the library's actual `fl_dotProduct`. -/
noncomputable def higham23MillerFlU (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  fl_dotProduct fp (h * h) (higham23MillerFlattenU alg k)
    (higham23MillerFlatten A)

noncomputable def higham23MillerFlV (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  fl_dotProduct fp (h * h) (higham23MillerFlattenV alg k)
    (higham23MillerFlatten B)

noncomputable def higham23MillerExactProduct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  higham23MillerExactU alg A k * higham23MillerExactV alg B k

noncomputable def higham23MillerFlProduct (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  fp.fl_mul (higham23MillerFlU fp alg A k) (higham23MillerFlV fp alg B k)

noncomputable def higham23MillerExactEvaluate {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j ↦ ∑ k : Fin t, alg.W i j k * higham23MillerExactProduct alg A B k

/-- Literal rounded bilinear circuit: rounded input linear forms, one rounded
multiplication for each bilinear product, and one rounded reconstruction dot
product for every output entry. -/
noncomputable def higham23MillerFlEvaluate (fp : FPModel) {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j ↦ fl_dotProduct fp t (alg.W i j)
    (higham23MillerFlProduct fp alg A B)

theorem higham23_miller_flat_sum {h : ℕ} (f : Fin h → Fin h → ℝ) :
    (∑ q : Fin (h * h),
      f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) =
      ∑ i : Fin h, ∑ j : Fin h, f i j := by
  have he : (∑ p : Fin h × Fin h, f p.1 p.2) =
      ∑ q : Fin (h * h),
        f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 := by
    simpa using (Equiv.sum_comp finProdFinEquiv
      (fun q : Fin (h * h) ↦
        f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))
  calc
    (∑ q : Fin (h * h),
        f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) =
        ∑ p : Fin h × Fin h, f p.1 p.2 := he.symm
    _ = ∑ i : Fin h, ∑ j : Fin h, f i j := Fintype.sum_prod_type _

theorem higham23_millerExactEvaluate_eq_bilinearEvaluate {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) :
    higham23MillerExactEvaluate alg A B = higham23BilinearEvaluate alg A B := by
  funext i j
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  unfold higham23MillerExactProduct higham23MillerExactU
    higham23MillerExactV higham23MillerFlattenU
    higham23MillerFlattenV higham23MillerFlatten
    higham23BilinearProduct
  have hU := higham23_miller_flat_sum (h := h)
    (fun x y ↦ alg.U k x y * A x y)
  have hV := higham23_miller_flat_sum (h := h)
    (fun x y ↦ alg.V k x y * B x y)
  rw [hU, hV]

theorem higham23_millerExactEvaluate_correct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (halg : alg.IsCorrect)
    (A B : Matrix (Fin h) (Fin h) ℝ) :
    higham23MillerExactEvaluate alg A B = A * B := by
  rw [higham23_millerExactEvaluate_eq_bilinearEvaluate]
  exact halg A B

private theorem higham23_miller_linearForm_error
    (fp : FPModel) (n : ℕ) (hvalid : gammaValid fp n)
    (c x : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hx : ∀ q, |x q| ≤ a) :
    |(∑ q : Fin n, c q * x q) - fl_dotProduct fp n c x| ≤
      gamma fp n * (∑ q : Fin n, |c q|) * a := by
  have hd := dotProduct_error_bound fp n c x hvalid
  have hs : (∑ q : Fin n, |c q| * |x q|) ≤
      (∑ q : Fin n, |c q|) * a := by
    calc
      (∑ q : Fin n, |c q| * |x q|) ≤ ∑ q : Fin n, |c q| * a := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hx q) (abs_nonneg _)
      _ = (∑ q : Fin n, |c q|) * a := by rw [Finset.sum_mul]
  calc
    |(∑ q : Fin n, c q * x q) - fl_dotProduct fp n c x| =
        |fl_dotProduct fp n c x - ∑ q : Fin n, c q * x q| := abs_sub_comm _ _
    _ ≤ gamma fp n * ∑ q : Fin n, |c q| * |x q| := hd
    _ ≤ gamma fp n * ((∑ q : Fin n, |c q|) * a) :=
      mul_le_mul_of_nonneg_left hs (gamma_nonneg fp hvalid)
    _ = _ := by ring

private theorem higham23_miller_linearForm_exact_abs
    (n : ℕ) (c x : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hx : ∀ q, |x q| ≤ a) :
    |∑ q : Fin n, c q * x q| ≤ (∑ q : Fin n, |c q|) * a := by
  calc
    |∑ q : Fin n, c q * x q| ≤ ∑ q : Fin n, |c q * x q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : Fin n, |c q| * a := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hx q) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem higham23_miller_linearForm_fl_abs
    (fp : FPModel) (n : ℕ) (hvalid : gammaValid fp n)
    (c x : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hx : ∀ q, |x q| ≤ a) :
    |fl_dotProduct fp n c x| ≤
      (1 + gamma fp n) * (∑ q : Fin n, |c q|) * a := by
  have he := higham23_miller_linearForm_error fp n hvalid c x a ha hx
  have hn := higham23_miller_linearForm_exact_abs n c x a ha hx
  calc
    |fl_dotProduct fp n c x| ≤
        |∑ q : Fin n, c q * x q| +
          |(∑ q : Fin n, c q * x q) - fl_dotProduct fp n c x| := by
      have h := abs_add_le (∑ q : Fin n, c q * x q)
        (fl_dotProduct fp n c x - ∑ q : Fin n, c q * x q)
      rw [show (∑ q : Fin n, c q * x q) +
        (fl_dotProduct fp n c x - ∑ q : Fin n, c q * x q) =
          fl_dotProduct fp n c x by ring] at h
      simpa [abs_sub_comm] using h
    _ ≤ (∑ q : Fin n, |c q|) * a +
        gamma fp n * (∑ q : Fin n, |c q|) * a := add_le_add hn he
    _ = _ := by ring

noncomputable def higham23MillerProductCore (g u : ℝ) : ℝ :=
  g + (1 + g) * g + u * (1 + g) ^ 2

noncomputable def higham23MillerProductNormCore (g u : ℝ) : ℝ :=
  (1 + u) * (1 + g) ^ 2

noncomputable def higham23MillerCore (g gt u : ℝ) : ℝ :=
  higham23MillerProductCore g u +
    gt * higham23MillerProductNormCore g u

private theorem higham23_miller_product_error
    (fp : FPModel) (g wx wy a b : ℝ)
    (hg : 0 ≤ g) (hwx : 0 ≤ wx) (hwy : 0 ≤ wy)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x xhat y yhat : ℝ)
    (hx : |x| ≤ wx * a) (hy : |y| ≤ wy * b)
    (hex : |x - xhat| ≤ g * wx * a)
    (hey : |y - yhat| ≤ g * wy * b)
    (hxhat : |xhat| ≤ (1 + g) * wx * a)
    (hyhat : |yhat| ≤ (1 + g) * wy * b) :
    |x * y - fp.fl_mul xhat yhat| ≤
      higham23MillerProductCore g fp.u * wx * wy * a * b := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul xhat yhat
  have hinput : |x * y - xhat * yhat| ≤
      g * wx * a * (wy * b) + ((1 + g) * wx * a) * (g * wy * b) := by
    calc
      |x * y - xhat * yhat| = |(x - xhat) * y + xhat * (y - yhat)| := by ring_nf
      _ ≤ |x - xhat| * |y| + |xhat| * |y - yhat| := by
        simpa [abs_mul] using abs_add_le ((x - xhat) * y) (xhat * (y - yhat))
      _ ≤ g * wx * a * (wy * b) + ((1 + g) * wx * a) * (g * wy * b) := by
        exact add_le_add
          (mul_le_mul hex hy (abs_nonneg _) (by positivity))
          (mul_le_mul hxhat hey (abs_nonneg _) (by positivity))
  have hlocal : |xhat * yhat - fp.fl_mul xhat yhat| ≤
      fp.u * ((1 + g) * wx * a) * ((1 + g) * wy * b) := by
    rw [hfl, show xhat * yhat - xhat * yhat * (1 + δ) =
      -(xhat * yhat) * δ by ring, abs_mul, abs_neg, abs_mul]
    calc
      |xhat| * |yhat| * |δ| ≤
          ((1 + g) * wx * a) * ((1 + g) * wy * b) * fp.u := by
        exact mul_le_mul
          (mul_le_mul hxhat hyhat (abs_nonneg _) (by positivity))
          hδ (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    |x * y - fp.fl_mul xhat yhat| ≤
        |x * y - xhat * yhat| + |xhat * yhat - fp.fl_mul xhat yhat| := by
      have h := abs_add_le (x * y - xhat * yhat)
        (xhat * yhat - fp.fl_mul xhat yhat)
      convert h using 1 <;> ring
    _ ≤ _ := by
      rw [higham23MillerProductCore]
      nlinarith

private theorem higham23_miller_product_fl_abs
    (fp : FPModel) (g wx wy a b : ℝ)
    (hg : 0 ≤ g) (hwx : 0 ≤ wx) (hwy : 0 ≤ wy)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (xhat yhat : ℝ)
    (hxhat : |xhat| ≤ (1 + g) * wx * a)
    (hyhat : |yhat| ≤ (1 + g) * wy * b) :
    |fp.fl_mul xhat yhat| ≤
      higham23MillerProductNormCore g fp.u * wx * wy * a * b := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul xhat yhat
  rw [hfl, abs_mul, abs_mul]
  have hone : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ 1 + |δ| := by simpa using abs_add_le 1 δ
      _ ≤ 1 + fp.u := by linarith
  calc
    |xhat| * |yhat| * |1 + δ| ≤
        ((1 + g) * wx * a) * ((1 + g) * wy * b) * (1 + fp.u) := by
      exact mul_le_mul
        (mul_le_mul hxhat hyhat (abs_nonneg _) (by positivity))
        hone (abs_nonneg _) (by positivity)
    _ = _ := by unfold higham23MillerProductNormCore; ring

noncomputable def higham23MillerWeight {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (i j : Fin h) : ℝ :=
  ∑ k : Fin t, |alg.W i j k| *
    higham23MillerUWeight alg k * higham23MillerVWeight alg k

noncomputable def higham23MillerWeightTotal {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) : ℝ :=
  ∑ i : Fin h, ∑ j : Fin h, higham23MillerWeight alg i j

theorem higham23_miller_literalCircuit_exact_error
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b)
    (i j : Fin h) :
    |higham23MillerExactEvaluate alg A B i j -
        higham23MillerFlEvaluate fp alg A B i j| ≤
      higham23MillerCore (gamma fp (h * h)) (gamma fp t) fp.u *
        higham23MillerWeight alg i j * a * b := by
  let g := gamma fp (h * h)
  let gt := gamma fp t
  have hg : 0 ≤ g := gamma_nonneg fp hLinear
  have hgt : 0 ≤ gt := gamma_nonneg fp hOutput
  have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hUWeight (k : Fin t) : 0 ≤ higham23MillerUWeight alg k := by
    unfold higham23MillerUWeight
    positivity
  have hVWeight (k : Fin t) : 0 ≤ higham23MillerVWeight alg k := by
    unfold higham23MillerVWeight
    positivity
  have hAflat (q : Fin (h * h)) : |higham23MillerFlatten A q| ≤ a := by
    exact hA _ _
  have hBflat (q : Fin (h * h)) : |higham23MillerFlatten B q| ≤ b := by
    exact hB _ _
  have hUexact (k : Fin t) :
      |higham23MillerExactU alg A k| ≤ higham23MillerUWeight alg k * a := by
    simpa [higham23MillerExactU, higham23MillerUWeight] using
      higham23_miller_linearForm_exact_abs (h * h)
        (higham23MillerFlattenU alg k) (higham23MillerFlatten A) a ha hAflat
  have hVexact (k : Fin t) :
      |higham23MillerExactV alg B k| ≤ higham23MillerVWeight alg k * b := by
    simpa [higham23MillerExactV, higham23MillerVWeight] using
      higham23_miller_linearForm_exact_abs (h * h)
        (higham23MillerFlattenV alg k) (higham23MillerFlatten B) b hb hBflat
  have hUerr (k : Fin t) :
      |higham23MillerExactU alg A k - higham23MillerFlU fp alg A k| ≤
        g * higham23MillerUWeight alg k * a := by
    simpa [g, higham23MillerExactU, higham23MillerFlU,
      higham23MillerUWeight] using
      higham23_miller_linearForm_error fp (h * h) hLinear
        (higham23MillerFlattenU alg k) (higham23MillerFlatten A) a ha hAflat
  have hVerr (k : Fin t) :
      |higham23MillerExactV alg B k - higham23MillerFlV fp alg B k| ≤
        g * higham23MillerVWeight alg k * b := by
    simpa [g, higham23MillerExactV, higham23MillerFlV,
      higham23MillerVWeight] using
      higham23_miller_linearForm_error fp (h * h) hLinear
        (higham23MillerFlattenV alg k) (higham23MillerFlatten B) b hb hBflat
  have hUfl (k : Fin t) :
      |higham23MillerFlU fp alg A k| ≤
        (1 + g) * higham23MillerUWeight alg k * a := by
    simpa [g, higham23MillerFlU, higham23MillerUWeight] using
      higham23_miller_linearForm_fl_abs fp (h * h) hLinear
        (higham23MillerFlattenU alg k) (higham23MillerFlatten A) a ha hAflat
  have hVfl (k : Fin t) :
      |higham23MillerFlV fp alg B k| ≤
        (1 + g) * higham23MillerVWeight alg k * b := by
    simpa [g, higham23MillerFlV, higham23MillerVWeight] using
      higham23_miller_linearForm_fl_abs fp (h * h) hLinear
        (higham23MillerFlattenV alg k) (higham23MillerFlatten B) b hb hBflat
  have hProductErr (k : Fin t) :
      |higham23MillerExactProduct alg A B k -
          higham23MillerFlProduct fp alg A B k| ≤
        higham23MillerProductCore g fp.u *
          higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b := by
    simpa [higham23MillerExactProduct, higham23MillerFlProduct] using
      higham23_miller_product_error fp g
        (higham23MillerUWeight alg k) (higham23MillerVWeight alg k) a b
        hg (hUWeight k) (hVWeight k) ha hb
        (higham23MillerExactU alg A k) (higham23MillerFlU fp alg A k)
        (higham23MillerExactV alg B k) (higham23MillerFlV fp alg B k)
        (hUexact k) (hVexact k) (hUerr k) (hVerr k) (hUfl k) (hVfl k)
  have hProductNorm (k : Fin t) :
      |higham23MillerFlProduct fp alg A B k| ≤
        higham23MillerProductNormCore g fp.u *
          higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b := by
    simpa [higham23MillerFlProduct] using
      higham23_miller_product_fl_abs fp g
        (higham23MillerUWeight alg k) (higham23MillerVWeight alg k) a b
        hg (hUWeight k) (hVWeight k) ha hb
        (higham23MillerFlU fp alg A k) (higham23MillerFlV fp alg B k)
        (hUfl k) (hVfl k)
  let mid := ∑ k : Fin t, alg.W i j k * higham23MillerFlProduct fp alg A B k
  have hProducts :
      |higham23MillerExactEvaluate alg A B i j - mid| ≤
        higham23MillerProductCore g fp.u * higham23MillerWeight alg i j * a * b := by
    unfold higham23MillerExactEvaluate
    dsimp only [mid]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k : Fin t, (alg.W i j k * higham23MillerExactProduct alg A B k -
          alg.W i j k * higham23MillerFlProduct fp alg A B k)| ≤
          ∑ k : Fin t, |alg.W i j k * higham23MillerExactProduct alg A B k -
            alg.W i j k * higham23MillerFlProduct fp alg A B k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin t, |alg.W i j k| *
          (higham23MillerProductCore g fp.u *
            higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b) := by
        apply Finset.sum_le_sum
        intro k _
        rw [show alg.W i j k * higham23MillerExactProduct alg A B k -
          alg.W i j k * higham23MillerFlProduct fp alg A B k =
            alg.W i j k * (higham23MillerExactProduct alg A B k -
              higham23MillerFlProduct fp alg A B k) by ring, abs_mul]
        exact mul_le_mul_of_nonneg_left (hProductErr k) (abs_nonneg _)
      _ = higham23MillerProductCore g fp.u *
          higham23MillerWeight alg i j * a * b := by
        unfold higham23MillerWeight
        calc
          (∑ k : Fin t, |alg.W i j k| *
              (higham23MillerProductCore g fp.u *
                higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b)) =
              ∑ k : Fin t, higham23MillerProductCore g fp.u *
                (|alg.W i j k| * higham23MillerUWeight alg k *
                  higham23MillerVWeight alg k) * a * b := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = _ := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have hDotRaw := dotProduct_error_bound fp t (alg.W i j)
    (higham23MillerFlProduct fp alg A B) hOutput
  have hWeightedNorm :
      (∑ k : Fin t, |alg.W i j k| *
          |higham23MillerFlProduct fp alg A B k|) ≤
        higham23MillerProductNormCore g fp.u *
          higham23MillerWeight alg i j * a * b := by
    calc
      (∑ k : Fin t, |alg.W i j k| *
          |higham23MillerFlProduct fp alg A B k|) ≤
          ∑ k : Fin t, |alg.W i j k| *
            (higham23MillerProductNormCore g fp.u *
              higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hProductNorm k) (abs_nonneg _)
      _ = higham23MillerProductNormCore g fp.u *
          higham23MillerWeight alg i j * a * b := by
        unfold higham23MillerWeight
        calc
          (∑ k : Fin t, |alg.W i j k| *
              (higham23MillerProductNormCore g fp.u *
                higham23MillerUWeight alg k * higham23MillerVWeight alg k * a * b)) =
              ∑ k : Fin t, higham23MillerProductNormCore g fp.u *
                (|alg.W i j k| * higham23MillerUWeight alg k *
                  higham23MillerVWeight alg k) * a * b := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = _ := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have hDot : |mid - higham23MillerFlEvaluate fp alg A B i j| ≤
      gt * higham23MillerProductNormCore g fp.u *
        higham23MillerWeight alg i j * a * b := by
    unfold higham23MillerFlEvaluate
    dsimp only [mid]
    calc
      |(∑ k : Fin t, alg.W i j k * higham23MillerFlProduct fp alg A B k) -
          fl_dotProduct fp t (alg.W i j) (higham23MillerFlProduct fp alg A B)| =
          |fl_dotProduct fp t (alg.W i j) (higham23MillerFlProduct fp alg A B) -
            ∑ k : Fin t, alg.W i j k * higham23MillerFlProduct fp alg A B k| :=
        abs_sub_comm _ _
      _ ≤ gamma fp t * (∑ k : Fin t, |alg.W i j k| *
          |higham23MillerFlProduct fp alg A B k|) := hDotRaw
      _ ≤ gamma fp t * (higham23MillerProductNormCore g fp.u *
          higham23MillerWeight alg i j * a * b) :=
        mul_le_mul_of_nonneg_left hWeightedNorm hgt
      _ = _ := by dsimp [gt]; ring
  calc
    |higham23MillerExactEvaluate alg A B i j -
        higham23MillerFlEvaluate fp alg A B i j| ≤
      |higham23MillerExactEvaluate alg A B i j - mid| +
        |mid - higham23MillerFlEvaluate fp alg A B i j| := by
      have h := abs_add_le
        (higham23MillerExactEvaluate alg A B i j - mid)
        (mid - higham23MillerFlEvaluate fp alg A B i j)
      convert h using 1 <;> ring
    _ ≤ higham23MillerProductCore g fp.u * higham23MillerWeight alg i j * a * b +
      gt * higham23MillerProductNormCore g fp.u *
        higham23MillerWeight alg i j * a * b := add_le_add hProducts hDot
    _ = _ := by unfold higham23MillerCore; dsimp [g, gt]; ring

/-- Miller's (23.11) for the fully specified finite bilinear circuit, at an
exact nonlinear radius. -/
theorem higham23_eq23_11_miller_exact
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) :
    ∀ i j,
      |(A * B) i j - higham23MillerFlEvaluate fp alg A B i j| ≤
        higham23MillerCore (gamma fp (h * h)) (gamma fp t) fp.u *
          higham23MillerWeight alg i j * a * b := by
  intro i j
  rw [← higham23_millerExactEvaluate_correct alg halg A B]
  exact higham23_miller_literalCircuit_exact_error fp alg hLinear hOutput
    A B a b ha hb hA hB i j

noncomputable def higham23MillerGammaFamily (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) * u + higham23GammaRemainder n u

noncomputable def higham23MillerCoreFamily (h t : ℕ) (u : ℝ) : ℝ :=
  higham23MillerCore (higham23MillerGammaFamily (h * h) u)
    (higham23MillerGammaFamily t u) u

noncomputable def higham23MillerFirstOrderCoefficient (h t : ℕ) : ℝ :=
  2 * (h * h : ℕ) + 1 + t

noncomputable def higham23MillerRemainder (h t : ℕ) (u : ℝ) : ℝ :=
  higham23MillerCoreFamily h t u -
    higham23MillerFirstOrderCoefficient h t * u

theorem higham23_millerCore_eq_family
    (fp : FPModel) (h t : ℕ)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    higham23MillerCore (gamma fp (h * h)) (gamma fp t) fp.u =
      higham23MillerCoreFamily h t fp.u := by
  rw [higham23_gamma_split fp (h * h) hLinear,
    higham23_gamma_split fp t hOutput]
  rfl

theorem higham23_millerRemainder_isBigO_u_sq (h t : ℕ) :
    (fun u : ℝ ↦ higham23MillerRemainder h t u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  let rN : ℝ → ℝ := higham23GammaRemainder (h * h)
  let rT : ℝ → ℝ := higham23GammaRemainder t
  let g : ℝ → ℝ := higham23MillerGammaFamily (h * h)
  let gt : ℝ → ℝ := higham23MillerGammaFamily t
  have hrN : rN =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    higham23_gammaRemainder_isBigO_u_sq (h * h)
  have hrT : rT =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    higham23_gammaRemainder_isBigO_u_sq t
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_id.isBigO_one ℝ
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [pow_two, mul_one] using hu.mul huOne
  have hg : g =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hlin := hu.const_mul_left (((h * h : ℕ) : ℝ))
    have hsum := hlin.add (hrN.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [g, rN, higham23MillerGammaFamily]
    · exact Filter.EventuallyEq.rfl
  have hgt : gt =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hlin := hu.const_mul_left ((t : ℝ))
    have hsum := hlin.add (hrT.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [gt, rT, higham23MillerGammaFamily]
    · exact Filter.EventuallyEq.rfl
  have hgg : (fun u : ℝ ↦ g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hg.mul hg
  have hug : (fun u : ℝ ↦ u * g u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul hg
  have hug2 : (fun u : ℝ ↦ u * g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := huOne.mul hgg
    simpa only [one_mul] using h
  let fminus : ℝ → ℝ := fun u ↦
    u + 2 * g u + 2 * u * g u + g u ^ 2 + u * g u ^ 2
  have hfminus : fminus =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have h2g := hg.const_mul_left (2 : ℝ)
    have h2ug := hug.const_mul_left (2 : ℝ)
    have hquad := (h2ug.add hgg).add hug2
    have hquadOu := hquad.trans huSqOu
    have hlin := hu.add h2g
    have hsum := hlin.add hquadOu
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [fminus]
        ring
    · exact Filter.EventuallyEq.rfl
  have hgtf : (fun u : ℝ ↦ gt u * fminus u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hgt.mul hfminus
  have hsum :=
    (((hrN.const_mul_left (2 : ℝ)).add hgg).add
      (hug.const_mul_left (2 : ℝ))).add hug2
  have hsum := (hsum.add hrT).add hgtf
  apply hsum.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      dsimp [higham23MillerRemainder, higham23MillerCoreFamily,
        higham23MillerCore, higham23MillerProductCore,
        higham23MillerProductNormCore, higham23MillerFirstOrderCoefficient,
        g, gt, rN, rT, fminus, higham23MillerGammaFamily]
      push_cast
      ring
  · exact Filter.EventuallyEq.rfl

theorem higham23_eq23_11_miller_firstOrder
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) :
    ∀ i j,
      |(A * B) i j - higham23MillerFlEvaluate fp alg A B i j| ≤
        ((higham23MillerFirstOrderCoefficient h t *
            higham23MillerWeight alg i j) * fp.u +
          higham23MillerRemainder h t fp.u *
            higham23MillerWeight alg i j) * a * b := by
  intro i j
  have hExact := higham23_eq23_11_miller_exact fp alg halg hLinear hOutput
    A B a b ha hb hA hB i j
  rw [higham23_millerCore_eq_family fp h t hLinear hOutput] at hExact
  have hsplit : higham23MillerCoreFamily h t fp.u =
      higham23MillerFirstOrderCoefficient h t * fp.u +
        higham23MillerRemainder h t fp.u := by
    unfold higham23MillerRemainder
    ring
  rw [hsplit] at hExact
  convert hExact using 1 <;> ring

theorem higham23_miller_weight_nonneg {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (i j : Fin h) :
    0 ≤ higham23MillerWeight alg i j := by
  unfold higham23MillerWeight higham23MillerUWeight higham23MillerVWeight
  positivity

theorem higham23_miller_weight_le_total {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (i j : Fin h) :
    higham23MillerWeight alg i j ≤ higham23MillerWeightTotal alg := by
  unfold higham23MillerWeightTotal
  have hj : higham23MillerWeight alg i j ≤
      ∑ y : Fin h, higham23MillerWeight alg i y := by
    exact Finset.single_le_sum
      (fun y _ ↦ higham23_miller_weight_nonneg alg i y) (Finset.mem_univ j)
  have hi : (∑ y : Fin h, higham23MillerWeight alg i y) ≤
      ∑ x : Fin h, ∑ y : Fin h, higham23MillerWeight alg x y := by
    exact Finset.single_le_sum
      (fun x _ ↦ Finset.sum_nonneg fun y _ ↦
        higham23_miller_weight_nonneg alg x y) (Finset.mem_univ i)
  exact hj.trans hi

theorem higham23_miller_normwiseRemainder_isBigO_u_sq {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) :
    (fun u : ℝ ↦ higham23MillerRemainder h t u *
      higham23MillerWeightTotal alg) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  simpa only [mul_comm] using
    (higham23_millerRemainder_isBigO_u_sq h t).const_mul_left
      (higham23MillerWeightTotal alg)

/-- The max-entry form of Miller's (23.11): an explicit algorithm-dependent
`f_n`, plus a genuinely quadratic remainder, for the literal rounded
polynomial circuit above. -/
theorem higham23_eq23_11_miller_normwise
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) :
    ∀ i j,
      |(A * B) i j - higham23MillerFlEvaluate fp alg A B i j| ≤
        ((higham23MillerFirstOrderCoefficient h t *
            higham23MillerWeightTotal alg) * fp.u +
          higham23MillerRemainder h t fp.u *
            higham23MillerWeightTotal alg) * a * b := by
  intro i j
  have hEntry := higham23_eq23_11_miller_firstOrder fp alg halg hLinear hOutput
    A B a b ha hb hA hB i j
  let q := higham23MillerWeight alg i j
  let Q := higham23MillerWeightTotal alg
  let c := higham23MillerFirstOrderCoefficient h t
  let R := higham23MillerRemainder h t fp.u
  have hqQ : q ≤ Q := higham23_miller_weight_le_total alg i j
  have hcoreNonneg : 0 ≤ c * fp.u + R := by
    have heq : c * fp.u + R = higham23MillerCoreFamily h t fp.u := by
      dsimp [c, R, higham23MillerRemainder]
      ring
    rw [heq, ← higham23_millerCore_eq_family fp h t hLinear hOutput]
    unfold higham23MillerCore higham23MillerProductCore
      higham23MillerProductNormCore
    have hg := gamma_nonneg fp hLinear
    have hgt := gamma_nonneg fp hOutput
    have hu : 0 ≤ fp.u := fp.u_nonneg
    have hg1 : 0 ≤ 1 + gamma fp (h * h) := by linarith
    have hu1 : 0 ≤ 1 + fp.u := by linarith
    positivity
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hscale := mul_le_mul_of_nonneg_left hqQ hcoreNonneg
  have hscale' := mul_le_mul_of_nonneg_right hscale hab
  apply le_trans hEntry
  change ((c * q) * fp.u + R * q) * a * b ≤
    ((c * Q) * fp.u + R * Q) * a * b
  calc
    ((c * q) * fp.u + R * q) * a * b =
        (c * fp.u + R) * q * (a * b) := by ring
    _ ≤ (c * fp.u + R) * Q * (a * b) := hscale'
    _ = ((c * Q) * fp.u + R * Q) * a * b := by ring

end NumStability
