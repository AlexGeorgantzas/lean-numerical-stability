/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.FastMatMul.Higham23Remaining

namespace NumStability

open scoped Topology BigOperators
open Filter

/-!
# Bini--Lotti recursive bilinear evaluator

The evaluator in this file is a literal recursive implementation of (23.7):
all coefficient-weighted linear forms and output reconstructions are rounded
at their scalar leaves, and every nonscalar product is a recursive call.
-/

abbrev Higham23BiniMatrix (h : ℕ) : ℕ → Type
  | 0 => ℝ
  | depth + 1 => Matrix (Fin h) (Fin h) (Higham23BiniMatrix h depth)

noncomputable def higham23BiniExactDot (h n : ℕ) :
    ∀ depth, (Fin n → ℝ) → (Fin n → Higham23BiniMatrix h depth) →
      Higham23BiniMatrix h depth
  | 0, c, X => ∑ q, c q * X q
  | depth + 1, c, X => fun i j ↦
      higham23BiniExactDot h n depth c (fun q ↦ X q i j)

noncomputable def higham23BiniAdd (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, x, y => x + y
  | depth + 1, X, Y => fun i j ↦ higham23BiniAdd h depth (X i j) (Y i j)

noncomputable def higham23BiniSub (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, x, y => x - y
  | depth + 1, X, Y => fun i j ↦ higham23BiniSub h depth (X i j) (Y i j)

noncomputable def higham23BiniMul (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, x, y => x * y
  | depth + 1, A, B => fun i j ↦
      higham23BiniExactDot h h depth (fun _ ↦ (1 : ℝ))
        (fun k ↦ higham23BiniMul h depth (A i k) (B k j))

noncomputable def higham23BiniFlDot (fp : FPModel) (h n : ℕ) :
    ∀ depth, (Fin n → ℝ) → (Fin n → Higham23BiniMatrix h depth) →
      Higham23BiniMatrix h depth
  | 0, c, X => fl_dotProduct fp n c X
  | depth + 1, c, X => fun i j ↦
      higham23BiniFlDot fp h n depth c (fun q ↦ X q i j)

def Higham23BiniNormLe (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → ℝ → Prop
  | 0, x, a => |x| ≤ a
  | depth + 1, A, a => ∀ i j, Higham23BiniNormLe h depth (A i j) a

def Higham23BiniErrorLe (h : ℕ) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth → ℝ → Prop
  | 0, x, y, e => |x - y| ≤ e
  | depth + 1, A, B, e => ∀ i j, Higham23BiniErrorLe h depth (A i j) (B i j) e

theorem higham23_biniError_refl (h : ℕ) :
    ∀ depth (X : Higham23BiniMatrix h depth), Higham23BiniErrorLe h depth X X 0
  | 0, X => by simp [Higham23BiniErrorLe]
  | depth + 1, X => fun i j ↦ higham23_biniError_refl h depth (X i j)

theorem higham23_biniError_symm (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e : ℝ},
      Higham23BiniErrorLe h depth X Y e → Higham23BiniErrorLe h depth Y X e
  | 0, X, Y, e, hE => by simpa [Higham23BiniErrorLe, abs_sub_comm] using hE
  | depth + 1, X, Y, e, hE => fun i j ↦
      higham23_biniError_symm h depth (X i j) (Y i j) (hE i j)

theorem higham23_biniError_trans (h : ℕ) :
    ∀ depth (X Y Z : Higham23BiniMatrix h depth) {e f : ℝ},
      Higham23BiniErrorLe h depth X Y e →
      Higham23BiniErrorLe h depth Y Z f →
      Higham23BiniErrorLe h depth X Z (e + f)
  | 0, X, Y, Z, e, f, hXY, hYZ => by
      change |X - Z| ≤ e + f
      calc
        |X - Z| ≤ |X - Y| + |Y - Z| := by
          have h := abs_add_le (X - Y) (Y - Z)
          convert h using 1 <;> ring
        _ ≤ e + f := add_le_add hXY hYZ
  | depth + 1, X, Y, Z, e, f, hXY, hYZ => fun i j ↦
      higham23_biniError_trans h depth (X i j) (Y i j) (Z i j)
        (hXY i j) (hYZ i j)

theorem higham23_biniError_mono (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e f : ℝ},
      Higham23BiniErrorLe h depth X Y e → e ≤ f →
      Higham23BiniErrorLe h depth X Y f
  | 0, X, Y, e, f, hE, hef => hE.trans hef
  | depth + 1, X, Y, e, f, hE, hef => fun i j ↦
      higham23_biniError_mono h depth (X i j) (Y i j) (hE i j) hef

theorem higham23_biniNorm_of_error (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {a e : ℝ},
      Higham23BiniNormLe h depth X a → Higham23BiniErrorLe h depth X Y e →
      Higham23BiniNormLe h depth Y (a + e)
  | 0, X, Y, a, e, hX, hE => by
      change |Y| ≤ a + e
      calc
        |Y| ≤ |X| + |X - Y| := by
          have h := abs_add_le X (Y - X)
          rw [show X + (Y - X) = Y by ring] at h
          simpa [abs_sub_comm] using h
        _ ≤ a + e := add_le_add hX hE
  | depth + 1, X, Y, a, e, hX, hE => fun i j ↦
      higham23_biniNorm_of_error h depth (X i j) (Y i j) (hX i j) (hE i j)

/-- A varying-radius leafwise dot-product certificate. -/
theorem higham23_biniFlDot_certificate
    (fp : FPModel) (h n : ℕ) (hvalid : gammaValid fp n) :
    ∀ depth (c : Fin n → ℝ)
      (X Xhat : Fin n → Higham23BiniMatrix h depth)
      (e rad : Fin n → ℝ),
      (∀ q, 0 ≤ e q) → (∀ q, 0 ≤ rad q) →
      (∀ q, Higham23BiniErrorLe h depth (X q) (Xhat q) (e q)) →
      (∀ q, Higham23BiniNormLe h depth (Xhat q) (rad q)) →
      Higham23BiniErrorLe h depth (higham23BiniExactDot h n depth c X)
        (higham23BiniFlDot fp h n depth c Xhat)
        ((∑ q, |c q| * e q) + gamma fp n * (∑ q, |c q| * rad q)) ∧
      Higham23BiniNormLe h depth (higham23BiniFlDot fp h n depth c Xhat)
        ((1 + gamma fp n) * (∑ q, |c q| * rad q))
  | 0, c, X, Xhat, e, rad, he0, hr0, hE, hN => by
      have hinput : |(∑ q, c q * X q) - ∑ q, c q * Xhat q| ≤
          ∑ q, |c q| * e q := by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ q, (c q * X q - c q * Xhat q)| ≤
              ∑ q, |c q * X q - c q * Xhat q| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ q, |c q| * e q := by
            apply Finset.sum_le_sum
            intro q _
            rw [show c q * X q - c q * Xhat q = c q * (X q - Xhat q) by ring,
              abs_mul]
            exact mul_le_mul_of_nonneg_left (hE q) (abs_nonneg _)
      have hweighted : (∑ q, |c q| * |Xhat q|) ≤ ∑ q, |c q| * rad q := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hN q) (abs_nonneg _)
      have hlocalRaw := dotProduct_error_bound fp n c Xhat hvalid
      have hlocal : |(∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat| ≤
          gamma fp n * (∑ q, |c q| * rad q) := by
        rw [abs_sub_comm]
        exact hlocalRaw.trans
          (mul_le_mul_of_nonneg_left hweighted (gamma_nonneg fp hvalid))
      have htotal : |(∑ q, c q * X q) - fl_dotProduct fp n c Xhat| ≤
          (∑ q, |c q| * e q) + gamma fp n * (∑ q, |c q| * rad q) := by
        calc
          |(∑ q, c q * X q) - fl_dotProduct fp n c Xhat| ≤
              |(∑ q, c q * X q) - ∑ q, c q * Xhat q| +
                |(∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat| := by
            have hh := abs_add_le
              ((∑ q, c q * X q) - ∑ q, c q * Xhat q)
              ((∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat)
            convert hh using 1 <;> ring
          _ ≤ _ := add_le_add hinput hlocal
      have hExactHat : |∑ q, c q * Xhat q| ≤ ∑ q, |c q| * rad q := by
        calc
          |∑ q, c q * Xhat q| ≤ ∑ q, |c q * Xhat q| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ q, |c q| * rad q := by
            apply Finset.sum_le_sum
            intro q _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hN q) (abs_nonneg _)
      have hflNorm : |fl_dotProduct fp n c Xhat| ≤
          (1 + gamma fp n) * (∑ q, |c q| * rad q) := by
        calc
          |fl_dotProduct fp n c Xhat| ≤ |∑ q, c q * Xhat q| +
              |(∑ q, c q * Xhat q) - fl_dotProduct fp n c Xhat| := by
            have hh := abs_add_le (∑ q, c q * Xhat q)
              (fl_dotProduct fp n c Xhat - ∑ q, c q * Xhat q)
            rw [show (∑ q, c q * Xhat q) +
              (fl_dotProduct fp n c Xhat - ∑ q, c q * Xhat q) =
                fl_dotProduct fp n c Xhat by ring] at hh
            simpa [abs_sub_comm] using hh
          _ ≤ (∑ q, |c q| * rad q) +
              gamma fp n * (∑ q, |c q| * rad q) :=
            add_le_add hExactHat hlocal
          _ = _ := by ring
      exact ⟨htotal, hflNorm⟩
  | depth + 1, c, X, Xhat, e, rad, he0, hr0, hE, hN => by
      constructor
      · intro i j
        exact (higham23_biniFlDot_certificate fp h n hvalid depth c
          (fun q ↦ X q i j) (fun q ↦ Xhat q i j) e rad he0 hr0
          (fun q ↦ hE q i j) (fun q ↦ hN q i j)).1
      · intro i j
        exact (higham23_biniFlDot_certificate fp h n hvalid depth c
          (fun q ↦ X q i j) (fun q ↦ Xhat q i j) e rad he0 hr0
          (fun q ↦ hE q i j) (fun q ↦ hN q i j)).2

theorem higham23_biniExactDot_norm (h n : ℕ) :
    ∀ depth (c : Fin n → ℝ) (X : Fin n → Higham23BiniMatrix h depth)
      (rad : Fin n → ℝ),
      (∀ q, 0 ≤ rad q) →
      (∀ q, Higham23BiniNormLe h depth (X q) (rad q)) →
      Higham23BiniNormLe h depth (higham23BiniExactDot h n depth c X)
        (∑ q, |c q| * rad q)
  | 0, c, X, rad, _hr0, hN => by
      calc
        |∑ q, c q * X q| ≤ ∑ q, |c q * X q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q, |c q| * rad q := by
          apply Finset.sum_le_sum
          intro q _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hN q) (abs_nonneg _)
  | depth + 1, c, X, rad, hr0, hN => fun i j ↦
      higham23_biniExactDot_norm h n depth c (fun q ↦ X q i j) rad hr0
        (fun q ↦ hN q i j)

theorem higham23_biniNorm_add (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {a b : ℝ},
      Higham23BiniNormLe h depth X a → Higham23BiniNormLe h depth Y b →
      Higham23BiniNormLe h depth (higham23BiniAdd h depth X Y) (a + b)
  | 0, X, Y, a, b, hX, hY => by
      exact (abs_add_le X Y).trans (add_le_add hX hY)
  | depth + 1, X, Y, a, b, hX, hY => fun i j ↦
      higham23_biniNorm_add h depth (X i j) (Y i j) (hX i j) (hY i j)

theorem higham23_biniNorm_sub_of_error (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e : ℝ},
      Higham23BiniErrorLe h depth X Y e →
      Higham23BiniNormLe h depth (higham23BiniSub h depth X Y) e
  | 0, X, Y, e, hE => hE
  | depth + 1, X, Y, e, hE => fun i j ↦
      higham23_biniNorm_sub_of_error h depth (X i j) (Y i j) (hE i j)

theorem higham23_biniError_of_norm_sub (h : ℕ) :
    ∀ depth (X Y : Higham23BiniMatrix h depth) {e : ℝ},
      Higham23BiniNormLe h depth (higham23BiniSub h depth X Y) e →
      Higham23BiniErrorLe h depth X Y e
  | 0, X, Y, e, hE => hE
  | depth + 1, X, Y, e, hE => fun i j ↦
      higham23_biniError_of_norm_sub h depth (X i j) (Y i j) (hE i j)

theorem higham23_biniNorm_mul (h : ℕ) :
    ∀ depth (A B : Higham23BiniMatrix h depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23BiniNormLe h depth A a → Higham23BiniNormLe h depth B b →
      Higham23BiniNormLe h depth (higham23BiniMul h depth A B)
        (((h ^ depth : ℕ) : ℝ) * a * b)
  | 0, A, B, a, b, ha, _hb, hA, hB => by
      change |A * B| ≤ _
      rw [abs_mul]
      have hh := mul_le_mul hA hB (abs_nonneg _) ha
      simpa using hh
  | depth + 1, A, B, a, b, ha, hb, hA, hB => by
      intro i j
      let nrad : ℝ := ((h ^ depth : ℕ) : ℝ) * a * b
      have hprod (k : Fin h) : Higham23BiniNormLe h depth
          (higham23BiniMul h depth (A i k) (B k j)) nrad :=
        higham23_biniNorm_mul h depth (A i k) (B k j) a b ha hb
          (hA i k) (hB k j)
      have hsum := higham23_biniExactDot_norm h h depth
        (fun _ ↦ (1 : ℝ))
        (fun k ↦ higham23BiniMul h depth (A i k) (B k j)) (fun _ ↦ nrad)
        (fun _ ↦ by dsimp [nrad]; positivity) hprod
      have hpow : (∑ _k : Fin h, |(1 : ℝ)| * nrad) =
          (((h ^ (depth + 1) : ℕ) : ℝ) * a * b) := by
        simp [nrad, pow_succ]
        push_cast
        ring
      rw [← hpow]
      exact hsum

theorem higham23_biniExactDot_error (h n : ℕ) :
    ∀ depth (c : Fin n → ℝ)
      (X Y : Fin n → Higham23BiniMatrix h depth) (e : Fin n → ℝ),
      (∀ q, 0 ≤ e q) →
      (∀ q, Higham23BiniErrorLe h depth (X q) (Y q) (e q)) →
      Higham23BiniErrorLe h depth
        (higham23BiniExactDot h n depth c X)
        (higham23BiniExactDot h n depth c Y)
        (∑ q, |c q| * e q)
  | 0, c, X, Y, e, _he0, hE => by
      change |(∑ q, c q * X q) - ∑ q, c q * Y q| ≤ ∑ q, |c q| * e q
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ q, (c q * X q - c q * Y q)| ≤
            ∑ q, |c q * X q - c q * Y q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q, |c q| * e q := by
          apply Finset.sum_le_sum
          intro q _
          rw [show c q * X q - c q * Y q = c q * (X q - Y q) by ring,
            abs_mul]
          exact mul_le_mul_of_nonneg_left (hE q) (abs_nonneg _)
  | depth + 1, c, X, Y, e, he0, hE => fun i j ↦
      higham23_biniExactDot_error h n depth c
        (fun q ↦ X q i j) (fun q ↦ Y q i j) e he0 (fun q ↦ hE q i j)

theorem higham23_biniError_mul (h : ℕ) :
    ∀ depth (A Ahat B Bhat : Higham23BiniMatrix h depth)
      (aHat b dx dy : ℝ),
      0 ≤ aHat → 0 ≤ b → 0 ≤ dx → 0 ≤ dy →
      Higham23BiniNormLe h depth Ahat aHat →
      Higham23BiniNormLe h depth B b →
      Higham23BiniErrorLe h depth Ahat A dx →
      Higham23BiniErrorLe h depth Bhat B dy →
      Higham23BiniErrorLe h depth
        (higham23BiniMul h depth Ahat Bhat) (higham23BiniMul h depth A B)
        (((h ^ depth : ℕ) : ℝ) * dx * b +
          ((h ^ depth : ℕ) : ℝ) * aHat * dy)
  | 0, A, Ahat, B, Bhat, aHat, b, dx, dy,
      haHat, hb, hdx, hdy, hAhat, hB, hAerr, hBerr => by
      change |Ahat * Bhat - A * B| ≤ _
      calc
        |Ahat * Bhat - A * B| = |(Ahat - A) * B + Ahat * (Bhat - B)| := by ring_nf
        _ ≤ |Ahat - A| * |B| + |Ahat| * |Bhat - B| := by
          simpa [abs_mul] using abs_add_le ((Ahat - A) * B) (Ahat * (Bhat - B))
        _ ≤ dx * b + aHat * dy := by
          exact add_le_add
            (mul_le_mul hAerr hB (abs_nonneg _) hdx)
            (mul_le_mul hAhat hBerr (abs_nonneg _) haHat)
        _ = _ := by norm_num
  | depth + 1, A, Ahat, B, Bhat, aHat, b, dx, dy,
      haHat, hb, hdx, hdy, hAhat, hB, hAerr, hBerr => by
      intro i j
      let er : ℝ := (((h ^ depth : ℕ) : ℝ) * dx * b +
        ((h ^ depth : ℕ) : ℝ) * aHat * dy)
      have hterm (k : Fin h) : Higham23BiniErrorLe h depth
          (higham23BiniMul h depth (Ahat i k) (Bhat k j))
          (higham23BiniMul h depth (A i k) (B k j)) er :=
        higham23_biniError_mul h depth (A i k) (Ahat i k) (B k j) (Bhat k j)
          aHat b dx dy haHat hb hdx hdy (hAhat i k) (hB k j)
          (hAerr i k) (hBerr k j)
      have hsum := higham23_biniExactDot_error h h depth
        (fun _ ↦ (1 : ℝ))
        (fun k ↦ higham23BiniMul h depth (Ahat i k) (Bhat k j))
        (fun k ↦ higham23BiniMul h depth (A i k) (B k j))
        (fun _ ↦ er) (fun _ ↦ by dsimp [er]; positivity) hterm
      convert hsum using 1 <;> dsimp [er] <;> simp [pow_succ] <;> push_cast <;> ring

structure Higham23BiniCertificate (h depth : ℕ)
    (X Xhat : Higham23BiniMatrix h depth) (error norm : ℝ) : Prop where
  error_le : Higham23BiniErrorLe h depth X Xhat error
  norm_le : Higham23BiniNormLe h depth Xhat norm

theorem higham23_biniCertificate_product (h depth : ℕ)
    (X Xhat Y Yhat P : Higham23BiniMatrix h depth)
    (yExact ex nx ey ny e : ℝ)
    (hyExact : 0 ≤ yExact) (hex : 0 ≤ ex) (hnx : 0 ≤ nx)
    (hey : 0 ≤ ey) (hny : 0 ≤ ny)
    (hYexact : Higham23BiniNormLe h depth Y yExact)
    (hX : Higham23BiniCertificate h depth X Xhat ex nx)
    (hY : Higham23BiniCertificate h depth Y Yhat ey ny)
    (hRec : Higham23BiniErrorLe h depth (higham23BiniMul h depth Xhat Yhat)
      P (e * nx * ny)) :
    let N : ℝ := ((h ^ depth : ℕ) : ℝ)
    Higham23BiniCertificate h depth (higham23BiniMul h depth X Y) P
      (N * ex * yExact + N * nx * ey + e * nx * ny)
      ((N + e) * nx * ny) := by
  dsimp only
  have hinputComputed := higham23_biniError_mul h depth
    X Xhat Y Yhat nx yExact ex ey hnx hyExact hex hey
    hX.norm_le hYexact
    (higham23_biniError_symm h depth _ _ hX.error_le)
    (higham23_biniError_symm h depth _ _ hY.error_le)
  have hinput := higham23_biniError_symm h depth _ _ hinputComputed
  have herr := higham23_biniError_trans h depth _ _ _ hinput hRec
  have hprod := higham23_biniNorm_mul h depth Xhat Yhat nx ny hnx hny
    hX.norm_le hY.norm_le
  have hout := higham23_biniNorm_of_error h depth _ _ hprod hRec
  constructor
  · exact higham23_biniError_mono h depth _ _ herr (by ring_nf; linarith)
  · convert hout using 1 <;> ring

def higham23BiniFlattenBlock {h depth : ℕ}
    (A : Higham23BiniMatrix h (depth + 1)) (q : Fin (h * h)) :
    Higham23BiniMatrix h depth :=
  A (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

noncomputable def higham23BiniExactLevel {h t depth : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Higham23BiniMatrix h (depth + 1)) :
    Higham23BiniMatrix h (depth + 1) :=
  fun i j ↦ higham23BiniExactDot h t depth (alg.W i j) (fun k ↦
    higham23BiniMul h depth
      (higham23BiniExactDot h (h * h) depth (higham23MillerFlattenU alg k)
        (higham23BiniFlattenBlock A))
      (higham23BiniExactDot h (h * h) depth (higham23MillerFlattenV alg k)
        (higham23BiniFlattenBlock B)))

/-- The noncommutative correctness condition required by Theorem 23.4.  It
is solely an exact tensor identity; no numerical-error conclusion is assumed. -/
def Higham23BilinearAlgorithm.IsNoncommutativeCorrect {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) : Prop :=
  ∀ depth (A B : Higham23BiniMatrix h (depth + 1)),
    higham23BiniExactLevel alg A B = higham23BiniMul h (depth + 1) A B

noncomputable def higham23BiniFlEvaluate
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, A, B => fp.fl_mul A B
  | depth + 1, A, B =>
      let Xhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A)
      let Yhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B)
      let P := fun k : Fin t ↦
        higham23BiniFlEvaluate fp alg depth (Xhat k) (Yhat k)
      fun i j ↦ higham23BiniFlDot fp h t depth (alg.W i j) P

noncomputable def higham23BiniProductErrorCore (N e g : ℝ) : ℝ :=
  N * g + N * (1 + g) * g + e * (1 + g) ^ 2

noncomputable def higham23BiniProductNormCore (N e g : ℝ) : ℝ :=
  (N + e) * (1 + g) ^ 2

noncomputable def higham23BiniStepMajorant
    (K N e g gt : ℝ) : ℝ :=
  K * (higham23BiniProductErrorCore N e g +
    gt * higham23BiniProductNormCore N e g)

noncomputable def higham23BiniExactMajorant
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℕ → ℝ
  | 0 => fp.u
  | depth + 1 =>
      higham23BiniStepMajorant (higham23MillerWeightTotal alg)
        ((h ^ depth : ℕ) : ℝ) (higham23BiniExactMajorant fp alg depth)
        (gamma fp (h * h)) (gamma fp t)

theorem higham23_biniExactMajorant_nonneg
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    ∀ depth, 0 ≤ higham23BiniExactMajorant fp alg depth
  | 0 => fp.u_nonneg
  | depth + 1 => by
      rw [higham23BiniExactMajorant]
      have hK : 0 ≤ higham23MillerWeightTotal alg := by
        unfold higham23MillerWeightTotal
        exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
          higham23_miller_weight_nonneg alg i j
      have hN : 0 ≤ (((h ^ depth : ℕ) : ℝ)) := Nat.cast_nonneg _
      have he := higham23_biniExactMajorant_nonneg fp alg hLinear hOutput depth
      have hg := gamma_nonneg fp hLinear
      have hgt := gamma_nonneg fp hOutput
      unfold higham23BiniStepMajorant higham23BiniProductErrorCore
        higham23BiniProductNormCore
      positivity

/-- Exact nonlinear Bini--Lotti bound for the literal recursive evaluator. -/
theorem higham23_theorem23_4_biniLotti_exactMajorant
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsNoncommutativeCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    ∀ depth (A B : Higham23BiniMatrix h depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23BiniNormLe h depth A a → Higham23BiniNormLe h depth B b →
      Higham23BiniErrorLe h depth (higham23BiniMul h depth A B)
        (higham23BiniFlEvaluate fp alg depth A B)
        (higham23BiniExactMajorant fp alg depth * a * b) := by
  intro depth
  induction depth with
  | zero =>
      intro A B a b ha hb hA hB
      obtain ⟨δ, hδ, hfl⟩ := fp.model_mul A B
      change |A * B - fp.fl_mul A B| ≤ _
      rw [hfl, show A * B - A * B * (1 + δ) = -(A * B) * δ by ring,
        abs_mul, abs_neg, abs_mul]
      calc
        |A| * |B| * |δ| ≤ a * b * fp.u := by
          exact mul_le_mul (mul_le_mul hA hB (abs_nonneg _) ha)
            hδ (abs_nonneg _) (mul_nonneg ha hb)
        _ = _ := by simp [higham23BiniExactMajorant]; ring
  | succ depth ih =>
      intro A B a b ha hb hA hB
      let g := gamma fp (h * h)
      let gt := gamma fp t
      let N : ℝ := ((h ^ depth : ℕ) : ℝ)
      let e := higham23BiniExactMajorant fp alg depth
      let K := higham23MillerWeightTotal alg
      let PE := higham23BiniProductErrorCore N e g
      let PN := higham23BiniProductNormCore N e g
      have hg : 0 ≤ g := gamma_nonneg fp hLinear
      have hgt : 0 ≤ gt := gamma_nonneg fp hOutput
      have hN : 0 ≤ N := by dsimp [N]; positivity
      have he : 0 ≤ e := higham23_biniExactMajorant_nonneg fp alg hLinear hOutput depth
      have hK : 0 ≤ K := by
        dsimp [K, higham23MillerWeightTotal]
        exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
          higham23_miller_weight_nonneg alg i j
      have hPE : 0 ≤ PE := by
        dsimp [PE, higham23BiniProductErrorCore]
        positivity
      have hPN : 0 ≤ PN := by
        dsimp [PN, higham23BiniProductNormCore]
        positivity
      let X := fun k : Fin t ↦
        higham23BiniExactDot h (h * h) depth (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A)
      let Y := fun k : Fin t ↦
        higham23BiniExactDot h (h * h) depth (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B)
      let Xhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A)
      let Yhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B)
      let P := fun k : Fin t ↦ higham23BiniFlEvaluate fp alg depth (Xhat k) (Yhat k)
      have hAflat (q : Fin (h * h)) :
          Higham23BiniNormLe h depth (higham23BiniFlattenBlock A q) a :=
        hA _ _
      have hBflat (q : Fin (h * h)) :
          Higham23BiniNormLe h depth (higham23BiniFlattenBlock B q) b :=
        hB _ _
      have hXcert (k : Fin t) : Higham23BiniCertificate h depth (X k) (Xhat k)
          (g * higham23MillerUWeight alg k * a)
          ((1 + g) * higham23MillerUWeight alg k * a) := by
        have hc := higham23_biniFlDot_certificate fp h (h * h) hLinear depth
          (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A) (higham23BiniFlattenBlock A)
          (fun _ ↦ 0) (fun _ ↦ a) (fun _ ↦ by norm_num) (fun _ ↦ ha)
          (fun q ↦ higham23_biniError_refl h depth _ ) hAflat
        constructor
        · simpa [X, Xhat, g, higham23MillerUWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.1
        · simpa [Xhat, g, higham23MillerUWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.2
      have hYcert (k : Fin t) : Higham23BiniCertificate h depth (Y k) (Yhat k)
          (g * higham23MillerVWeight alg k * b)
          ((1 + g) * higham23MillerVWeight alg k * b) := by
        have hc := higham23_biniFlDot_certificate fp h (h * h) hLinear depth
          (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B) (higham23BiniFlattenBlock B)
          (fun _ ↦ 0) (fun _ ↦ b) (fun _ ↦ by norm_num) (fun _ ↦ hb)
          (fun q ↦ higham23_biniError_refl h depth _) hBflat
        constructor
        · simpa [Y, Yhat, g, higham23MillerVWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.1
        · simpa [Yhat, g, higham23MillerVWeight, pow_two,
            Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
            using hc.2
      have hYexact (k : Fin t) : Higham23BiniNormLe h depth (Y k)
          (higham23MillerVWeight alg k * b) := by
        have hn := higham23_biniExactDot_norm h (h * h) depth
          (higham23MillerFlattenV alg k) (higham23BiniFlattenBlock B)
          (fun _ ↦ b) (fun _ ↦ hb) hBflat
        simpa [Y, higham23MillerVWeight, Finset.mul_sum, Finset.sum_mul,
          mul_comm, mul_left_comm, mul_assoc] using hn
      have hProduct (k : Fin t) : Higham23BiniCertificate h depth
          (higham23BiniMul h depth (X k) (Y k)) (P k)
          (PE * higham23MillerUWeight alg k *
            higham23MillerVWeight alg k * a * b)
          (PN * higham23MillerUWeight alg k *
            higham23MillerVWeight alg k * a * b) := by
        let uw := higham23MillerUWeight alg k
        let vw := higham23MillerVWeight alg k
        have huw : 0 ≤ uw := by dsimp [uw, higham23MillerUWeight]; positivity
        have hvw : 0 ≤ vw := by dsimp [vw, higham23MillerVWeight]; positivity
        have hrec := ih (Xhat k) (Yhat k) ((1 + g) * uw * a)
          ((1 + g) * vw * b) (by positivity) (by positivity)
          (hXcert k).norm_le (hYcert k).norm_le
        have hp := higham23_biniCertificate_product h depth
          (X k) (Xhat k) (Y k) (Yhat k) (P k)
          (vw * b) (g * uw * a) ((1 + g) * uw * a)
          (g * vw * b) ((1 + g) * vw * b) e
          (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
          (by simpa [vw] using hYexact k)
          (by simpa [uw] using hXcert k) (by simpa [vw] using hYcert k)
          (by simpa [P, e, uw, vw] using hrec)
        constructor
        · convert hp.error_le using 1 <;>
            dsimp [PE, higham23BiniProductErrorCore, N, e, g, uw, vw] <;> ring
        · convert hp.norm_le using 1 <;>
            dsimp [PN, higham23BiniProductNormCore, N, e, g, uw, vw] <;> ring
      have hOutCert (i j : Fin h) := higham23_biniFlDot_certificate fp h t hOutput
        depth (alg.W i j)
        (fun k ↦ higham23BiniMul h depth (X k) (Y k)) P
        (fun k ↦ PE * higham23MillerUWeight alg k *
          higham23MillerVWeight alg k * a * b)
        (fun k ↦ PN * higham23MillerUWeight alg k *
          higham23MillerVWeight alg k * a * b)
        (fun k ↦ by
          have hu : 0 ≤ higham23MillerUWeight alg k := by
            unfold higham23MillerUWeight
            positivity
          have hv : 0 ≤ higham23MillerVWeight alg k := by
            unfold higham23MillerVWeight
            positivity
          positivity)
        (fun k ↦ by
          have hu : 0 ≤ higham23MillerUWeight alg k := by
            unfold higham23MillerUWeight
            positivity
          have hv : 0 ≤ higham23MillerVWeight alg k := by
            unfold higham23MillerVWeight
            positivity
          positivity)
        (fun k ↦ (hProduct k).error_le) (fun k ↦ (hProduct k).norm_le)
      have hCorrect := halg depth A B
      intro i j
      have hEntry := (hOutCert i j).1
      have hWeight := higham23_miller_weight_le_total alg i j
      have hcore : 0 ≤ PE + gt * PN := add_nonneg hPE (mul_nonneg hgt hPN)
      have hscaled := mul_le_mul_of_nonneg_left hWeight hcore
      have hab : 0 ≤ a * b := mul_nonneg ha hb
      have hscaled := mul_le_mul_of_nonneg_right hscaled hab
      have hPEsum :
          (∑ q, |alg.W i j q| * (PE * higham23MillerUWeight alg q *
            higham23MillerVWeight alg q * a * b)) =
            PE * higham23MillerWeight alg i j * (a * b) := by
        rw [higham23MillerWeight]
        calc
          _ = ∑ q, PE * (|alg.W i j q| * higham23MillerUWeight alg q *
                higham23MillerVWeight alg q) * (a * b) := by
              apply Finset.sum_congr rfl
              intro q _
              ring
          _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
      have hPNsum :
          (∑ q, |alg.W i j q| * (PN * higham23MillerUWeight alg q *
            higham23MillerVWeight alg q * a * b)) =
            PN * higham23MillerWeight alg i j * (a * b) := by
        rw [higham23MillerWeight]
        calc
          _ = ∑ q, PN * (|alg.W i j q| * higham23MillerUWeight alg q *
                higham23MillerVWeight alg q) * (a * b) := by
              apply Finset.sum_congr rfl
              intro q _
              ring
          _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
      have hEntry' := higham23_biniError_mono h depth _ _ hEntry
        (show
          (∑ q, |alg.W i j q| * (PE * higham23MillerUWeight alg q *
              higham23MillerVWeight alg q * a * b)) +
            gt * (∑ q, |alg.W i j q| * (PN * higham23MillerUWeight alg q *
              higham23MillerVWeight alg q * a * b)) ≤
            (PE + gt * PN) * higham23MillerWeight alg i j * (a * b) by
          rw [hPEsum, hPNsum]
          ring_nf
          exact le_rfl)
      have hmonoRaw := higham23_biniError_mono h depth _ _ hEntry' hscaled
      have hmono : Higham23BiniErrorLe h depth
          (higham23BiniExactLevel alg A B i j)
          (higham23BiniFlEvaluate fp alg (depth + 1) A B i j)
          (higham23BiniStepMajorant K N e g gt * a * b) := by
        convert hmonoRaw using 1 <;>
          dsimp [higham23BiniExactLevel, higham23BiniFlEvaluate, X, Y, Xhat, Yhat,
            P, higham23BiniStepMajorant, K, N, e, g, gt, PE, PN] <;> ring
      have hCorrectEntry := congrArg
        (fun M : Higham23BiniMatrix h (depth + 1) ↦ M i j) hCorrect
      change higham23BiniExactLevel alg A B i j =
        higham23BiniMul h (depth + 1) A B i j at hCorrectEntry
      rw [← hCorrectEntry]
      simpa [higham23BiniExactMajorant, K, N, e, g, gt] using hmono

/-! ### First-order coefficient and the genuine quadratic remainder -/

/-- The exact majorant with unit roundoff exposed as a variable. -/
noncomputable def higham23BiniMajorantFamily
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℕ → ℝ → ℝ
  | 0, u => u
  | depth + 1, u =>
      higham23BiniStepMajorant (higham23MillerWeightTotal alg)
        (((h ^ depth : ℕ) : ℝ)) (higham23BiniMajorantFamily alg depth u)
        (higham23MillerGammaFamily (h * h) u)
        (higham23MillerGammaFamily t u)

/-- The derivative at zero of the exact Bini--Lotti majorant. -/
noncomputable def higham23BiniFirstOrderCoefficient
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℕ → ℝ
  | 0 => 1
  | depth + 1 =>
      higham23MillerWeightTotal alg *
        (higham23BiniFirstOrderCoefficient alg depth +
          (((h ^ depth : ℕ) : ℝ)) *
            (2 * (((h * h : ℕ) : ℝ)) + (t : ℝ)))

noncomputable def higham23BiniMajorantRemainder
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) (depth : ℕ) (u : ℝ) : ℝ :=
  higham23BiniMajorantFamily alg depth u -
    higham23BiniFirstOrderCoefficient alg depth * u

theorem higham23_biniExactMajorant_eq_family
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t) :
    ∀ depth, higham23BiniExactMajorant fp alg depth =
      higham23BiniMajorantFamily alg depth fp.u
  | 0 => rfl
  | depth + 1 => by
      rw [higham23BiniExactMajorant, higham23BiniMajorantFamily,
        higham23_biniExactMajorant_eq_family fp alg hLinear hOutput depth,
        higham23_gamma_split fp (h * h) hLinear,
        higham23_gamma_split fp t hOutput]
      rfl

/-- A polynomial one-step lemma: after the displayed linear term is removed,
the Bini--Lotti step is quadratic whenever each incoming remainder is. -/
theorem higham23_biniStepRemainder_isBigO_u_sq
    (K N s τ c : ℝ) (e g gt : ℝ → ℝ)
    (he : e =O[𝓝 0] (fun u : ℝ ↦ u))
    (hg : g =O[𝓝 0] (fun u : ℝ ↦ u))
    (hgt : gt =O[𝓝 0] (fun u : ℝ ↦ u))
    (heR : (fun u : ℝ ↦ e u - c * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2))
    (hgR : (fun u : ℝ ↦ g u - s * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2))
    (hgtR : (fun u : ℝ ↦ gt u - τ * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2)) :
    (fun u : ℝ ↦ higham23BiniStepMajorant K N (e u) (g u) (gt u) -
      K * (c + N * (2 * s + τ)) * u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_id.isBigO_one ℝ
  have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [pow_two, mul_one] using hu.mul huOne
  have hgSq : (fun u : ℝ ↦ g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hg.mul hg
  have heg : (fun u : ℝ ↦ e u * g u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using he.mul hg
  have hegSq : (fun u : ℝ ↦ e u * g u ^ 2)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have heOne := he.trans huOne
    simpa only [one_mul] using heOne.mul hgSq
  have hPE :=
    (((hgR.const_mul_left (2 * N)).add heR).add
      (hgSq.const_mul_left N)).add
      ((heg.const_mul_left 2).add hegSq)
  have hPE : (fun u : ℝ ↦
      (2 * N) * (g u - s * u) + (e u - c * u) + N * g u ^ 2 +
        2 * (e u * g u) + e u * g u ^ 2)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [add_assoc] using hPE
  have hBracket : (fun u : ℝ ↦
      e u + 2 * N * g u + 2 * e u * g u + N * g u ^ 2 +
        e u * g u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hlin := he.add (hg.const_mul_left (2 * N))
    have hquad := ((heg.const_mul_left 2).add
      (hgSq.const_mul_left N)).add hegSq
    have hsum := hlin.add (hquad.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by ring
    · exact Filter.EventuallyEq.rfl
  have hOutputNonlinear : (fun u : ℝ ↦ gt u *
      (e u + 2 * N * g u + 2 * e u * g u + N * g u ^ 2 +
        e u * g u ^ 2)) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hgt.mul hBracket
  have hOutput := (hgtR.const_mul_left N).add hOutputNonlinear
  have hTotal := (hPE.add hOutput).const_mul_left K
  apply hTotal.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      unfold higham23BiniStepMajorant higham23BiniProductErrorCore
        higham23BiniProductNormCore
      ring
  · exact Filter.EventuallyEq.rfl

theorem higham23_biniMajorantRemainder_isBigO_u_sq
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth, (fun u : ℝ ↦ higham23BiniMajorantRemainder alg depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2)
  | 0 => by
      simp only [higham23BiniMajorantRemainder, higham23BiniMajorantFamily,
        higham23BiniFirstOrderCoefficient, one_mul, sub_self]
      exact Asymptotics.isBigO_zero _ _
  | depth + 1 => by
      let K := higham23MillerWeightTotal alg
      let N : ℝ := (((h ^ depth : ℕ) : ℝ))
      let s : ℝ := (((h * h : ℕ) : ℝ))
      let τ : ℝ := (t : ℝ)
      let c := higham23BiniFirstOrderCoefficient alg depth
      let e : ℝ → ℝ := higham23BiniMajorantFamily alg depth
      let g : ℝ → ℝ := higham23MillerGammaFamily (h * h)
      let gt : ℝ → ℝ := higham23MillerGammaFamily t
      have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        Asymptotics.isBigO_refl _ _
      have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
        continuousAt_id.isBigO_one ℝ
      have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
        simpa only [pow_two, mul_one] using hu.mul huOne
      have heR : (fun u : ℝ ↦ e u - c * u)
          =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
        simpa [e, c, higham23BiniMajorantRemainder] using
          higham23_biniMajorantRemainder_isBigO_u_sq alg depth
      have he : e =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hlin := hu.const_mul_left c
        have hsum := hlin.add (heR.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by
            dsimp [e, c, higham23BiniMajorantRemainder]
            ring
        · exact Filter.EventuallyEq.rfl
      have hgR : (fun u : ℝ ↦ g u - s * u)
          =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
        simpa [g, s, higham23MillerGammaFamily] using
          higham23_gammaRemainder_isBigO_u_sq (h * h)
      have hgtR : (fun u : ℝ ↦ gt u - τ * u)
          =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
        simpa [gt, τ, higham23MillerGammaFamily] using
          higham23_gammaRemainder_isBigO_u_sq t
      have hg : g =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hlin := hu.const_mul_left s
        have hsum := hlin.add (hgR.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by ring
        · exact Filter.EventuallyEq.rfl
      have hgt : gt =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hlin := hu.const_mul_left τ
        have hsum := hlin.add (hgtR.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by ring
        · exact Filter.EventuallyEq.rfl
      have hStep := higham23_biniStepRemainder_isBigO_u_sq
        K N s τ c e g gt he hg hgt heR hgR hgtR
      simpa [higham23BiniMajorantRemainder, higham23BiniMajorantFamily,
        higham23BiniFirstOrderCoefficient, K, N, s, τ, c, e, g, gt]
        using hStep

/-- Theorem 23.4 for the literal recursive evaluator, split into its explicit
first-order recurrence coefficient and a genuine `O(u²)` remainder. -/
theorem higham23_theorem23_4_biniLotti_firstOrder
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsNoncommutativeCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (depth : ℕ) (A B : Higham23BiniMatrix h depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23BiniNormLe h depth A a)
    (hB : Higham23BiniNormLe h depth B b) :
    Higham23BiniErrorLe h depth (higham23BiniMul h depth A B)
      (higham23BiniFlEvaluate fp alg depth A B)
      ((higham23BiniFirstOrderCoefficient alg depth * fp.u +
        higham23BiniMajorantRemainder alg depth fp.u) * a * b) := by
  have hExact := higham23_theorem23_4_biniLotti_exactMajorant
    fp alg halg hLinear hOutput depth A B a b ha hb hA hB
  rw [higham23_biniExactMajorant_eq_family fp alg hLinear hOutput depth] at hExact
  have hsplit : higham23BiniMajorantFamily alg depth fp.u =
      higham23BiniFirstOrderCoefficient alg depth * fp.u +
        higham23BiniMajorantRemainder alg depth fp.u := by
    unfold higham23BiniMajorantRemainder
    ring
  rwa [hsplit] at hExact

/-- An explicit algorithm-dependent `α` for (23.19). -/
noncomputable def higham23BiniLottiAlpha
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℝ :=
  1 + higham23MillerWeightTotal alg *
    (2 * (((h * h : ℕ) : ℝ)) + (t : ℝ))

/-- An explicit algorithm-dependent `β` for (23.19). -/
noncomputable def higham23BiniLottiBeta
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℝ :=
  1 + higham23MillerWeightTotal alg + (h : ℝ)

theorem higham23_biniWeightTotal_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    0 ≤ higham23MillerWeightTotal alg := by
  unfold higham23MillerWeightTotal
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    higham23_miller_weight_nonneg alg i j

theorem higham23_biniFirstOrderCoefficient_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth, 0 ≤ higham23BiniFirstOrderCoefficient alg depth
  | 0 => by simp [higham23BiniFirstOrderCoefficient]
  | depth + 1 => by
      rw [higham23BiniFirstOrderCoefficient]
      have hK := higham23_biniWeightTotal_nonneg alg
      have hc := higham23_biniFirstOrderCoefficient_nonneg alg depth
      positivity

theorem higham23_biniLottiAlpha_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    0 ≤ higham23BiniLottiAlpha alg := by
  unfold higham23BiniLottiAlpha
  have hK := higham23_biniWeightTotal_nonneg alg
  positivity

theorem higham23_biniLottiBeta_nonneg
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    0 ≤ higham23BiniLottiBeta alg := by
  unfold higham23BiniLottiBeta
  have hK := higham23_biniWeightTotal_nonneg alg
  positivity

/-- The recurrence coefficient is bounded by the source shape
`α β^depth depth = α n^(log_h β) log_h n` at every positive depth. -/
theorem higham23_biniFirstOrderCoefficient_le_source
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth,
      higham23BiniFirstOrderCoefficient alg (depth + 1) ≤
        higham23BiniLottiCoefficient (higham23BiniLottiAlpha alg)
          (higham23BiniLottiBeta alg) h (depth + 1)
  | 0 => by
      let K := higham23MillerWeightTotal alg
      let S : ℝ := 2 * (((h * h : ℕ) : ℝ)) + (t : ℝ)
      let q := K * S
      let α := higham23BiniLottiAlpha alg
      let β := higham23BiniLottiBeta alg
      have hK : 0 ≤ K := by simpa [K] using higham23_biniWeightTotal_nonneg alg
      have hS : 0 ≤ S := by dsimp [S]; positivity
      have hq : 0 ≤ q := mul_nonneg hK hS
      have hcast : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
      have hid : α * β = (K + q) +
          (1 + (h : ℝ) + q * K + q * (h : ℝ)) := by
        dsimp [α, β, q, K, S, higham23BiniLottiAlpha,
          higham23BiniLottiBeta]
        ring
      have hbase : K * (1 + S) ≤ α * β := by
        calc
          _ = K + q := by dsimp [q]; ring
          _ ≤ _ := by
            rw [hid]
            have hp : 0 ≤ 1 + (h : ℝ) + q * K + q * (h : ℝ) := by positivity
            linarith
      simpa [higham23BiniFirstOrderCoefficient, higham23BiniLottiCoefficient,
        K, S, α, β, Nat.cast_pow, Nat.cast_mul] using hbase
  | depth + 1 => by
      let K := higham23MillerWeightTotal alg
      let S : ℝ := 2 * (((h * h : ℕ) : ℝ)) + (t : ℝ)
      let q := K * S
      let α := higham23BiniLottiAlpha alg
      let β := higham23BiniLottiBeta alg
      have hK : 0 ≤ K := by simpa [K] using higham23_biniWeightTotal_nonneg alg
      have hS : 0 ≤ S := by dsimp [S]; positivity
      have hq : 0 ≤ q := mul_nonneg hK hS
      have hα : 0 ≤ α := by simpa [α] using higham23_biniLottiAlpha_nonneg alg
      have hβ : 0 ≤ β := by simpa [β] using higham23_biniLottiBeta_nonneg alg
      have hKβ : K ≤ β := by
        dsimp [K, β, higham23BiniLottiBeta]
        have hK0 := higham23_biniWeightTotal_nonneg alg
        have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
        linarith
      have hhβ : (h : ℝ) ≤ β := by
        dsimp [β, higham23BiniLottiBeta]
        have hK0 := higham23_biniWeightTotal_nonneg alg
        linarith
      have hqαβ : q ≤ α * β := by
        have hβone : 1 ≤ β := by
          dsimp [β, higham23BiniLottiBeta]
          have hK0 := higham23_biniWeightTotal_nonneg alg
          have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
          linarith
        have hqα : q ≤ α := by
          dsimp [q, α, K, S, higham23BiniLottiAlpha]
          linarith
        exact hqα.trans (by
          have := mul_le_mul_of_nonneg_left hβone hα
          simpa using this)
      have ih := higham23_biniFirstOrderCoefficient_le_source alg depth
      have ih' : higham23BiniFirstOrderCoefficient alg (depth + 1) ≤
          α * β ^ (depth + 1) * ((depth + 1 : ℕ) : ℝ) := by
        simpa [higham23BiniLottiCoefficient, α, β] using ih
      have hPow : ((h : ℝ) ^ (depth + 1)) ≤ β ^ (depth + 1) := by
        gcongr
      have hKterm : K * higham23BiniFirstOrderCoefficient alg (depth + 1) ≤
          α * β ^ (depth + 2) * ((depth + 1 : ℕ) : ℝ) := by
        calc
          _ ≤ K * (α * β ^ (depth + 1) * ((depth + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left ih' hK
          _ ≤ β * (α * β ^ (depth + 1) * ((depth + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hKβ (by positivity)
          _ = _ := by rw [pow_succ]; ring
      have hqterm : q * (h : ℝ) ^ (depth + 1) ≤
          α * β ^ (depth + 2) := by
        calc
          _ ≤ q * β ^ (depth + 1) := mul_le_mul_of_nonneg_left hPow hq
          _ ≤ (α * β) * β ^ (depth + 1) :=
            mul_le_mul_of_nonneg_right hqαβ (by positivity)
          _ = _ := by rw [pow_succ]; ring
      have hfinal : K * (higham23BiniFirstOrderCoefficient alg (depth + 1) +
          ((h : ℝ) ^ (depth + 1)) * S) ≤
          α * β ^ (depth + 2) * ((depth + 2 : ℕ) : ℝ) := by
        calc
          _ = K * higham23BiniFirstOrderCoefficient alg (depth + 1) +
              q * (h : ℝ) ^ (depth + 1) := by dsimp [q]; ring
          _ ≤ α * β ^ (depth + 2) * ((depth + 1 : ℕ) : ℝ) +
              α * β ^ (depth + 2) := add_le_add hKterm hqterm
          _ = _ := by push_cast; ring
      simpa [higham23BiniFirstOrderCoefficient, higham23BiniLottiCoefficient,
        K, S, α, β, Nat.cast_pow, Nat.cast_mul, Nat.add_assoc] using hfinal

/-- Equation (23.19) with explicit algorithm-dependent `α` and `β`, for the
literal recursive bilinear evaluator. -/
theorem higham23_theorem23_4_biniLotti_eq23_19
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (halg : alg.IsNoncommutativeCorrect)
    (hLinear : gammaValid fp (h * h)) (hOutput : gammaValid fp t)
    (depth : ℕ) (A B : Higham23BiniMatrix h (depth + 1)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23BiniNormLe h (depth + 1) A a)
    (hB : Higham23BiniNormLe h (depth + 1) B b) :
    Higham23BiniErrorLe h (depth + 1)
      (higham23BiniMul h (depth + 1) A B)
      (higham23BiniFlEvaluate fp alg (depth + 1) A B)
      ((higham23BiniLottiCoefficient (higham23BiniLottiAlpha alg)
          (higham23BiniLottiBeta alg) h (depth + 1) * fp.u +
        higham23BiniMajorantRemainder alg (depth + 1) fp.u) * a * b) := by
  have hFirst := higham23_theorem23_4_biniLotti_firstOrder fp alg halg
    hLinear hOutput (depth + 1) A B a b ha hb hA hB
  apply higham23_biniError_mono h (depth + 1) _ _ hFirst
  have hCoeff := higham23_biniFirstOrderCoefficient_le_source alg depth
  have hScale := mul_le_mul_of_nonneg_right hCoeff fp.u_nonneg
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  calc
    _ = (higham23BiniFirstOrderCoefficient alg (depth + 1) * fp.u +
        higham23BiniMajorantRemainder alg (depth + 1) fp.u) * (a * b) := by ring
    _ ≤ (higham23BiniLottiCoefficient (higham23BiniLottiAlpha alg)
          (higham23BiniLottiBeta alg) h (depth + 1) * fp.u +
        higham23BiniMajorantRemainder alg (depth + 1) fp.u) * (a * b) :=
      mul_le_mul_of_nonneg_right (add_le_add hScale le_rfl) hab
    _ = _ := by ring

theorem higham23_biniLotti_scaledRemainder_isBigO_u_sq
    {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) (depth : ℕ) (a b : ℝ) :
    (fun u : ℝ ↦ higham23BiniMajorantRemainder alg depth u * a * b)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have hR := (higham23_biniMajorantRemainder_isBigO_u_sq alg depth).const_mul_left
    (a * b)
  apply hR.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by ring
  · exact Filter.EventuallyEq.rfl

end NumStability
