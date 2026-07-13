-- Algorithms/CondEstimationTripleProduct.lean
--
-- Higham, 2nd ed., Problem 15.1 (Appendix A solution): rewrite and approximate
--   ‖ |A| |A⁻¹| |A| ‖∞
-- so that it can be estimated with the LAPACK norm estimator (Algorithm 15.4 /
-- 14.4), whose only primitive is the matrix–vector product (with a matrix and
-- its transpose).
--
-- Mathematical content (the honest REDUCTION, not a new numerical claim):
--
--   (R0)  ‖ |M| ‖∞ = ‖ M ‖∞      (repo `infNorm_absMatrix`: absolute values are
--         free inside an ∞-norm).
--
--   (R1)  For a nonnegative matrix  M ≥ 0,
--             ‖M‖∞ = ‖ M · 𝟙 ‖∞_vec ,        𝟙 = (1,…,1)ᵀ,
--         i.e. the max row sum is *realised* by the all-ones vector.  Hence any
--         product of nonnegative matrices has its ∞-norm computed by ONE
--         matrix–vector chain applied to 𝟙 — exactly the estimator's primitive.
--
--   (R2)  |A| |A⁻¹| |A|  is a product of nonnegative matrices, so
--             ‖ |A| |A⁻¹| |A| ‖∞ = ‖ |A| ( |A⁻¹| ( |A| 𝟙 ) ) ‖∞_vec ,
--         collapsing the componentwise triple product to a nested matvec chain
--         with the *nonnegative right-hand weight vector*  g = |A| 𝟙  (the row
--         sums of |A|).
--
--   (R3)  The only factor unavailable as a plain matvec is |A⁻¹| (the estimator
--         applies A⁻¹ and (A⁻¹)ᵀ by linear solves, but never forms |A⁻¹|).
--         Higham's fold (eq (14.1)/(15.1), repo `cond_norm_identity`) removes it:
--         for the nonnegative weight  g ≥ 0,
--             |A⁻¹| g  =  |A⁻¹ diag(g)| · 𝟙            (vectorwise),
--         because |A⁻¹_{ij}| g_j = |A⁻¹_{ij} g_j|.  So the middle factor is
--         evaluated by applying A⁻¹ to signed columns (i.e. columns of diag(g)),
--         no |A⁻¹| needed.  We also record the exact ∞-norm form of this fold via
--         `cond_norm_identity`.
--
-- Estimator honesty: Algorithm 14.4 returns a LOWER BOUND on the reduced norm
-- (repo `lapackNormEstimator_lower_bound`), never the exact value.  The final
-- corollary keeps that: the estimator output ≤ the exact rewritten quantity.
--
-- IMPORT-ONLY: no existing file is edited.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.CondEstimation

namespace LeanFpAnalysis.FP.Ch15

open scoped BigOperators
open LeanFpAnalysis.FP

/-- All-ones vector `𝟙 = (1,…,1)ᵀ`. -/
noncomputable def onesVec (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- **(R1) Row-sum collapse for a nonnegative matrix.**

    For `M ≥ 0` the ∞-norm (max row sum) is *attained by the all-ones vector*:
      ‖M‖∞ = ‖ M · 𝟙 ‖∞_vec .
    This is the fact that lets a nonnegative product be handled by the norm
    estimator, whose only primitive is the matrix–vector product. -/
theorem infNorm_nonneg_eq_infNormVec_matMulVec_ones {n : ℕ} (_hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    infNorm M = infNormVec (matMulVec n M (onesVec n)) := by
  have hrow : ∀ i : Fin n,
      matMulVec n M (onesVec n) i = ∑ j : Fin n, |M i j| := by
    intro i
    unfold matMulVec onesVec
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_one, abs_of_nonneg (hM i j)]
  have hrow_nonneg : ∀ i : Fin n, 0 ≤ matMulVec n M (onesVec n) i := by
    intro i
    rw [hrow i]
    exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      rw [← hrow i, ← abs_of_nonneg (hrow_nonneg i)]
      exact abs_le_infNormVec _ i
    · exact infNormVec_nonneg _
  · apply infNormVec_le_of_abs_le
    · intro i
      rw [abs_of_nonneg (hrow_nonneg i), hrow i]
      exact row_sum_le_infNorm M i
    · exact infNorm_nonneg M

/-- Entrywise nonnegativity of `|A|` (the componentwise absolute value). -/
lemma absMatrix_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i j, 0 ≤ absMatrix n A i j := fun _ _ => abs_nonneg _

/-- A product `matMul n A B` of two nonnegative matrices is nonnegative. -/
lemma matMul_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ matMul n A B i j := by
  intro i j
  unfold matMul
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))

/-- The componentwise triple product `|A| |A⁻¹| |A|`, as a genuine matrix. -/
noncomputable def tripleProduct (n : ℕ) (A A_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n (absMatrix n A) (matMul n (absMatrix n A_inv) (absMatrix n A))

/-- The triple product `|A| |A⁻¹| |A|` has nonnegative entries. -/
lemma tripleProduct_nonneg {n : ℕ} (A A_inv : Fin n → Fin n → ℝ) :
    ∀ i j, 0 ≤ tripleProduct n A A_inv i j := by
  unfold tripleProduct
  exact matMul_nonneg _ _ (absMatrix_nonneg A)
    (matMul_nonneg _ _ (absMatrix_nonneg A_inv) (absMatrix_nonneg A))

/-- The nonnegative right-hand weight `g = |A|·𝟙` = row sums of `|A|`. -/
noncomputable def rowSumWeights (n : ℕ) (A : Fin n → Fin n → ℝ) : Fin n → ℝ :=
  matMulVec n (absMatrix n A) (onesVec n)

/-- `g = |A|·𝟙` is nonnegative. -/
lemma rowSumWeights_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ j, 0 ≤ rowSumWeights n A j := by
  intro j
  unfold rowSumWeights matMulVec absMatrix onesVec
  exact Finset.sum_nonneg (fun k _ => by rw [mul_one]; exact abs_nonneg _)

/-- **(R2) Collapse of the componentwise triple product to a matvec chain.**

    Because `|A| |A⁻¹| |A| ≥ 0`, (R1) applies and the ∞-norm is the ∞-norm of
    the vector obtained by the *nested* matrix–vector chain
        |A| · ( |A⁻¹| · ( |A| · 𝟙 ) )
    applied to the all-ones vector.  This is exactly what a norm estimator that
    only knows how to form matrix–vector products can drive. -/
theorem tripleProduct_infNorm_eq_matvec_chain {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    infNorm (tripleProduct n A A_inv) =
      infNormVec
        (matMulVec n (absMatrix n A)
          (matMulVec n (absMatrix n A_inv) (rowSumWeights n A))) := by
  rw [infNorm_nonneg_eq_infNormVec_matMulVec_ones hn _
        (tripleProduct_nonneg A A_inv)]
  congr 1
  funext i
  unfold tripleProduct
  rw [matMulVec_matMul n (absMatrix n A)
        (matMul n (absMatrix n A_inv) (absMatrix n A)) (onesVec n) i]
  congr 1
  funext k
  rw [matMulVec_matMul n (absMatrix n A_inv) (absMatrix n A) (onesVec n) k]
  rfl

/-- **(R3) The Higham fold on the middle factor** (vector form).

    The estimator cannot form `|A⁻¹|`.  For the nonnegative weight `g` the middle
    vector `|A⁻¹| g` equals `|A⁻¹ diag(g)| · 𝟙`, so it is obtained by applying
    `A⁻¹` to the columns of `diag(g)` (linear solves) and taking row sums of
    absolute values — no `|A⁻¹|` is ever formed.  Here `A_inv_D i j = A⁻¹_{ij} g_j`
    is the honest matrix `A⁻¹ diag(g)`. -/
theorem middle_fold_vector {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (hg : ∀ j, 0 ≤ g j) :
    matMulVec n (absMatrix n A_inv) g =
      matMulVec n (absMatrix n (fun i j => A_inv i j * g j)) (onesVec n) := by
  funext i
  unfold matMulVec absMatrix onesVec
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_one, abs_mul, abs_of_nonneg (hg j)]

/-- **(R3′) The Higham fold on the middle factor** (∞-norm form; reuses
    `cond_norm_identity`, Higham eq (14.1)/(15.1)).

    The ∞-norm of the middle vector `|A⁻¹| g` equals that of the honest matrix
    `A⁻¹ diag(g)`; this is the exact identity the estimator relies on to avoid
    ever forming `|A⁻¹|`. -/
theorem middle_fold_infNorm {n : ℕ} (hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (g : Fin n → ℝ) (hg : ∀ j, 0 ≤ g j) :
    infNormVec (matMulVec n (absMatrix n A_inv) g) =
      infNorm (fun i j => A_inv i j * g j) := by
  have hchain : matMulVec n (absMatrix n A_inv) g
      = (fun i => ∑ j : Fin n, |A_inv i j| * g j) := by
    funext i; unfold matMulVec absMatrix; rfl
  rw [hchain]
  exact cond_norm_identity n hn A_inv g hg

/-- **Main exact rewriting (Problem 15.1).**

    The componentwise quantity `‖ |A| |A⁻¹| |A| ‖∞` equals the ∞-norm of the
    all-nonnegative product `|A| · |A⁻¹ diag(g)|` applied to `𝟙`, where
    `g = |A|·𝟙` collects the row sums of `|A|`:

        ‖ |A| |A⁻¹| |A| ‖∞
          = ‖ |A| ( |A⁻¹| ( |A| 𝟙 ) ) ‖∞_vec                     (R2)
          = ‖ |A| ( |A⁻¹ diag g| 𝟙 ) ‖∞_vec                       (R3 fold)
          = ‖ ( |A| · |A⁻¹ diag g| ) · 𝟙 ‖∞_vec .

    Every factor on the right is available to a norm estimator through matrix–
    vector products only: `|A|·v` for `v ≥ 0` is a genuine `|A|`-matvec, and the
    middle factor uses `A⁻¹` on the (signed) columns of `diag(g)` — never the
    forbidden `|A⁻¹|`. -/
theorem tripleProduct_rewrite {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    infNorm (tripleProduct n A A_inv) =
      infNormVec
        (matMulVec n (absMatrix n A)
          (matMulVec n
            (absMatrix n
              (fun i j => A_inv i j * rowSumWeights n A j))
            (onesVec n))) := by
  rw [tripleProduct_infNorm_eq_matvec_chain hn A A_inv]
  rw [middle_fold_vector A_inv (rowSumWeights n A) (rowSumWeights_nonneg A)]

/-- The reduced matrix whose (1-norm) the LAPACK estimator is fed with:
    `C = |A| · |A⁻¹ diag(g)|`, a genuine nonnegative matrix.  Its ∞-norm is the
    exact rewritten quantity. -/
noncomputable def reducedMatrix (n : ℕ) (A A_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n (absMatrix n A)
    (absMatrix n (fun i j => A_inv i j * rowSumWeights n A j))

/-- `‖ |A| |A⁻¹| |A| ‖∞ = ‖C‖∞` where `C = |A| · |A⁻¹ diag(g)|` is the reduced
    (nonnegative) matrix — the exact rewriting in genuine-matrix form. -/
theorem tripleProduct_infNorm_eq_reducedMatrix {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    infNorm (tripleProduct n A A_inv) = infNorm (reducedMatrix n A A_inv) := by
  rw [tripleProduct_rewrite hn A A_inv]
  -- C ≥ 0, so ‖C‖∞ = ‖C·𝟙‖∞_vec = ‖ |A|(|A⁻¹ diag g| 𝟙) ‖∞_vec.
  rw [infNorm_nonneg_eq_infNormVec_matMulVec_ones hn (reducedMatrix n A A_inv)
        (matMul_nonneg _ _ (absMatrix_nonneg A)
          (absMatrix_nonneg _))]
  congr 1
  funext i
  unfold reducedMatrix
  rw [matMulVec_matMul n (absMatrix n A)
        (absMatrix n (fun i j => A_inv i j * rowSumWeights n A j)) (onesVec n) i]

/-- **(R0/duality) `‖C‖∞ = ‖Cᵀ‖₁`**, so the *1-norm* LAPACK estimator (repo
    `lapackNormEstimator`, run on `Cᵀ`) lower-bounds the ∞-norm target. -/
theorem reducedMatrix_infNorm_eq_oneNorm_transpose {n : ℕ}
    (A A_inv : Fin n → Fin n → ℝ) :
    infNorm (reducedMatrix n A A_inv) =
      oneNorm (fun i j => reducedMatrix n A A_inv j i) := by
  rw [oneNorm_eq_infNorm_transpose]

/-- **Estimator soundness (honest lower bound, Problem 15.1).**

    Feeding the transpose of the reduced matrix `C = |A| · |A⁻¹ diag(g)|` to the
    LAPACK 1-norm estimator produces a value that never exceeds the exact
    rewritten quantity `‖ |A| |A⁻¹| |A| ‖∞`.  The estimator is a genuine
    lower-bound estimate — we do NOT claim equality. -/
theorem lapackEstimator_le_tripleProduct {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    lapackNormEstimator hn (fun i j => reducedMatrix n A A_inv j i) ≤
      infNorm (tripleProduct n A A_inv) := by
  have hle := lapackNormEstimator_lower_bound hn
    (fun i j => reducedMatrix n A A_inv j i)
  -- ‖(Cᵀ)‖₁ = ‖C‖∞ = target.
  have hCt : oneNorm (fun i j => reducedMatrix n A A_inv j i)
      = infNorm (reducedMatrix n A A_inv) := by
    rw [oneNorm_eq_infNorm_transpose]
  rw [hCt] at hle
  rw [tripleProduct_infNorm_eq_reducedMatrix hn A A_inv]
  exact hle

end LeanFpAnalysis.FP.Ch15
