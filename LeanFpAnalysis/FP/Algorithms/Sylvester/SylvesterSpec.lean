-- Algorithms/Sylvester/SylvesterSpec.lean
--
-- Definitions and basic properties for the Sylvester equation AX - XB = C
-- (Higham §15). Core definitions: sylvesterResidual, SepLowerBound,
-- IsSymmetric, lyapunovOp, and the residual bound (eq 15.12).

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- The Sylvester equation: AX - XB = C (§15, eq 15.1)
-- ============================================================

/-- **Sylvester operator**: T(X) = AX - XB.
    The Sylvester equation AX - XB = C is T(X) = C. -/
noncomputable def sylvesterOp (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n A X i j - matMul n X B i j

/-- **Sylvester residual**: R = C - (AŶ - ŶB) for approximate solution Ŷ.
    A small residual is necessary for a small backward error (§15.2). -/
noncomputable def sylvesterResidual (n : ℕ) (A B C Y_hat : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => C i j - sylvesterOp n A B Y_hat i j

/-- Residual expanded: R_ij = C_ij - (AŶ)_ij + (ŶB)_ij. -/
theorem sylvesterResidual_eq (n : ℕ) (A B C Y_hat : Fin n → Fin n → ℝ) :
    sylvesterResidual n A B C Y_hat =
    fun i j => C i j - matMul n A Y_hat i j + matMul n Y_hat B i j := by
  ext i j; unfold sylvesterResidual sylvesterOp; ring

-- ============================================================
-- Separation function (§15.3, eq 15.26)
-- ============================================================

/-- **sep(A,B)** as a lower bound hypothesis: sep(A,B) ≥ σ > 0.
    sep(A,B) = min_{X≠0} ‖AX-XB‖_F/‖X‖_F is the separation of A and B.
    We work with a lower bound σ rather than computing the exact value,
    following the library convention for operator norms. -/
def SepLowerBound (n : ℕ) (A B : Fin n → Fin n → ℝ) (σ : ℝ) : Prop :=
  0 < σ ∧ ∀ X : Fin n → Fin n → ℝ, frobNormSq X ≠ 0 →
    σ ^ 2 * frobNormSq X ≤ frobNormSq (sylvesterOp n A B X)

/-- If sep(A,B) ≥ σ > 0, then AX - XB = C has a unique solution for any C. -/
theorem sep_implies_unique_solution (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (σ : ℝ) (hsep : SepLowerBound n A B σ)
    (C : Fin n → Fin n → ℝ)
    (X₁ X₂ : Fin n → Fin n → ℝ)
    (hX₁ : ∀ i j, sylvesterOp n A B X₁ i j = C i j)
    (hX₂ : ∀ i j, sylvesterOp n A B X₂ i j = C i j) :
    ∀ i j, X₁ i j = X₂ i j := by
  -- If X₁ ≠ X₂, then D = X₁ - X₂ ≠ 0 and sylvesterOp(D) = 0,
  -- contradicting sep > 0.
  by_contra h
  push_neg at h
  obtain ⟨i₀, j₀, hne⟩ := h
  -- D = X₁ - X₂
  let D : Fin n → Fin n → ℝ := fun i j => X₁ i j - X₂ i j
  -- D ≠ 0
  have hD_ne : frobNormSq D ≠ 0 := by
    intro h_eq
    have hzero := (frobNorm_eq_zero_iff D).mp (by
      unfold frobNorm; rw [Real.sqrt_eq_zero (frobNormSq_nonneg D)]; exact h_eq)
    exact hne (sub_eq_zero.mp (hzero i₀ j₀))
  -- sylvesterOp(D) = 0
  have hD_zero : ∀ i j, sylvesterOp n A B D i j = 0 := by
    intro i j
    have h1 := hX₁ i j; have h2 := hX₂ i j
    unfold sylvesterOp at h1 h2 ⊢; unfold matMul at h1 h2 ⊢
    simp only [D]
    have : ∀ k : Fin n, A i k * (X₁ k j - X₂ k j) =
        A i k * X₁ k j - A i k * X₂ k j := fun k => mul_sub _ _ _
    have : ∀ k : Fin n, (X₁ i k - X₂ i k) * B k j =
        X₁ i k * B k j - X₂ i k * B k j := fun k => sub_mul _ _ _
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]; linarith
  -- frobNormSq(sylvesterOp(D)) = 0
  have hFrob_zero : frobNormSq (sylvesterOp n A B D) = 0 := by
    unfold frobNormSq
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    rw [hD_zero i j]; ring
  -- sep > 0 gives σ² ‖D‖² ≤ ‖T(D)‖² = 0, contradicting ‖D‖² > 0
  have hpos : 0 < frobNormSq D :=
    lt_of_le_of_ne (frobNormSq_nonneg D) (Ne.symm hD_ne)
  have hle := hsep.2 D hD_ne
  rw [hFrob_zero] at hle
  -- hle : σ ^ 2 * frobNormSq D ≤ 0, but σ² > 0 and ‖D‖² > 0
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hsep.1
  nlinarith

-- ============================================================
-- Symmetric matrices and Lyapunov equation (§15.2.1)
-- ============================================================

/-- **Symmetric matrix**: A = Aᵀ. -/
def IsSymmetric (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, A i j = A j i

/-- **Lyapunov operator**: L(X) = AX + XAᵀ.
    The Lyapunov equation AX + XAᵀ = C is the special case B = -Aᵀ
    of the Sylvester equation. -/
noncomputable def lyapunovOp (n : ℕ) (A : Fin n → Fin n → ℝ)
    (X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n A X i j + matMul n X (matTranspose A) i j

/-- Lyapunov operator is Sylvester operator with B = -Aᵀ:
    L(X) = AX + XAᵀ = AX - X(-Aᵀ). -/
theorem lyapunovOp_eq_sylvesterOp (n : ℕ) (A X : Fin n → Fin n → ℝ) :
    lyapunovOp n A X =
    sylvesterOp n A (fun i j => -matTranspose A i j) X := by
  ext i j; unfold lyapunovOp sylvesterOp matMul matTranspose
  simp [mul_neg, Finset.sum_neg_distrib]

-- ============================================================
-- Normwise backward error definition (§15.2, eq 15.10)
-- ============================================================

/-- **Normwise backward error** (eq 15.10) as a lower bound predicate.
    η(Y) is the smallest ε such that (A+ΔA)Y - Y(B+ΔB) = C+ΔC
    with ‖ΔA‖_F ≤ εα, ‖ΔB‖_F ≤ εβ, ‖ΔC‖_F ≤ εγ.

    We represent this as: η is a backward error for Y if there exist
    perturbations ΔA, ΔB, ΔC satisfying the backward error equation
    and bounds. -/
def IsBackwardError (n : ℕ) (A B C Y : Fin n → Fin n → ℝ)
    (α β γ η : ℝ) : Prop :=
  ∃ (ΔA ΔB ΔC : Fin n → Fin n → ℝ),
    (∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j) ∧
    frobNormSq ΔA ≤ (η * α) ^ 2 ∧
    frobNormSq ΔB ≤ (η * β) ^ 2 ∧
    frobNormSq ΔC ≤ (η * γ) ^ 2

-- ============================================================
-- Residual bound (§15.2, eq 15.12)
-- ============================================================

/-- **Residual decomposition** (Higham §15.2, eq 15.11).

    From (A+ΔA)Y - Y(B+ΔB) = C + ΔC, the residual R = C - (AY - YB)
    decomposes as R = ΔAY - YΔB - ΔC. -/
theorem residual_decomposition (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ)
    (hEq : ∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j) :
    ∀ i j, sylvesterResidual n A B C Y i j =
      matMul n ΔA Y i j - matMul n Y ΔB i j - ΔC i j := by
  intro i j
  have h := hEq i j
  unfold sylvesterOp at h; unfold sylvesterResidual sylvesterOp
  unfold matMul at h ⊢
  simp only [add_mul, mul_add, Finset.sum_add_distrib] at h
  linarith

/-- **Residual bound** (Higham §15.2, eq 15.12).

    If ‖ΔA‖_F ≤ ηα, ‖ΔB‖_F ≤ ηβ, ‖ΔC‖_F ≤ ηγ, and
    R = ΔAY - YΔB - ΔC, then:
      ‖R‖_F ≤ ((α+β)‖Y‖_F + γ) · η.

    Proved via triangle inequality and submultiplicativity. -/
theorem residual_bound (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ)
    (α β γ η : ℝ) (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hγ : 0 ≤ γ) (_hη : 0 ≤ η)
    (hEq : ∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j)
    (hΔA : frobNorm ΔA ≤ η * α)
    (hΔB : frobNorm ΔB ≤ η * β)
    (hΔC : frobNorm ΔC ≤ η * γ) :
    frobNorm (sylvesterResidual n A B C Y) ≤
    ((α + β) * frobNorm Y + γ) * η := by
  -- R_ij = (ΔA·Y)_ij - (Y·ΔB)_ij - ΔC_ij
  have hR := residual_decomposition n A B C Y ΔA ΔB ΔC hEq
  -- ‖R‖_F = ‖ΔAY - YΔB - ΔC‖_F
  -- We bound this using the triangle inequality step by step.
  -- First, ‖R‖_F ≤ ‖ΔAY - YΔB‖_F + ‖ΔC‖_F  (since R = (ΔAY - YΔB) + (-ΔC))
  -- Then, ‖ΔAY - YΔB‖_F ≤ ‖ΔAY‖_F + ‖YΔB‖_F
  -- And ‖ΔAY‖_F ≤ ‖ΔA‖_F ‖Y‖_F, ‖YΔB‖_F ≤ ‖Y‖_F ‖ΔB‖_F
  -- Step 1: ‖ΔAY‖_F ≤ ‖ΔA‖_F ‖Y‖_F ≤ ηα ‖Y‖_F
  have h1 : frobNorm (matMul n ΔA Y) ≤ η * α * frobNorm Y :=
    le_trans (frobNorm_matMul_le ΔA Y)
      (mul_le_mul_of_nonneg_right hΔA (frobNorm_nonneg Y))
  -- Step 2: ‖YΔB‖_F ≤ ‖Y‖_F ‖ΔB‖_F ≤ ‖Y‖_F ηβ
  have h2 : frobNorm (matMul n Y ΔB) ≤ frobNorm Y * (η * β) :=
    le_trans (frobNorm_matMul_le Y ΔB)
      (mul_le_mul_of_nonneg_left hΔB (frobNorm_nonneg Y))
  -- Step 3: ‖R‖_F ≤ ‖ΔAY‖_F + ‖YΔB‖_F + ‖ΔC‖_F via triangle inequality
  -- First rewrite R pointwise using residual_decomposition
  have hReq : frobNorm (sylvesterResidual n A B C Y) =
      frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j - ΔC i j) := by
    congr 1; ext i j; exact hR i j
  rw [hReq]
  -- ‖ΔAY - YΔB - ΔC‖_F = ‖(ΔAY - YΔB) - ΔC‖_F ≤ ‖ΔAY - YΔB‖_F + ‖ΔC‖_F
  have h3 : frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j - ΔC i j) ≤
      frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j) + frobNorm ΔC := by
    have := frobNorm_sub_le (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j) ΔC
    convert this using 2
  -- ‖ΔAY - YΔB‖_F ≤ ‖ΔAY‖_F + ‖YΔB‖_F
  have h4 : frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j) ≤
      frobNorm (matMul n ΔA Y) + frobNorm (matMul n Y ΔB) :=
    frobNorm_sub_le (matMul n ΔA Y) (matMul n Y ΔB)
  -- Combine: ‖R‖_F ≤ ηα‖Y‖_F + ‖Y‖_F ηβ + ηγ = ((α+β)‖Y‖_F + γ)η
  have h5 : frobNorm (matMul n ΔA Y) + frobNorm (matMul n Y ΔB) + frobNorm ΔC ≤
      (η * α * frobNorm Y + frobNorm Y * (η * β)) + η * γ :=
    add_le_add (add_le_add h1 h2) hΔC
  have h6 : (η * α * frobNorm Y + frobNorm Y * (η * β)) + η * γ =
      ((α + β) * frobNorm Y + γ) * η := by ring
  linarith

end LeanFpAnalysis.FP
