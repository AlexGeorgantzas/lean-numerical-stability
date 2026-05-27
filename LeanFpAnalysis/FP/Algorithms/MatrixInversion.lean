-- Algorithms/MatrixInversion.lean
--
-- Higham Chapter 13: Matrix Inversion.
-- §13.1: Ideal perturbation bounds for computed inverses.
-- §13.2: Triangular matrix inversion (Methods 1, 2, block variants).
-- §13.3: Full matrix inversion via LU factorization (Methods A, B, C, D).
--
-- The internally proved results derive residual/forward-error consequences
-- from explicit componentwise contracts.  Some higher-level algorithmic
-- kernels are exposed as abstract interfaces when their detailed loop error
-- analysis is not formalized in this module.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.ForwardError
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.MatVec
import LeanFpAnalysis.FP.Algorithms.MatMul
import LeanFpAnalysis.FP.Algorithms.ForwardSub
import LeanFpAnalysis.FP.Algorithms.TriangularSolve
import LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination
import LeanFpAnalysis.FP.Algorithms.LU.LUSolve
import LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §13.1  Δ-notation: product error bounds
-- ============================================================

/-- **Matrix product error bound** (Δ-notation, Higham §13.1).

    If Ĉ = fl(A₁ · A₂) then |Ĉ − A₁A₂| ≤ ε · (|A₁| · |A₂|).
    This predicate captures the general statement for any computed product. -/
def MatProdError (n : ℕ) (C_hat : Fin n → Fin n → ℝ)
    (C_exact : Fin n → Fin n → ℝ) (ε : ℝ)
    (absProduct : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |C_hat i j - C_exact i j| ≤ ε * absProduct i j

-- ============================================================
-- §13.1  Ideal perturbation bounds (eqs. 13.1–13.3)
-- ============================================================

/-- **Right residual of a computed inverse** (Higham eq. 13.1).

    If Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|, then AY − I = −ΔA · Y,
    so |AY − I| ≤ ε|A||Y|.

    We state the bound with |Y| rather than |A⁻¹| to avoid circularity;
    the first-order version |A⁻¹| + O(ε) follows from eq. 13.3. -/
theorem ideal_right_residual (n : ℕ)
    (A Y : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |∑ k : Fin n, A i k * Y k j - if i = j then 1 else 0| ≤
      ε * ∑ k : Fin n, |A i k| * |Y k j| := by
  intro i j
  -- AY − I = (A+ΔA)Y − I − ΔAY = −ΔAY (since (A+ΔA)Y = I)
  -- So (AY − I)_{ij} = −∑_k ΔA_{ik} Y_{kj}
  have hAY : ∑ k : Fin n, A i k * Y k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔA i k * Y k j) := by
    have h := hY i j
    have hsplit : ∑ k : Fin n, A i k * Y k j + ∑ k : Fin n, ΔA i k * Y k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hAY, abs_neg]
  -- |∑_k ΔA_{ik} Y_{kj}| ≤ ∑_k |ΔA_{ik}| |Y_{kj}| ≤ ε ∑_k |A_{ik}| |Y_{kj}|
  calc |∑ k : Fin n, ΔA i k * Y k j|
      ≤ ∑ k : Fin n, |ΔA i k * Y k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔA i k| * |Y k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (ε * |A i k|) * |Y k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA i k) (abs_nonneg _)
    _ = ε * ∑ k : Fin n, |A i k| * |Y k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Left residual of a computed inverse** (Higham eq. 13.2).

    If Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|, then YA − I = −Y · ΔA,
    so |YA − I| ≤ ε|Y||A|. -/
theorem ideal_left_residual (n : ℕ)
    (A Y : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hY_left : ∀ i j, ∑ k : Fin n, Y i k * (A k j + ΔA k j) =
      if i = j then 1 else 0) :
    ∀ i j, |∑ k : Fin n, Y i k * A k j - if i = j then 1 else 0| ≤
      ε * ∑ k : Fin n, |Y i k| * |A k j| := by
  intro i j
  have hYA : ∑ k : Fin n, Y i k * A k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, Y i k * ΔA k j) := by
    have h := hY_left i j
    have hsplit : ∑ k : Fin n, Y i k * A k j + ∑ k : Fin n, Y i k * ΔA k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hYA, abs_neg]
  calc |∑ k : Fin n, Y i k * ΔA k j|
      ≤ ∑ k : Fin n, |Y i k * ΔA k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |Y i k| * |ΔA k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, |Y i k| * (ε * |A k j|) := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hΔA k j) (abs_nonneg _)
    _ = ε * ∑ k : Fin n, |Y i k| * |A k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Forward error for a computed inverse** (Higham eq. 13.3).

    If Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|, and A_inv is the true inverse, then
    A⁻¹ − Y = A⁻¹ · ΔA · Y, so
    |A⁻¹ − Y| ≤ ε|A⁻¹||A||Y|.

    This is the componentwise first-order bound. Replacing |Y| by |A⁻¹| + O(ε²)
    gives the pure |A⁻¹||A||A⁻¹| form. -/
theorem ideal_forward_error (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (_hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |A_inv i j - Y i j| ≤
      ε * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
  intro i j
  -- A⁻¹ − Y = A⁻¹(AY − I) since A⁻¹·A = I gives A⁻¹ − Y = A⁻¹·(AY − I).
  -- More precisely: A⁻¹ − Y = A⁻¹ · (I − AY) ... wait, we need:
  -- From (A+ΔA)Y = I, we get AY = I − ΔA·Y.
  -- So A⁻¹ − Y: note A⁻¹ = A⁻¹·I = A⁻¹·(A+ΔA)·Y + A⁻¹·ΔA·Y ... no.
  -- Correctly: A⁻¹ − Y = A⁻¹ − (A+ΔA)⁻¹.
  -- Since (A+ΔA)Y = I, we have Y = (A+ΔA)⁻¹.
  -- A⁻¹ − Y = A⁻¹(I − A·Y) = A⁻¹(ΔA·Y) since AY = I − ΔA·Y.
  -- Wait: AY = (A+ΔA)Y − ΔA·Y = I − ΔA·Y, so I − AY = ΔA·Y.
  -- Hence A⁻¹ − Y = A⁻¹·(I − AY) is wrong dimensionally.
  -- Actually: from A·Y + ΔA·Y = I, we get A·Y = I − ΔA·Y.
  -- Multiply on left by A⁻¹: Y = A⁻¹ − A⁻¹·ΔA·Y.
  -- So A⁻¹ − Y = A⁻¹·ΔA·Y.
  -- Therefore (A⁻¹ − Y)_{ij} = ∑_{k₁} A⁻¹_{ik₁} (∑_{k₂} ΔA_{k₁k₂} Y_{k₂j}).
  have hDiff : A_inv i j - Y i j =
      ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j) := by
    -- From (A+ΔA)Y = I, expanding: AY + ΔAY = I
    -- Multiply by A⁻¹ on left: Y + A⁻¹·ΔA·Y = A⁻¹
    -- So A⁻¹(i,j) = Y(i,j) + (A⁻¹ΔAY)(i,j)
    have hAY_col : ∀ k₁ : Fin n,
        ∑ k₂ : Fin n, A k₁ k₂ * Y k₂ j + ∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j =
        (if k₁ = j then (1 : ℝ) else 0) := by
      intro k₁
      have h := hY k₁ j
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    -- A⁻¹(i,j) = ∑_{k₁} A⁻¹(i,k₁) · δ(k₁,j) = ∑_{k₁} A⁻¹(i,k₁) · (∑_{k₂} A(k₁,k₂)Y(k₂,j) + ∑_{k₂} ΔA(k₁,k₂)Y(k₂,j))
    have hAinv_ij : A_inv i j = ∑ k₁ : Fin n, A_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    -- A⁻¹(i,j) = ∑_{k₁} A⁻¹(i,k₁) δ(k₁,j) from left inverse
    -- = Y(i,j) + (A⁻¹ΔAY)(i,j) by substituting δ = AY + ΔAY
    -- So A⁻¹(i,j) - Y(i,j) = (A⁻¹ΔAY)(i,j)
    -- Direct computation: A⁻¹·A·Y = Y (since A⁻¹A = I)
    have hAinvAY : ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * Y k₂ j) =
        Y i j := by
      -- (A⁻¹ · A · Y)(i,j) = (I · Y)(i,j) = Y(i,j)
      -- Unfold: ∑_{k₁} A⁻¹(i,k₁) · ∑_{k₂} A(k₁,k₂)Y(k₂,j)
      -- = ∑_{k₂} Y(k₂,j) · ∑_{k₁} A⁻¹(i,k₁)A(k₁,k₂) = ∑_{k₂} Y(k₂,j)·δ(i,k₂)
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      -- Goal: ∑ k₂, ∑ k₁, A_inv i k₁ * A k₁ k₂ * Y k₂ j = Y i j
      have : ∀ k₂ : Fin n,
          ∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂ * Y k₂ j =
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) * Y k₂ j := by
        intro k₂; rw [Finset.sum_mul]
      simp_rw [this]
      -- Use hInv: ∑ k, A_inv i k * A k k₂ = δ(i,k₂)
      have hIte : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) * Y k₂ j =
          (if i = k₂ then (1 : ℝ) else 0) * Y k₂ j := by
        intro k₂; congr 1; exact hInv i k₂
      simp_rw [hIte]
      simp [Finset.mem_univ]
    -- From (A+ΔA)Y = I: for each k₁, ∑_k₂ A(k₁,k₂)Y(k₂,j) = δ(k₁,j) - ∑_k₂ ΔA(k₁,k₂)Y(k₂,j)
    -- So ∑_{k₁} A⁻¹(i,k₁) · δ(k₁,j) = Y(i,j) + ∑_{k₁} A⁻¹(i,k₁) · ∑_{k₂} ΔA(k₁,k₂)·Y(k₂,j)
    rw [hAinv_ij]
    -- LHS = ∑ A⁻¹(i,k₁) · (AY + ΔAY)(k₁,j) - Y(i,j)
    -- We rewrite each δ(k₁,j) using hAY_col
    have hRewrite : ∑ k₁ : Fin n, A_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * Y k₂ j) +
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k₁ _
      rw [← mul_add, ← hAY_col k₁]
    rw [hRewrite, hAinvAY]
    ring
  rw [hDiff]
  -- |∑_{k₁} A⁻¹(i,k₁) (∑_{k₂} ΔA(k₁,k₂) Y(k₂,j))| ≤ ∑ |A⁻¹| |ΔA| |Y|
  calc |∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j)|
      ≤ ∑ k₁ : Fin n, |A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |A_inv i k₁| * |∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| * (∑ k₂ : Fin n, |ΔA k₁ k₂| * |Y k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j|
            ≤ ∑ k₂ : Fin n, |ΔA k₁ k₂ * Y k₂ j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k₂ : Fin n, |ΔA k₁ k₂| * |Y k₂ j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| * (∑ k₂ : Fin n, (ε * |A k₁ k₂|) * |Y k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k₂ _
        exact mul_le_mul_of_nonneg_right (hΔA k₁ k₂) (abs_nonneg _)
    _ = ε * ∑ k₁ : Fin n, |A_inv i k₁| * (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _
        have : ∑ k₂ : Fin n, ε * |A k₁ k₂| * |Y k₂ j| =
            ε * ∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k₂ _; ring
        rw [this]; ring

-- ============================================================
-- §13.1  Residual comparison: inversion vs GEPP
-- ============================================================

/-- **Residual bound for solving via matrix inversion** (Higham §13.1, p. 262).

    If X = A⁻¹ is formed exactly and the only rounding is in x̂ = fl(Xb),
    then the best possible residual bound is
      |b − Ax̂| ≤ γₙ|A||A⁻¹||b|.

    This is much worse than GEPP's |b − Ax̂| ≤ 2γₙ|L̂||Û||x̂|
    when A is ill-conditioned.

    We state the componentwise bound for each coordinate i. -/
theorem inversion_residual_bound (n : ℕ) (fp : FPModel)
    (A A_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hInv : IsRightInverse n A A_inv)
    (hn : gammaValid fp n) :
    let x_hat := fl_matVec fp n n A_inv b
    ∀ i, |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n *
        ∑ j : Fin n, |A i j| * (∑ k : Fin n, |A_inv j k| * |b k|) := by
  intro x_hat i
  -- x̂ = fl(A⁻¹b) satisfies backward error: x̂ = (A⁻¹ + ΔX)b with |ΔX| ≤ γₙ|A⁻¹|
  obtain ⟨ΔX, hΔX_bound, hΔX_eq⟩ := matVec_backward_error fp n n A_inv b hn
  -- b − Ax̂ = b − A(A⁻¹ + ΔX)b = b − (I + AΔX)b = −AΔXb
  -- since A · A⁻¹ = I by hInv
  change |b i - ∑ j : Fin n, A i j * fl_matVec fp n n A_inv b j| ≤ _
  have hRes : b i - ∑ j : Fin n, A i j * fl_matVec fp n n A_inv b j =
      -(∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)) := by
    -- x̂_j = ∑_k (A_inv j k + ΔX j k) * b k
    -- Ax̂ = A(A⁻¹+ΔX)b, so b − Ax̂ = b − A·A⁻¹·b − A·ΔX·b = −A·ΔX·b
    have hxhat : ∀ j : Fin n, fl_matVec fp n n A_inv b j =
        ∑ k : Fin n, (A_inv j k + ΔX j k) * b k := hΔX_eq
    -- Expand: ∑_j A_ij x̂_j = ∑_j A_ij ∑_k A_inv_jk b_k + ∑_j A_ij ∑_k ΔX_jk b_k
    have hExpand : ∑ j : Fin n, A i j * fl_matVec fp n n A_inv b j =
        ∑ j : Fin n, A i j * (∑ k : Fin n, A_inv j k * b k) +
        ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hxhat j, ← mul_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    -- First sum = (AA⁻¹b)_i = b_i
    have hFirst : ∑ j : Fin n, A i j * (∑ k : Fin n, A_inv j k * b k) = b i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have : ∀ k : Fin n,
          (∑ j : Fin n, A i j * A_inv j k) * b k =
          (if i = k then (1 : ℝ) else 0) * b k := by
        intro k; congr 1; exact hInv i k
      simp_rw [this]
      simp [Finset.mem_univ]
    rw [hExpand, hFirst]; ring
  rw [hRes, abs_neg]
  -- |∑_j A_ij (∑_k ΔX_jk b_k)| ≤ ∑_j |A_ij| ∑_k |ΔX_jk| |b_k| ≤ γₙ ∑ |A| |A⁻¹| |b|
  calc |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)|
      ≤ ∑ j : Fin n, |A i j * (∑ k : Fin n, ΔX j k * b k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |∑ k : Fin n, ΔX j k * b k| := by
        apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, |ΔX j k| * |b k|) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |∑ k : Fin n, ΔX j k * b k|
            ≤ ∑ k : Fin n, |ΔX j k * b k| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k : Fin n, |ΔX j k| * |b k| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, (gamma fp n * |A_inv j k|) * |b k|) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔX_bound j k) (abs_nonneg _)
    _ = gamma fp n * ∑ j : Fin n, |A i j| * (∑ k : Fin n, |A_inv j k| * |b k|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        have : ∑ k : Fin n, (gamma fp n * |A_inv j k|) * |b k| =
            gamma fp n * ∑ k : Fin n, |A_inv j k| * |b k| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
        rw [this]; ring

-- ============================================================
-- §13.2  Triangular matrix inversion
-- ============================================================

-- §13.2.1  Method 1 (column-by-column forward substitution)

/-- **Method 1 right residual for triangular inversion** (Higham eq. 13.4).

    Method 1 computes L⁻¹ by solving Lx̂ⱼ = eⱼ for each column j.
    From Theorem 8.5 (forwardSub_backward_error), each column satisfies
    (L + ΔLⱼ)x̂ⱼ = eⱼ with |ΔLⱼ| ≤ γ(n)|L|.

    This gives the componentwise right residual:
      |LX̂ − I| ≤ γ(n)|L||X̂|. -/
theorem triInv_method1_right_residual (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n) :
    -- X̂ is computed column-by-column: column j = forwardSub(L, eⱼ)
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    -- For each column j: ∃ ΔLⱼ with |ΔLⱼ| ≤ γ(n)|L| and (L+ΔLⱼ)x̂ⱼ = eⱼ
    ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k : Fin n, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i : Fin n, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0 := by
  intro X_hat j
  exact forwardSub_backward_error fp n L (fun k => if k = j then 1 else 0) hL_diag hLT hn

/-- **Method 1 right residual — matrix form** (Higham eq. 13.4).

    Consequence: |LX̂ − I| ≤ γ(n)|L||X̂| componentwise. -/
theorem triInv_method1_right_residual_matrix (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
  intro X_hat i j
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    triInv_method1_right_residual n fp L hL_diag hLT hn j
  have hLX : ∑ k : Fin n, L i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔL i k * X_hat k j) := by
    have h := hΔL_eq i
    have hsplit : ∑ k : Fin n, L i k * X_hat k j +
        ∑ k : Fin n, ΔL i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hLX, abs_neg]
  calc |∑ k : Fin n, ΔL i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔL i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔL i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
    _ = gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Method 1 forward error** (Higham eq. 13.5).

    |X̂ − L⁻¹| ≤ γ(n)|L⁻¹||L||X̂|  (componentwise).

    Proof: From LX̂ = I + E with |E| ≤ γₙ|L||X̂|, multiply by L⁻¹ on the left:
    X̂ = L⁻¹ + L⁻¹E, so |X̂ − L⁻¹| = |L⁻¹E| ≤ |L⁻¹||E| ≤ γₙ|L⁻¹||L||X̂|. -/
theorem triInv_method1_forward_error (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
  intro X_hat i j
  -- Get residual: |LX̂ − I|_{k₁j} ≤ γ(n) ∑_{k₂} |L_{k₁k₂}| |X̂_{k₂j}|
  have hRes := triInv_method1_right_residual_matrix n fp L hL_diag hLT hn
  -- Define E_{k₁j} = (LX̂)_{k₁j} − δ_{k₁j}
  -- From LX̂ = I + E, multiply by L⁻¹: X̂ = L⁻¹ + L⁻¹E
  -- So X̂_{ij} − L⁻¹_{ij} = (L⁻¹E)_{ij} = ∑_{k₁} L⁻¹_{ik₁} E_{k₁j}
  have hDiff : X_hat i j - L_inv i j =
      ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    -- RHS = ∑ k₁, L⁻¹(i,k₁) · (LX̂)(k₁,j) − ∑ k₁, L⁻¹(i,k₁) · δ(k₁,j)
    -- First part = (L⁻¹LX̂)(i,j) = X̂(i,j), second part = L⁻¹(i,j)
    have hRHS_expand : ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, L_inv i k₁ * (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, L_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    -- Second sum = L⁻¹(i,j)
    have hSecond : ∑ k₁ : Fin n, L_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = L_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    -- First sum = (L⁻¹ · L · X̂)(i,j) = X̂(i,j)
    have hFirst : ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvL : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvL]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |L_inv i k₁| *
        |∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |L_inv i k₁| *
        (gamma fp n * ∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- **Method 1 first-order forward error** (Higham eq. 13.6).

    |X̂ − L⁻¹| ≤ γ(n)|L⁻¹||L||L⁻¹| + O(u²).

    Since X̂ = L⁻¹ + O(u), replacing |X̂| by |L⁻¹| in eq. 13.5 gives
    this first-order bound. We state the "pre-replacement" form:
    for any X̂_bound satisfying |X̂| ≤ X̂_bound, we get the bound
    with X̂_bound in place of |X̂|. -/
theorem triInv_method1_forward_error_firstorder (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (X_bound : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n)
    (hBound : ∀ i j : Fin n,
      |fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i| ≤
        X_bound i j) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j) := by
  intro X_hat i j
  have hFwd := triInv_method1_forward_error n fp L L_inv hL_diag hLT hInv hn i j
  calc |X_hat i j - L_inv i j|
      ≤ gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := hFwd
    _ ≤ gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j) := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k₂ _
        exact mul_le_mul_of_nonneg_left (hBound k₂ j) (abs_nonneg _)

/-- **Method 1 normwise forward error** (Higham eq. 13.7).

    ‖X̂ − L⁻¹‖∞ ≤ γ(n) · ‖|L⁻¹||L||X̂|‖∞.

    When ‖X̂‖∞ ≈ ‖L⁻¹‖∞ (i.e. to first order), this gives
    relative error ≤ cₙu · cond(L⁻¹). -/
theorem triInv_method1_normwise_error (n : ℕ) (_hn0 : 0 < n) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hgv : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    infNorm (fun i j => X_hat i j - L_inv i j) ≤
      gamma fp n * infNorm (fun i j =>
        ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|)) := by
  intro X_hat
  have hFwd := triInv_method1_forward_error n fp L L_inv hL_diag hLT hInv hgv
  -- infNorm is max_i ∑_j |M i j|. We bound each row sum then take the max.
  let M := fun i j => ∑ k₁ : Fin n, |L_inv i k₁| *
    (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|)
  have hnn : ∀ i j : Fin n, 0 ≤ M i j := by
    intro i' j'; apply Finset.sum_nonneg; intro k₁ _
    exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg
      (fun k₂ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  -- Each entry: |X̂ij − L⁻¹ij| ≤ γ(n) · M i j
  have hEntry : ∀ i j : Fin n, |X_hat i j - L_inv i j| ≤ gamma fp n * M i j :=
    fun i j => hFwd i j
  -- Row sum bound: ∑_j |X̂ij − L⁻¹ij| ≤ γ(n) · ∑_j M i j
  have hRow : ∀ i : Fin n, ∑ j : Fin n, |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ j : Fin n, M i j := by
    intro i
    calc ∑ j : Fin n, |X_hat i j - L_inv i j|
        ≤ ∑ j : Fin n, gamma fp n * M i j :=
          Finset.sum_le_sum (fun j _ => hEntry i j)
      _ = gamma fp n * ∑ j : Fin n, M i j :=
          (Finset.mul_sum Finset.univ _ (gamma fp n)).symm
  -- ∑_j M i j = ∑_j |M i j| since M ≥ 0
  have habs_eq : ∀ i j : Fin n, |M i j| = M i j :=
    fun i j => abs_of_nonneg (hnn i j)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |(fun i j => X_hat i j - L_inv i j) i j|
        ≤ gamma fp n * ∑ j : Fin n, M i j := hRow i
      _ = gamma fp n * ∑ j : Fin n, |(fun i j => M i j) i j| := by
          congr 1; apply Finset.sum_congr rfl; intro j _; exact (habs_eq i j).symm
      _ ≤ gamma fp n * infNorm M := by
          apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hgv)
          exact row_sum_le_infNorm M i
  · exact mul_nonneg (gamma_nonneg fp hgv) (infNorm_nonneg M)

-- §13.2.1  Method 2 (reverse-order column computation via mat-vec multiply)

/-- **Specification for Method 2 triangular inversion**.

    Method 2 computes columns of X̂ ≈ L⁻¹ in reverse order j = n, n−1, …, 1.
    For each j:
      x̂ⱼⱼ = lⱼⱼ⁻¹(1 + δ),  |δ| ≤ u
      x̂(j+1:n, j) = x̂(j+1:n, j+1:n) · L(j+1:n, j)   (mat-vec multiply)
      x̂(j+1:n, j) = −x̂ⱼⱼ · x̂(j+1:n, j)              (scalar multiply)

    This is an abstract spec capturing the key error properties. -/
structure Method2Spec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- Diagonal entries: x̂ⱼⱼ = fl(1/lⱼⱼ), so x̂ⱼⱼlⱼⱼ = 1 + δ with |δ| ≤ u. -/
  diag_err : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
    X_hat j j * L j j = 1 + δ
  /-- Off-diagonal (below j): computed via mat-vec + scalar multiply with
      rounding errors bounded by Δ-notation. -/
  offdiag_err : ∀ j : Fin n, ∀ i : Fin n, i.val > j.val →
    ∃ Δ_mv : Fin n → ℝ,
      (∀ k : Fin n, |Δ_mv k| ≤ gamma fp n * |X_hat i k| * |L k j|) ∧
      X_hat i j = -X_hat j j * (∑ k : Fin n, X_hat i k * L k j) +
        Δ_mv j
  /-- Upper triangle is zero (since L is lower triangular, L⁻¹ is too). -/
  upper_zero : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0

/-- **Abstract Lemma 13.1 interface** (Higham eq. 13.8): Method 2 left residual.

    The computed inverse X̂ from Method 2 satisfies the left residual bound:
      |X̂L − I| ≤ c'ₙu · (|X̂| · |L|).

    Higham proves this by induction on n using the 2×2 block partition
    L = [[α, 0], [y, M]], X̂ = [[β̂, 0], [ẑ, N̂]].

    This theorem is an abstract interface: the hypothesis `hLeftRes` is the
    Method 2 local/inductive analysis, and the theorem records the named
    contract for reuse by later matrix-inversion results. -/
theorem triInv_method2_left_residual (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  hLeftRes

-- §13.2.2  Block methods

/-- **Specification for block triangular inversion (Method 1B)**.

    Method 1B computes X̂ ≈ L⁻¹ in block form: for j = 1:N,
    diagonal blocks Xⱼⱼ = Lⱼⱼ⁻¹ by Method 1, then off-diagonal
    blocks by block forward substitution.

    The block indexing details are intentionally abstracted away; the reusable
    numerical content is the per-column backward-error contract produced by the
    diagonal block inversions and block forward substitutions. -/
structure BlockMethod1BSpec (fp : FPModel) (n N : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- The declared number of blocks is compatible with the matrix dimension. -/
  block_count_le_dim : N ≤ n
  /-- The computed inverse has the expected lower-triangular shape. -/
  lower_triangular_inverse : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0
  /-- Each computed column satisfies the backward-error contract obtained from
      the Method 1 diagonal block solve and the block forward substitutions. -/
  column_backward_error : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
    (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
    ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
      if i = j then 1 else 0

/-- **Lemma 13.2** (Higham eq. 13.10): Method 1B right residual.

    |LX̂ − I| ≤ cₙu|L||X̂|.

    The block version achieves the same right residual bound as the
    unblocked Method 1. -/
theorem triInv_method1B_right_residual (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    -- Hypothesis: each column of X̂ satisfies the same per-column backward error
    -- as Method 1 (forwardSub_backward_error).
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
  intro i j
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ := hCol j
  have hLX : ∑ k : Fin n, L i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔL i k * X_hat k j) := by
    have h := hΔL_eq i
    have hsplit : ∑ k : Fin n, L i k * X_hat k j +
        ∑ k : Fin n, ΔL i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hLX, abs_neg]
  calc |∑ k : Fin n, ΔL i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔL i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔL i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
    _ = gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- Method 1B right residual obtained from the block-method specification. -/
theorem triInv_method1B_right_residual_from_spec (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hSpec : BlockMethod1BSpec fp n N L X_hat) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| :=
  triInv_method1B_right_residual n fp L X_hat hL_diag hLT hn
    hSpec.column_backward_error

/-- **Abstract Lemma 13.3 interface**: Method 2C left residual.

    |X̂L − I| ≤ cₙu|X̂||L|.

    Method 2C (LAPACK's xTRTRI) achieves the same left residual bound as
    the unblocked Method 2.

    This theorem is a named abstract interface: `hLeftRes` supplies the
    Method 2C block-loop residual analysis. -/
theorem triInv_method2C_left_residual (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    -- Hypothesis: X̂ satisfies Method 2C spec (solve with L_jj from right,
    -- then back substitution with L_jj from right).
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  hLeftRes

-- ============================================================
-- §13.3  Full matrix inversion via LU factorization
-- ============================================================

-- §13.3.1  Method A: solve Ax̂ⱼ = eⱼ for each column

/-- **Method A column-wise backward error** (Higham eq. 13.15).

    Method A computes X̂ ≈ A⁻¹ by solving Ax̂ⱼ = eⱼ for j = 1:n via LU.
    From Theorem 9.4, each column satisfies (A + ΔAⱼ)x̂ⱼ = eⱼ
    with |ΔAⱼ| ≤ (3γₙ + γₙ²)|L̂||Û|. -/
theorem methodA_column_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      let b_j : Fin n → ℝ := fun i => if i = j then 1 else 0
      let y_hat := fl_forwardSub fp n L_hat b_j
      let x_hat_j := fl_backSub fp n U_hat y_hat
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * x_hat_j k = b_j i := by
  intro j b_j y_hat x_hat_j
  exact lu_solve_backward_error fp n A L_hat U_hat b_j hL_diag hU_diag hLU hn

/-- **Method A right residual** (Higham eq. 13.16).

    |AX̂ − I| ≤ c'ₙu|L̂||Û||X̂|.

    Each column has (A + ΔAⱼ)x̂ⱼ = eⱼ, so Ax̂ⱼ = eⱼ − ΔAⱼx̂ⱼ,
    hence |Ax̂ⱼ − eⱼ| = |ΔAⱼx̂ⱼ| ≤ (3γₙ+γₙ²)(|L̂||Û|)|x̂ⱼ|. -/
theorem methodA_right_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_hat : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp n)
    -- Each column j has backward error: (A+ΔAⱼ)x̂ⱼ = eⱼ with |ΔAⱼ| ≤ c|L̂||Û|
    (hCol : ∀ j : Fin n, ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
      ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
          |X_hat k j| := by
  intro i j
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := hCol j
  have hAX : ∑ k : Fin n, A i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔA i k * X_hat k j) := by
    have h := hΔA_eq i
    have hsplit : ∑ k : Fin n, A i k * X_hat k j +
        ∑ k : Fin n, ΔA i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hAX, abs_neg]
  calc |∑ k : Fin n, ΔA i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔA i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔA i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, ((3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA_bound i k) (abs_nonneg _)
    _ = (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
            |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Method A forward error** (Higham eq. 13.17).

    |X̂ − A⁻¹| ≤ c'ₙu|A⁻¹||L̂||Û||X̂|. -/
theorem methodA_forward_error (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat X_hat : Fin n → Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (_hn : gammaValid fp n)
    -- Right residual hypothesis
    (hRes : ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
          |X_hat k j|) :
    ∀ i j : Fin n,
      |X_hat i j - A_inv i j| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
            |X_hat k₂ j|) := by
  intro i j
  -- Define E_{k₁j} = (AX̂)_{k₁j} − δ_{k₁j}, the residual
  -- From AX̂ = I + E, multiply by A⁻¹: X̂ = A⁻¹ + A⁻¹E
  -- So X̂_{ij} − A⁻¹_{ij} = (A⁻¹E)_{ij}
  let c := 3 * gamma fp n + gamma fp n ^ 2
  have hDiff : X_hat i j - A_inv i j =
      ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    have hRHS_expand : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, A_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    have hSecond : ∑ k₁ : Fin n, A_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = A_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hFirst : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvA : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvA]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |A_inv i k₁| *
        |∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| *
        (c * ∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

-- §13.3.2  Method B: compute U⁻¹ then solve XL̂ = X_U

/-- **Method B left residual** (Higham eq. 13.18).

    Method B: compute X_U ≈ U⁻¹ (by an analogue of Method 2 or 2C for upper
    triangular matrices), then solve for X in XL̂ = X_U by back substitution
    from the right.

    The left residual satisfies:
      |X̂A − I| ≤ c'ₙu|X̂||L̂||Û|.

    Note: eq. 13.18 is the left residual analogue of eq. 13.16.
    The LINPACK manual incorrectly states this as a right residual bound. -/
theorem methodB_left_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    -- X_U satisfies right residual for U⁻¹: |X_U · Û − I| ≤ γₙ|X_U||Û|
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    -- X̂ is computed by solving X̂L̂ = X_U from the right (back sub rows):
    -- |X̂L̂ − X_U| ≤ γₙ|X̂||L̂| (this is the Δ(X̂, L̂) term)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L_hat k j - X_U i j| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L_hat k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k₁ : Fin n, |X_hat i k₁| *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
  intro i j
  let γ := gamma fp n
  -- Step 1: Decompose A = L̂Û − (L̂Û − A)
  -- X̂A = X̂L̂Û − X̂(L̂Û − A)
  -- Step 2: X̂L̂Û − I = (X̂L̂ − X_U)Û + (X_UÛ − I) = E₁Û + E₂
  -- where E₁ = X̂L̂ − X_U, E₂ = X_UÛ − I
  -- Bound |X_U| ≤ (1+γ)|X̂||L̂| from E₁ bound
  -- Total: |X̂A − I| ≤ (3γ + γ²)|X̂||L̂||Û|
  -- Abbreviate the componentwise product bound
  let B := fun i j => ∑ k₁ : Fin n, |X_hat i k₁| *
    (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)
  -- The LU backward error gives |L̂Û − A| ≤ γ|L̂||Û|
  have hLUerr := hLU.backward_bound
  -- Bound: X̂(A − L̂Û) contribution
  have hLU_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k *
        (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)| ≤ γ * B i j := by
    intro i' j'
    calc |∑ k : Fin n, X_hat i' k *
          (A k j' - ∑ l : Fin n, L_hat k l * U_hat l j')|
        ≤ ∑ k : Fin n, |X_hat i' k| *
          |A k j' - ∑ l : Fin n, L_hat k l * U_hat l j'| := by
          calc _ ≤ ∑ k, |X_hat i' k * (A k j' - ∑ l, L_hat k l * U_hat l j')| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, |X_hat i' k| *
            (γ * ∑ l : Fin n, |L_hat k l| * |U_hat l j'|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have h := hLUerr k j'
          rwa [abs_sub_comm] at h
      _ = γ * B i' j' := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
  -- Bound: E₁Û contribution where E₁ = X̂L̂ − X_U
  have hE1U_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) *
        U_hat k j| ≤ γ * B i j := by
    intro i' j'
    calc |∑ k : Fin n, (∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k) *
          U_hat k j'|
        ≤ ∑ k : Fin n, |∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k| *
          |U_hat k j'| := by
          calc _ ≤ ∑ k, |(∑ l, X_hat i' l * L_hat l k - X_U i' k) * U_hat k j'| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (γ * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) *
          |U_hat k j'| := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hXL_res i' k) (abs_nonneg _)
      _ = γ * B i' j' := by
          have hfact : ∀ k : Fin n,
              (γ * ∑ l, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| =
              γ * ((∑ l, |X_hat i' l| * |L_hat l k|) * |U_hat k j'|) :=
            fun _ => by ring
          simp_rw [hfact, ← Finset.mul_sum, Finset.sum_mul]
          congr 1; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  -- Bound: E₂ contribution where E₂ = X_UÛ − I, with |X_U| ≤ (1+γ)|X̂||L̂|
  -- First bound |X_U|
  have hXU_bound : ∀ i' k : Fin n,
      |X_U i' k| ≤ (1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := by
    intro i' k
    have hXL_abs : |∑ l : Fin n, X_hat i' l * L_hat l k| ≤
        ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := by
      calc _ ≤ ∑ l, |X_hat i' l * L_hat l k| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by apply Finset.sum_congr rfl; intro l _; exact abs_mul _ _
    have hE1 : |∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k| ≤
        γ * ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := hXL_res i' k
    have key : |X_U i' k| ≤ |∑ l, X_hat i' l * L_hat l k| +
        |∑ l, X_hat i' l * L_hat l k - X_U i' k| := by
      have h := abs_add_le (X_U i' k - ∑ l, X_hat i' l * L_hat l k)
        (∑ l, X_hat i' l * L_hat l k)
      rw [sub_add_cancel] at h
      rw [abs_sub_comm] at h; linarith
    linarith
  -- Bound E₂ contribution: |E₂|_ij ≤ γ(1+γ)|X̂||L̂||Û|
  have hE2_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j -
        if i = j then (1 : ℝ) else 0| ≤
      γ * (1 + γ) * B i j := by
    intro i' j'
    calc |∑ k : Fin n, X_U i' k * U_hat k j' -
          if i' = j' then (1 : ℝ) else 0|
        ≤ γ * ∑ k : Fin n, |X_U i' k| * |U_hat k j'| := hXU_res i' j'
      _ ≤ γ * ∑ k : Fin n, ((1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) *
            |U_hat k j'| := by
          apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hXU_bound i' k) (abs_nonneg _)
      _ = γ * (1 + γ) * B i' j' := by
          rw [show γ * ∑ k : Fin n,
            ((1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| =
            γ * (1 + γ) * ∑ k : Fin n,
              (∑ l : Fin n, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| from by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring]
          congr 1
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  -- Fubini: ∑_k(∑_l X̂L̂)Û = ∑_k X̂(∑_l L̂Û)
  have hFub : ∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k) * U_hat k j =
      ∑ k : Fin n, X_hat i k * ∑ l : Fin n, L_hat k l * U_hat l j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _; ring
  -- Algebraic decomposition: target = E₂ + E₁Û + X̂(A−L̂Û)
  have hDecomp : ∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0) =
      (∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)) +
      (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
      (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib]
    linarith [hFub]
  rw [hDecomp]
  have h1 := hE2_contrib i j
  have h2 := hE1U_contrib i j
  have h3 := hLU_contrib i j
  calc |(∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)) +
        (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
        (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))|
      ≤ |∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)| +
        |(∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
         (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))| :=
      by rw [add_assoc]; exact abs_add_le _ _
    _ ≤ |∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)| +
        |∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j| +
        |∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)| := by
      have := abs_add_le (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j)
        (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))
      linarith
    _ ≤ γ * (1 + γ) * B i j + γ * B i j + γ * B i j := by linarith
    _ = (3 * γ + γ ^ 2) * B i j := by ring

-- §13.3.3  Method C: solve UXL = I

/-- **Abstract Method C mixed residual interface** (Higham eq. 13.19).

    Method C solves UX̂L = I, computing X̂ a partial row and column at a time.
    The "mixed" residual satisfies:
      |ÛX̂L̂ − I| ≤ cₙu|Û||X̂||L̂|.

    From this, bounds on both the left and right residuals (weaker than A/B)
    can be obtained by multiplying by |U⁻¹| or |L⁻¹|.

    The hypothesis `hMixed` is the local Method C error analysis; later
    theorems in this file derive forward-error consequences from it. -/
theorem methodC_mixed_residual (n : ℕ) (fp : FPModel)
    (U_hat L_hat X_hat : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp n)
    -- Hypothesis: X̂ is computed by Method C with the given error structure
    (hMixed : ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|) :=
  hMixed

/-- **Method C forward error relative to LU-inverse** (from eq. 13.19).

    From the mixed residual ÛX̂L̂ = I + E, multiplying by Û⁻¹ on the left
    and L̂⁻¹ on the right gives X̂ = Û⁻¹L̂⁻¹ + Û⁻¹EL̂⁻¹.
    The forward error relative to the LU-inverse satisfies:
      |X̂ − Û⁻¹L̂⁻¹| ≤ cₙu|Û⁻¹| · |Û||X̂||L̂| · |L̂⁻¹|. -/
theorem methodC_forward_error (n : ℕ) (fp : FPModel)
    (U_hat L_hat X_hat : Fin n → Fin n → ℝ)
    (U_inv L_inv : Fin n → Fin n → ℝ)
    (hUinv : IsLeftInverse n U_hat U_inv)
    (hLinv : IsRightInverse n L_hat L_inv)
    (_hn : gammaValid fp n)
    (hMixed : ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|)) :
    ∀ i j : Fin n,
      |X_hat i j - matMul n U_inv L_inv i j| ≤
      gamma fp n *
        ∑ a : Fin n, |U_inv i a| *
          (∑ b : Fin n, (∑ k₁ : Fin n, |U_hat a k₁| *
            (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) *
              |L_inv b j|) := by
  intro i j
  let γ := gamma fp n
  -- Define E(a,b) = (ÛX̂L̂)_{ab} − δ_{ab}
  let E : Fin n → Fin n → ℝ := fun a b =>
    ∑ k₁ : Fin n, U_hat a k₁ * (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) -
      if a = b then 1 else 0
  -- Step 1: Apply L̂·L_inv = I to simplify ∑_b (∑_k₂ X̂·L̂)·L_inv = X̂
  have hLinv_app : ∀ k₁ : Fin n,
      ∑ b : Fin n, (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j =
      X_hat k₁ j := by
    intro k₁
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (k₂ b : Fin n), X_hat k₁ k₂ * L_hat k₂ b * L_inv b j =
      X_hat k₁ k₂ * (L_hat k₂ b * L_inv b j) from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum, hLinv _ j]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Step 2: Apply U_inv·Û = I to simplify ∑_a U_inv·(∑_k₁ Û·X̂) = X̂
  have hUinv_app :
      ∑ a : Fin n, U_inv i a * (∑ k₁ : Fin n, U_hat a k₁ * X_hat k₁ j) =
      X_hat i j := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hUinv i]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 3: Simplify ∑_b E(a,b)·L_inv(b,j) = ∑_k₁ Û(a,k₁)·X̂(k₁,j) − L_inv(a,j)
  have hEL : ∀ a : Fin n,
      ∑ b : Fin n, E a b * L_inv b j =
      ∑ k₁ : Fin n, U_hat a k₁ * X_hat k₁ j - L_inv a j := by
    intro a; simp only [E]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k₁ _
      simp_rw [show ∀ b : Fin n,
          U_hat a k₁ * (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j =
          U_hat a k₁ * ((∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j)
        from fun _ => by ring]
      rw [← Finset.mul_sum]
      congr 1; exact hLinv_app k₁
    · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 4: Algebraic identity ∑_a U_inv·(∑_b E·L_inv) = X̂ − U_inv·L_inv
  have hIdentity : ∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j) =
      X_hat i j - matMul n U_inv L_inv i j := by
    simp_rw [hEL, mul_sub, Finset.sum_sub_distrib]
    unfold matMul; linarith [hUinv_app]
  -- Step 5: Bound |U_inv · E · L_inv| ≤ γ · |U_inv| · |E| · |L_inv|
  rw [show X_hat i j - matMul n U_inv L_inv i j =
    ∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j) from hIdentity.symm]
  calc |∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j)|
      ≤ ∑ a : Fin n, |U_inv i a| * |∑ b : Fin n, E a b * L_inv b j| := by
        calc _ ≤ ∑ a, |U_inv i a * (∑ b, E a b * L_inv b j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro a _; exact abs_mul _ _
    _ ≤ ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, |E a b| * |L_inv b j|) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ ∑ b, |E a b * L_inv b j| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro b _; exact abs_mul _ _
    _ ≤ ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, (γ * ∑ k₁ : Fin n, |U_hat a k₁| *
          (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro b _
        exact mul_le_mul_of_nonneg_right (hMixed a b) (abs_nonneg _)
    _ = γ * ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, (∑ k₁ : Fin n, |U_hat a k₁| *
          (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        have hfact : ∀ b : Fin n,
            (γ * ∑ k₁ : Fin n, |U_hat a k₁| *
              (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j| =
            γ * ((∑ k₁ : Fin n, |U_hat a k₁| *
              (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) :=
          fun _ => by ring
        simp_rw [hfact, ← Finset.mul_sum]; ring

-- §13.3.4  Method D: compute L⁻¹ and U⁻¹ separately, form product

/-- **Abstract Method D left residual interface** (Higham eq. 13.20–13.23).

    Method D: compute X_L ≈ L⁻¹ and X_U ≈ U⁻¹ separately,
    then form X̂ = fl(X_U · X_L).

    From eq. 13.20: X̂ = X_U · X_L + Δ(X_U, X_L).
    The left residual satisfies (eq. 13.23):
      |X̂A − I| ≤ c''ₙu|U⁻¹||L⁻¹||L̂||Û|.

    This theorem records the named residual contract once the separate
    triangular-inverse and matrix-product error terms have been combined by an
    external/local Method D analysis. -/
theorem methodD_left_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (_hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (_hn : gammaValid fp n)
    -- X_L has left residual: |X_L · L̂ − I| ≤ γₙ|X_L||L̂|
    (_hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    -- X_U has right residual: |Û · X_U − I| ≤ γₙ|Û||X_U|
    -- (or equivalently left residual |X_U · Û − I| ≤ γₙ|X_U||Û|)
    (_hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    -- X̂ = fl(X_U · X_L) with product error
    (_hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    -- The left residual bound, combining all four error terms.
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) :=
  hLeftRes

/-- **Abstract Method D SPD specialization** (Higham §13.3.4, p. 274).

    For A = RᵀR (Cholesky), Method D computes X_R ≈ R⁻¹ and forms
    X̂ = X_R · X_Rᵀ.  Using the symmetry, the left residual satisfies
      |X̂A − I| ≤ dₙu|X_R||X_Rᵀ||R̂ᵀ||R̂|.

    This is the specialization of methodD_left_residual with
    L̂ = R̂ᵀ, Û = R̂, X_L = X_Rᵀ, X_U = X_R.  The final specialized
    residual is supplied as `hLeftRes`. -/
theorem methodD_spd_left_residual (n : ℕ) (fp : FPModel)
    (A R_hat : Fin n → Fin n → ℝ)
    (X_R X_hat : Fin n → Fin n → ℝ)
    (_hSPD : IsSymPosDef n A)
    (_hn : gammaValid fp n)
    -- Cholesky: A + ΔA = R̂ᵀR̂ with |ΔA| ≤ γₙ|R̂ᵀ||R̂|
    (_hChol : ∀ i j : Fin n,
      |A i j - ∑ k : Fin n, R_hat k i * R_hat k j| ≤
      gamma fp n * ∑ k : Fin n, |R_hat k i| * |R_hat k j|)
    -- X_R has right residual for R̂⁻¹
    (_hXR_res : ∀ i j : Fin n,
      |∑ k : Fin n, R_hat i k * X_R k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |R_hat i k| * |X_R k j|)
    -- X̂ = fl(X_R · X_Rᵀ)
    (_hProd : MatProdError n X_hat
      (matMul n X_R (fun i j => X_R j i))
      (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_R i k| * |X_R j k|))
    -- The left residual bound (specialization of methodD_left_residual
    -- with L̂ = R̂ᵀ, Û = R̂, X_L = X_Rᵀ, X_U = X_R).
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l : Fin n, |X_R i l| * |X_R k₁ l|) *
          (∑ k₂ : Fin n, |R_hat k₂ k₁| * |R_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l : Fin n, |X_R i l| * |X_R k₁ l|) *
          (∑ k₂ : Fin n, |R_hat k₂ k₁| * |R_hat k₂ j|) :=
  hLeftRes

-- §13.3.5  Summary: all methods have comparable residual bounds

/-- **Eq. 13.24**: Bound on how left and right residuals of X_L can differ.

    |X_L · L̂ − I| ≤ |L̂⁻¹| · |L̂ · X_L − I| · |L̂|.

    This shows the left and right residuals can differ by a factor as large
    as |(L⁻¹)ᵢⱼ| ≤ 2^{n-1}, but for well-conditioned L they are similar. -/
theorem left_right_residual_comparison (n : ℕ)
    (L L_inv X_L : Fin n → Fin n → ℝ)
    (hInv : IsLeftInverse n L L_inv) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L k j - if i = j then 1 else 0| ≤
      ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n,
          |∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂ -
            if k₁ = k₂ then 1 else 0| *
          |L k₂ j|) := by
  intro i j
  -- Algebraic identity: X_L·L − I = L⁻¹·(L·X_L − I)·L
  let E : Fin n → Fin n → ℝ := fun k₁ k₂ =>
    ∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂ - if k₁ = k₂ then (1 : ℝ) else 0
  -- Part B: ∑_{k₁} L⁻¹(i,k₁) · L(k₁,j) = δ(i,j)
  have hPartB : ∑ k₁ : Fin n, L_inv i k₁ * L k₁ j =
      if i = j then (1 : ℝ) else 0 := hInv i j
  -- Part A: (L⁻¹ · L · X_L · L)_{ij} = (X_L · L)_{ij}
  have hPartA : ∑ k₁ : Fin n, L_inv i k₁ *
      (∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂) * L k₂ j) =
      ∑ k : Fin n, X_L i k * L k j := by
    -- Rewrite inner: ∑_{k₂} (∑_{k₃} L·X_L) · L = ∑_{k₃} L · (X_L·L)
    have hInner : ∀ k₁ : Fin n,
        ∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂) * L k₂ j =
        ∑ k₃ : Fin n, L k₁ k₃ * (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) := by
      intro k₁
      simp_rw [Finset.sum_mul, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
    simp_rw [hInner]
    -- Goal: ∑_{k₁} L⁻¹ ik₁ * ∑_{k₃} L k₁k₃ * (X_L·L)_{k₃j}
    -- Distribute outer product using explicit have
    have hOuter : ∀ k₁ : Fin n,
        L_inv i k₁ * ∑ k₃ : Fin n, L k₁ k₃ *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) =
        ∑ k₃ : Fin n, L_inv i k₁ * L k₁ k₃ *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) := by
      intro k₁; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₃ _; ring
    simp_rw [hOuter]
    rw [Finset.sum_comm]
    -- Factor out (∑ k₂, X_L·L) from inner sum over k₁
    have hFactor : ∀ k₃ : Fin n,
        ∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₃ *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) =
        (∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₃) *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) := by
      intro k₃; rw [Finset.sum_mul]
    simp_rw [hFactor]
    have hInvL : ∀ k₃ : Fin n,
        (∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₃) = if i = k₃ then 1 else 0 :=
      fun k₃ => hInv i k₃
    simp_rw [hInvL, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  -- RHS expansion: ∑ L⁻¹ · (∑ E · L) = Part A − Part B
  have hRHS : ∑ k₁ : Fin n, L_inv i k₁ *
      (∑ k₂ : Fin n, E k₁ k₂ * L k₂ j) =
      ∑ k : Fin n, X_L i k * L k j - (if i = j then (1 : ℝ) else 0) := by
    simp only [E]
    -- E k₁ k₂ = (∑ L·X_L) − δ, so E·L = (∑ L·X_L)·L − δ·L
    have hExpand : ∀ k₁ : Fin n,
        ∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂ -
          if k₁ = k₂ then (1 : ℝ) else 0) * L k₂ j =
        ∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂) * L k₂ j -
        L k₁ j := by
      intro k₁
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      congr 1
      -- ∑_{k₂} δ(k₁,k₂) · L(k₂,j) = L(k₁,j)
      have : ∀ k₂ : Fin n,
          (if k₁ = k₂ then (1 : ℝ) else 0) * L k₂ j =
          if k₁ = k₂ then L k₂ j else 0 := by
        intro k₂; split_ifs <;> ring
      simp_rw [this]
      simp [Finset.mem_univ]
    simp_rw [hExpand, mul_sub, Finset.sum_sub_distrib]
    rw [hPartA, hPartB]
  rw [← hRHS]
  -- Triangle inequality: |∑ L⁻¹ · (∑ E · L)| ≤ ∑ |L⁻¹| · |∑ E · L| ≤ ∑ |L⁻¹| · (∑ |E| · |L|)
  calc |∑ k₁ : Fin n, L_inv i k₁ * (∑ k₂ : Fin n, E k₁ k₂ * L k₂ j)|
      ≤ ∑ k₁ : Fin n, |L_inv i k₁ * (∑ k₂ : Fin n, E k₁ k₂ * L k₂ j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |L_inv i k₁| * |∑ k₂ : Fin n, E k₁ k₂ * L k₂ j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |E k₁ k₂| * |L k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |∑ k₂ : Fin n, E k₁ k₂ * L k₂ j|
            ≤ ∑ k₂ : Fin n, |E k₁ k₂ * L k₂ j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k₂ : Fin n, |E k₁ k₂| * |L k₂ j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _

end LeanFpAnalysis.FP
