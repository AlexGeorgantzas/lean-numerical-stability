-- Algorithms/MatrixInversion.lean
--
-- Higham Chapter 14: Matrix Inversion.
-- §14.1: Ideal perturbation bounds for computed inverses.
-- §14.2: Triangular matrix inversion (Methods 1, 2, block variants).
-- §14.3: Full matrix inversion via LU factorization (Methods A, B, C, D).
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
import LeanFpAnalysis.FP.Algorithms.HighamChapter9

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §14.1  Δ-notation: product error bounds
-- ============================================================

/-- **Matrix product error bound** (Δ-notation, Higham §14.1).

    If Ĉ = fl(A₁ · A₂) then |Ĉ − A₁A₂| ≤ ε · (|A₁| · |A₂|).
    This predicate captures the general statement for any computed product. -/
def MatProdError (n : ℕ) (C_hat : Fin n → Fin n → ℝ)
    (C_exact : Fin n → Fin n → ℝ) (ε : ℝ)
    (absProduct : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |C_hat i j - C_exact i j| ≤ ε * absProduct i j

-- ============================================================
-- §14.1  Ideal perturbation bounds (eqs. 14.1–14.3)
-- ============================================================

/-- **Right residual of a computed inverse** (Higham eq. 14.1).

    If Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|, then AY − I = −ΔA · Y,
    so |AY − I| ≤ ε|A||Y|.

    We state the bound with |Y| rather than |A⁻¹| to avoid circularity;
    the first-order version |A⁻¹| + O(ε) follows from eq. 14.3. -/
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

/-- **Left residual of a computed inverse** (Higham eq. 14.2).

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

/-- **Forward error for a computed inverse** (Higham eq. 14.3).

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
-- §14.1  Residual comparison: inversion vs GEPP
-- ============================================================

/-- **Residual bound for solving via matrix inversion** (Higham §14.1, p. 262).

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
-- §14.2  Triangular matrix inversion
-- ============================================================

-- §14.2.1  Method 1 (column-by-column forward substitution)

/-- **Method 1 right residual for triangular inversion** (Higham eq. 14.4).

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

/-- **Method 1 right residual — matrix form** (Higham eq. 14.4).

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

/-- **Method 1 forward error** (Higham eq. 14.5).

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

/-- **Method 1 first-order forward error** (Higham eq. 14.6).

    |X̂ − L⁻¹| ≤ γ(n)|L⁻¹||L||L⁻¹| + O(u²).

    Since X̂ = L⁻¹ + O(u), replacing |X̂| by |L⁻¹| in eq. 14.5 gives
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

/-- **Method 1 normwise forward error** (Higham eq. 14.7).

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

-- §14.2.1  Method 2 (reverse-order column computation via mat-vec multiply)

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

/-- **Abstract Lemma 14.1 interface** (Higham eq. 14.8): Method 2 left residual.

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

-- §14.2.2  Block methods

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

/-- **Lemma 14.2** (Higham eq. 14.10): Method 1B right residual.

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

/-- **Abstract Lemma 14.3 interface**: Method 2C left residual.

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
-- §14.3  Full matrix inversion via LU factorization
-- ============================================================

-- §14.3.1  Method A: solve Ax̂ⱼ = eⱼ for each column

/-- Computed inverse produced by Method A after an LU factorization: each
column solves `L_hat y = e_j`, then `U_hat x = y`. -/
noncomputable def methodAComputedInverse (fp : FPModel) (n : ℕ)
    (L_hat U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    let b_j : Fin n → ℝ := fun k => if k = j then 1 else 0
    let y_hat := fl_forwardSub fp n L_hat b_j
    fl_backSub fp n U_hat y_hat i

/-- **Method A column-wise backward error** (Higham eq. 14.15).

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

/-- Method A column-wise backward error specialized to the named computed
inverse matrix `methodAComputedInverse`. -/
theorem methodA_column_backward_error_computed_inverse (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n,
          (A i k + ΔA i k) *
            methodAComputedInverse fp n L_hat U_hat k j =
          if i = j then 1 else 0 := by
  intro j
  simpa [methodAComputedInverse] using
    methodA_column_backward_error n fp A L_hat U_hat
      hL_diag hU_diag hLU hn j

/-- Method A column-wise backward error with an exposed LU factorization
coefficient.  The LU factorization is certified at level `epsLU`, while the
forward and back triangular solves are still charged at `gamma fp n`. -/
theorem methodA_column_backward_error_factor_bound (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      let b_j : Fin n → ℝ := fun i => if i = j then 1 else 0
      let y_hat := fl_forwardSub fp n L_hat b_j
      let x_hat_j := fl_backSub fp n U_hat y_hat
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤
          (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * x_hat_j k = b_j i := by
  intro j b_j y_hat x_hat_j
  exact
    lu_solve_backward_error_factor_gamma fp n A L_hat U_hat b_j
      hepsLU hL_diag hU_diag hLU hn

/-- Coefficient-exposed Method A column-wise backward error specialized to the
named computed inverse matrix `methodAComputedInverse`. -/
theorem methodA_column_backward_error_computed_inverse_factor_bound
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤
          (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n,
          (A i k + ΔA i k) *
            methodAComputedInverse fp n L_hat U_hat k j =
          if i = j then 1 else 0 := by
  intro j
  simpa [methodAComputedInverse] using
    methodA_column_backward_error_factor_bound n fp A L_hat U_hat
      hepsLU hL_diag hU_diag hLU hn j

/-- **Method A right residual** (Higham eq. 14.16).

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

/-- Method A right residual with an externally supplied componentwise column
backward-error coefficient `c`. -/
theorem methodA_right_residual_of_column_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_hat : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hCol : ∀ j : Fin n, ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ c *
        ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
      ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      c * ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
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
    _ ≤ ∑ k : Fin n, (c *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA_bound i k) (abs_nonneg _)
    _ = c * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
            |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Method A forward error** (Higham eq. 14.17).

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

/-- Method A forward error with an externally supplied residual coefficient
`c`. -/
theorem methodA_forward_error_of_residual_bound (n : ℕ)
    (A A_inv L_hat U_hat X_hat : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hRes : ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      c * ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
        |X_hat k j|) :
    ∀ i j : Fin n,
      |X_hat i j - A_inv i j| ≤
      c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
  intro i j
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
        (c * ∑ k₂ : Fin n,
          (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
            |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- Method A computed inverse entrywise forward-error certificate for the
repository nonsingular inverse, with a visible scalar budget `eta`. -/
theorem methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_budget
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {eta : ℝ}
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hBudget :
      ∀ i j : Fin n,
        (3 * gamma fp n + gamma fp n ^ 2) *
            ∑ k₁ : Fin n,
              |nonsingInv n A i k₁| *
                (∑ k₂ : Fin n,
                  (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp n L_hat U_hat k₂ j|) ≤ eta) :
    ∀ i j : Fin n,
      |nonsingInv n A i j -
          methodAComputedInverse fp n L_hat U_hat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse n A (nonsingInv n A) :=
    isInverse_nonsingInv_of_det_ne_zero n A hdet
  have hCol :=
    methodA_column_backward_error_computed_inverse n fp A L_hat U_hat
      hL_diag hU_diag hLU hn
  have hRes :=
    methodA_right_residual n fp A L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) hn hCol
  have hFwd :=
    methodA_forward_error n fp A (nonsingInv n A) L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) hInv.1 hn hRes i j
  rw [abs_sub_comm]
  exact le_trans hFwd (hBudget i j)

/-- Method A computed inverse entrywise forward-error certificate with an
exposed LU factorization coefficient `epsLU`.  This is the implementation-facing
variant used when the LU factors are certified for a computed input matrix and
that input error has already been transferred into the `LUBackwardError`
coefficient. -/
theorem methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_factor_budget
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU eta : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n)
    (hBudget :
      ∀ i j : Fin n,
        (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ k₁ : Fin n,
              |nonsingInv n A i k₁| *
                (∑ k₂ : Fin n,
                  (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp n L_hat U_hat k₂ j|) ≤ eta) :
    ∀ i j : Fin n,
      |nonsingInv n A i j -
          methodAComputedInverse fp n L_hat U_hat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse n A (nonsingInv n A) :=
    isInverse_nonsingInv_of_det_ne_zero n A hdet
  have hCol :=
    methodA_column_backward_error_computed_inverse_factor_bound n fp A L_hat U_hat
      hepsLU hL_diag hU_diag hLU hn
  let c := epsLU + 2 * gamma fp n + gamma fp n ^ 2
  have hRes :=
    methodA_right_residual_of_column_bound n A L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) c hCol
  have hFwd :=
    methodA_forward_error_of_residual_bound n A (nonsingInv n A) L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) c hInv.1 hRes i j
  rw [abs_sub_comm]
  exact le_trans hFwd (hBudget i j)

-- §14.3.2  Method B: compute U⁻¹ then solve XL̂ = X_U

/-- **Method B left residual** (Higham eq. 14.18).

    Method B: compute X_U ≈ U⁻¹ (by an analogue of Method 2 or 2C for upper
    triangular matrices), then solve for X in XL̂ = X_U by back substitution
    from the right.

    The left residual satisfies:
      |X̂A − I| ≤ c'ₙu|X̂||L̂||Û|.

    Note: eq. 14.18 is the left residual analogue of eq. 14.16.
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

-- §14.3.3  Method C: solve UXL = I

/-- **Abstract Method C mixed residual interface** (Higham eq. 14.19).

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

/-- **Method C forward error relative to LU-inverse** (from eq. 14.19).

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

-- §14.3.4  Method D: compute L⁻¹ and U⁻¹ separately, form product

/-- **Abstract Method D left residual interface** (Higham eq. 14.20–14.23).

    Method D: compute X_L ≈ L⁻¹ and X_U ≈ U⁻¹ separately,
    then form X̂ = fl(X_U · X_L).

    From eq. 14.20: X̂ = X_U · X_L + Δ(X_U, X_L).
    The left residual satisfies (eq. 14.23):
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

/-- **Abstract Method D SPD specialization** (Higham §14.3.4, p. 274).

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

-- §14.3.5  Summary: all methods have comparable residual bounds

/-- **Eq. 14.24**: Bound on how left and right residuals of X_L can differ.

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

/-- Right inverse residual `AX - I`, used in Higham Chapter 14 problems. -/
noncomputable def inverseRightResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n A X i j - idMatrix n i j

/-- Left inverse residual `XA - I`, used in Higham Chapter 14 problems. -/
noncomputable def inverseLeftResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n X A i j - idMatrix n i j

/-- Higham, 2nd ed., Chapter 14, Problem 14.3 algebraic identity:
    `AX - I = A (XA - I) A⁻¹`. -/
theorem higham14_problem14_3_right_residual_eq_mul_left_residual (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    inverseRightResidual n A X =
      matMul n (matMul n A (inverseLeftResidual n A X)) A_inv := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let XM : Matrix (Fin n) (Fin n) ℝ := X
  have hAAinv : AM * AinvM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hRight i j
  have hmat :
      AM * XM - 1 = AM * (XM * AM - 1) * AinvM := by
    calc
      AM * XM - 1
          = AM * XM * (AM * AinvM) - AM * AinvM := by
              rw [hAAinv]
              simp
      _ = AM * (XM * AM - 1) * AinvM := by
              noncomm_ring
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [inverseRightResidual, inverseLeftResidual, matMul, idMatrix,
    AM, AinvM, XM, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- Higham, 2nd ed., Chapter 14, Problem 14.3 algebraic identity:
    `XA - I = A⁻¹ (AX - I) A`. -/
theorem higham14_problem14_3_left_residual_eq_mul_right_residual (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    inverseLeftResidual n A X =
      matMul n (matMul n A_inv (inverseRightResidual n A X)) A := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let XM : Matrix (Fin n) (Fin n) ℝ := X
  have hAinvA : AinvM * AM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hLeft i j
  have hmat :
      XM * AM - 1 = AinvM * (AM * XM - 1) * AM := by
    calc
      XM * AM - 1
          = AinvM * AM * XM * AM - AinvM * AM := by
              rw [hAinvA]
              simp
      _ = AinvM * (AM * XM - 1) * AM := by
              noncomm_ring
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [inverseRightResidual, inverseLeftResidual, matMul, idMatrix,
    AM, AinvM, XM, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- Higham, 2nd ed., Chapter 14, Problem 14.3, infinity-norm half:
    `‖AX - I‖∞ / ‖XA - I‖∞ ≤ κ∞(A)`. -/
theorem higham14_problem14_3_right_over_left_residual_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv)
    (hLeftResPos : 0 < infNorm (inverseLeftResidual n A X)) :
    infNorm (inverseRightResidual n A X) /
        infNorm (inverseLeftResidual n A X) ≤
      kappaInf n hn A A_inv := by
  have hres_eq :=
    higham14_problem14_3_right_residual_eq_mul_left_residual
      n A A_inv X hRight
  have hnorm :
      infNorm (inverseRightResidual n A X) ≤
        (infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv := by
    calc
      infNorm (inverseRightResidual n A X)
          = infNorm (matMul n (matMul n A (inverseLeftResidual n A X)) A_inv) := by
              rw [hres_eq]
      _ ≤ infNorm (matMul n A (inverseLeftResidual n A X)) * infNorm A_inv :=
              infNorm_matMul_le hn (matMul n A (inverseLeftResidual n A X)) A_inv
      _ ≤ (infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv := by
              exact mul_le_mul_of_nonneg_right
                (infNorm_matMul_le hn A (inverseLeftResidual n A X))
                (infNorm_nonneg A_inv)
  have hdiv := div_le_div_of_nonneg_right hnorm (le_of_lt hLeftResPos)
  calc
    infNorm (inverseRightResidual n A X) /
        infNorm (inverseLeftResidual n A X)
        ≤ ((infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv) /
            infNorm (inverseLeftResidual n A X) := hdiv
    _ = infNorm A * infNorm A_inv := by
        field_simp [ne_of_gt hLeftResPos]
    _ = kappaInf n hn A A_inv := by
        rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]

/-- Higham, 2nd ed., Chapter 14, Problem 14.3, infinity-norm half:
    `‖XA - I‖∞ / ‖AX - I‖∞ ≤ κ∞(A)`. -/
theorem higham14_problem14_3_left_over_right_residual_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (hRightResPos : 0 < infNorm (inverseRightResidual n A X)) :
    infNorm (inverseLeftResidual n A X) /
        infNorm (inverseRightResidual n A X) ≤
      kappaInf n hn A A_inv := by
  have hres_eq :=
    higham14_problem14_3_left_residual_eq_mul_right_residual
      n A A_inv X hLeft
  have hnorm :
      infNorm (inverseLeftResidual n A X) ≤
        (infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A := by
    calc
      infNorm (inverseLeftResidual n A X)
          = infNorm (matMul n (matMul n A_inv (inverseRightResidual n A X)) A) := by
              rw [hres_eq]
      _ ≤ infNorm (matMul n A_inv (inverseRightResidual n A X)) * infNorm A :=
              infNorm_matMul_le hn
                (matMul n A_inv (inverseRightResidual n A X)) A
      _ ≤ (infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A := by
              exact mul_le_mul_of_nonneg_right
                (infNorm_matMul_le hn A_inv (inverseRightResidual n A X))
                (infNorm_nonneg A)
  have hdiv := div_le_div_of_nonneg_right hnorm (le_of_lt hRightResPos)
  calc
    infNorm (inverseLeftResidual n A X) /
        infNorm (inverseRightResidual n A X)
        ≤ ((infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A) /
            infNorm (inverseRightResidual n A X) := hdiv
    _ = infNorm A_inv * infNorm A := by
        field_simp [ne_of_gt hRightResPos]
    _ = kappaInf n hn A A_inv := by
        rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]
        ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.3:
    for nonzero left and right residuals,
    `max (‖AX-I‖∞/‖XA-I‖∞) (‖XA-I‖∞/‖AX-I‖∞) ≤ κ∞(A)`. -/
theorem higham14_problem14_3_max_residual_ratio_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hLeftResPos : 0 < infNorm (inverseLeftResidual n A X))
    (hRightResPos : 0 < infNorm (inverseRightResidual n A X)) :
    max
        (infNorm (inverseRightResidual n A X) /
          infNorm (inverseLeftResidual n A X))
        (infNorm (inverseLeftResidual n A X) /
          infNorm (inverseRightResidual n A X))
      ≤ kappaInf n hn A A_inv := by
  exact max_le
    (higham14_problem14_3_right_over_left_residual_infNorm_le_kappa
      n hn A A_inv X hInv.2 hLeftResPos)
    (higham14_problem14_3_left_over_right_residual_infNorm_le_kappa
      n hn A A_inv X hInv.1 hRightResPos)

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 matrix `A(eps)`.

The source uses this two-by-two family, with `0 < eps << 1`, to show that
the right residual `AX-I` can be arbitrarily larger than the left residual
`XA-I`. -/
noncomputable def higham14_problem14_4_A (eps : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![![1 / eps, 1], ![1 / eps ^ 2 - 1, 1 / eps]]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 approximate inverse family. -/
noncomputable def higham14_problem14_4_X (eps : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![![1 - eps + 2 / eps, -2 - eps],
    ![2 - eps + 1 / eps - 1 / eps ^ 2, -1 - eps + 1 / eps]]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 exact left product:
    `X(eps) A(eps) = [[1+eps,-eps],[eps,1-eps]]`. -/
theorem higham14_problem14_4_XA_eq (eps : ℝ) (heps : eps ≠ 0) :
    matMul 2 (higham14_problem14_4_X eps) (higham14_problem14_4_A eps) =
      ![![1 + eps, -eps], ![eps, 1 - eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham14_problem14_4_X, higham14_problem14_4_A, matMul]
  all_goals
    field_simp [heps]
    ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 exact right product. -/
theorem higham14_problem14_4_AX_eq (eps : ℝ) (heps : eps ≠ 0) :
    matMul 2 (higham14_problem14_4_A eps) (higham14_problem14_4_X eps) =
      ![![1 / eps ^ 2 + 2 / eps + 1 - eps, -2 - eps - 1 / eps],
        ![1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps,
          -1 / eps ^ 2 - 2 / eps + 1 + eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham14_problem14_4_X, higham14_problem14_4_A, matMul]
  all_goals
    field_simp [heps]
    ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the left residual is the small matrix with entries `±eps`. -/
theorem higham14_problem14_4_left_residual_eq
    (eps : ℝ) (heps : eps ≠ 0) :
    inverseLeftResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps) =
      ![![eps, -eps], ![eps, -eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseLeftResidual, idMatrix,
      higham14_problem14_4_XA_eq eps heps]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    for `0 <= eps`, `||X(eps)A(eps)-I||_∞ = 2 eps`. -/
theorem higham14_problem14_4_left_residual_infNorm_eq
    (eps : ℝ) (hpos : 0 ≤ eps) (heps : eps ≠ 0) :
    infNorm (inverseLeftResidual 2
      (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) =
      2 * eps := by
  rw [higham14_problem14_4_left_residual_eq eps heps]
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;> simp [hpos, abs_of_nonneg, abs_of_nonpos] <;> linarith
    · nlinarith [hpos]
  · have hrow :=
      row_sum_le_infNorm (![![eps, -eps], ![eps, -eps]] :
        Fin 2 → Fin 2 → ℝ) (0 : Fin 2)
    have hsum :
        (∑ j : Fin 2,
          |(![![eps, -eps], ![eps, -eps]] :
            Fin 2 → Fin 2 → ℝ) (0 : Fin 2) j|) = 2 * eps := by
      simp [hpos, abs_of_nonneg, abs_of_nonpos]
      ring
    linarith

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 support:
    the displayed lower-left entry of `AX-I` dominates `eps^{-3}` for
    `0 < eps <= 1`. -/
lemma higham14_problem14_4_right_residual_entry_ge_inv_cube
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / eps ^ 3 ≤
      1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps := by
  field_simp [ne_of_gt hpos]
  nlinarith [hpos, hle, sq_nonneg eps, sq_nonneg (eps - 1)]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    for `0 < eps <= 1`, the right residual has infinity norm at least
    `eps^{-3}`. -/
theorem higham14_problem14_4_right_residual_infNorm_ge_inv_cube
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / eps ^ 3 ≤
      infNorm (inverseRightResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  have heps : eps ≠ 0 := ne_of_gt hpos
  let M := inverseRightResidual 2
    (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)
  have hentry : M (1 : Fin 2) (0 : Fin 2) =
      1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps := by
    simp [M, inverseRightResidual, idMatrix,
      higham14_problem14_4_AX_eq eps heps]
  have hentry_ge : 1 / eps ^ 3 ≤ M (1 : Fin 2) (0 : Fin 2) := by
    rw [hentry]
    exact higham14_problem14_4_right_residual_entry_ge_inv_cube eps hpos hle
  have habs : M (1 : Fin 2) (0 : Fin 2) ≤ |M (1 : Fin 2) (0 : Fin 2)| :=
    le_abs_self _
  have hsingle :
      |M (1 : Fin 2) (0 : Fin 2)| ≤ ∑ j : Fin 2, |M (1 : Fin 2) j| := by
    simp
  exact le_trans hentry_ge
    (le_trans habs (le_trans hsingle (row_sum_le_infNorm M (1 : Fin 2))))

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the right-over-left residual ratio is bounded below by `1/(2 eps^4)`. -/
theorem higham14_problem14_4_right_over_left_ratio_ge
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / (2 * eps ^ 4) ≤
      infNorm (inverseRightResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  have heps : eps ≠ 0 := ne_of_gt hpos
  have hleft :=
    higham14_problem14_4_left_residual_infNorm_eq eps (le_of_lt hpos) heps
  have hleft_pos :
      0 < infNorm (inverseLeftResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
    rw [hleft]
    nlinarith
  have hright :=
    higham14_problem14_4_right_residual_infNorm_ge_inv_cube eps hpos hle
  calc
    1 / (2 * eps ^ 4) = (1 / eps ^ 3) / (2 * eps) := by
      field_simp [heps]
    _ = (1 / eps ^ 3) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
      rw [hleft]
    _ ≤ infNorm (inverseRightResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) :=
      div_le_div_of_nonneg_right hright (le_of_lt hleft_pos)

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the ratio `||AX-I||_∞ / ||XA-I||_∞` is arbitrarily large for the displayed
    two-by-two family. -/
theorem higham14_problem14_4_right_over_left_ratio_arbitrarily_large
    (K : ℝ) :
    ∃ eps : ℝ,
      0 < eps ∧ eps ≤ 1 ∧
        K <
          infNorm (inverseRightResidual 2
            (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
            infNorm (inverseLeftResidual 2
              (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  let eps : ℝ := (2 * (|K| + 1))⁻¹
  have hden : 0 < 2 * (|K| + 1) := by positivity
  have hpos : 0 < eps := by
    dsimp [eps]
    exact inv_pos.mpr hden
  have hle : eps ≤ 1 := by
    dsimp [eps]
    have hden_ge_one : 1 ≤ 2 * (|K| + 1) := by
      have habs : 0 ≤ |K| := abs_nonneg K
      nlinarith
    exact inv_le_one_of_one_le₀ hden_ge_one
  refine ⟨eps, hpos, hle, ?_⟩
  have hlower :=
    higham14_problem14_4_right_over_left_ratio_ge eps hpos hle
  have htarget : K < 1 / (2 * eps ^ 4) := by
    dsimp [eps]
    have hK_lt : K < |K| + 1 := by
      have hKle : K ≤ |K| := le_abs_self K
      linarith
    have hnon : 0 ≤ |K| := abs_nonneg K
    have ht_ge_one : 1 ≤ |K| + 1 := by linarith
    have ht_nonneg : 0 ≤ |K| + 1 := by linarith
    have ht_le_pow4 : |K| + 1 ≤ (|K| + 1) ^ 4 := by
      nlinarith [ht_ge_one, ht_nonneg,
        sq_nonneg ((|K| + 1) ^ 2 - (|K| + 1))]
    have ht_le_8pow4 : |K| + 1 ≤ 2 ^ 3 * (|K| + 1) ^ 4 := by
      nlinarith
    field_simp [ne_of_gt hden]
    nlinarith [hK_lt, ht_le_8pow4]
  exact lt_of_lt_of_le htarget hlower

/-- Scalar gamma collapse used in Higham Chapter 14, Problem 14.5:
    `u + gamma_n <= gamma_{n+1}`. -/
lemma higham14_unit_roundoff_add_gamma_le_gamma_succ
    (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    fp.u + gamma fp n ≤ gamma fp (n + 1) := by
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega : 1 ≤ n + 1) hn1
  have hvalidn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  have hγ_sum : gamma fp 1 + gamma fp n + gamma fp 1 * gamma fp n ≤
      gamma fp (n + 1) := by
    have h := gamma_sum_le fp 1 n (by simpa [Nat.add_comm] using hn1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hu_le_γ1 : fp.u ≤ gamma fp 1 :=
    u_le_gamma fp one_pos hvalid1
  have hγprod_nonneg : 0 ≤ gamma fp 1 * gamma fp n :=
    mul_nonneg (gamma_nonneg fp hvalid1) (gamma_nonneg fp hvalidn)
  linarith

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    residual bound.

If `X` has a small right inverse residual, `|A X - I| <= u |A||X|`, and
`x_hat = fl(X b)`, then
`|A x_hat - b| <= gamma_{n+1} |A||X||b|` componentwise. -/
theorem higham14_problem14_5_right_inverse_solve_residual_bound
    (n : ℕ) (fp : FPModel)
    (A X : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |∑ j : Fin n, A i j * x_hat j - b i| ≤
        gamma fp (n + 1) *
          ∑ j : Fin n, |A i j| * (∑ k : Fin n, |X j k| * |b k|) := by
  intro x_hat i
  have hn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  obtain ⟨ΔX, hΔX_bound, hΔX_eq⟩ := matVec_backward_error fp n n X b hn
  change |∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i| ≤ _
  let S : ℝ := ∑ j : Fin n, |A i j| * (∑ k : Fin n, |X j k| * |b k|)
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hxhat : ∀ j : Fin n,
      fl_matVec fp n n X b j =
        ∑ k : Fin n, (X j k + ΔX j k) * b k := hΔX_eq
  have hmain :
      ∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i =
        (∑ k : Fin n, inverseRightResidual n A X i k * b k) +
          ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
    have hsplit :
        ∑ j : Fin n, A i j * fl_matVec fp n n X b j =
          ∑ j : Fin n, A i j * (∑ k : Fin n, X j k * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hxhat j, ← mul_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hAXb :
        ∑ j : Fin n, A i j * (∑ k : Fin n, X j k * b k) =
          ∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    have hb :
        b i = ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k := by
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    have hresExpand :
        (∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k) -
          ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k =
        ∑ k : Fin n, inverseRightResidual n A X i k * b k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp [inverseRightResidual, matMul, idMatrix]
      by_cases h : i = k
      · subst i
        simp
        ring_nf
      · simp [h]
    calc
      ∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i
          = (∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k +
              ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)) -
              ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k := by
            rw [hsplit, hAXb, hb]
      _ = ((∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k) -
              ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
            ring
      _ = (∑ k : Fin n, inverseRightResidual n A X i k * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
            rw [hresExpand]
  have hres_part :
      |∑ k : Fin n, inverseRightResidual n A X i k * b k| ≤ fp.u * S := by
    calc
      |∑ k : Fin n, inverseRightResidual n A X i k * b k|
          ≤ ∑ k : Fin n, |inverseRightResidual n A X i k * b k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |inverseRightResidual n A X i k| * |b k| := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (fp.u * ∑ j : Fin n, |A i j| * |X j k|) * |b k| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hRightRes i k) (abs_nonneg _)
      _ = fp.u * S := by
            simp only [S]
            calc
              ∑ k : Fin n, (fp.u * ∑ j : Fin n, |A i j| * |X j k|) * |b k|
                  = ∑ k : Fin n, ∑ j : Fin n,
                      fp.u * (|A i j| * |X j k|) * |b k| := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ j : Fin n, ∑ k : Fin n,
                      fp.u * (|A i j| * |X j k|) * |b k| := by
                    rw [Finset.sum_comm]
              _ = ∑ j : Fin n, fp.u * (|A i j| * ∑ k : Fin n, |X j k| * |b k|) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    calc
                      ∑ k : Fin n, fp.u * (|A i j| * |X j k|) * |b k|
                          = ∑ k : Fin n, fp.u * (|A i j| * (|X j k| * |b k|)) := by
                            apply Finset.sum_congr rfl
                            intro k _
                            ring
                      _ = fp.u * (∑ k : Fin n, |A i j| * (|X j k| * |b k|)) := by
                            rw [← Finset.mul_sum]
                      _ = fp.u * (|A i j| * ∑ k : Fin n, |X j k| * |b k|) := by
                            congr 1
                            rw [← Finset.mul_sum]
              _ = fp.u * ∑ j : Fin n, |A i j| * (∑ k : Fin n, |X j k| * |b k|) := by
                    rw [Finset.mul_sum]
  have hround_part :
      |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)| ≤
        gamma fp n * S := by
    calc
      |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)|
          ≤ ∑ j : Fin n, |A i j * (∑ k : Fin n, ΔX j k * b k)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j| * |∑ k : Fin n, ΔX j k * b k| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
      _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, |ΔX j k| * |b k|) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc
              |∑ k : Fin n, ΔX j k * b k|
                  ≤ ∑ k : Fin n, |ΔX j k * b k| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ k : Fin n, |ΔX j k| * |b k| := by
                    apply Finset.sum_congr rfl
                    intro k _
                    exact abs_mul _ _
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, (gamma fp n * |X j k|) * |b k|) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hΔX_bound j k) (abs_nonneg _)
      _ = gamma fp n * S := by
            simp only [S]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            calc
              |A i j| * (∑ k : Fin n, gamma fp n * |X j k| * |b k|)
                  = |A i j| * (gamma fp n * (∑ k : Fin n, |X j k| * |b k|)) := by
                    congr 1
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k _
                    ring
              _ = gamma fp n * (|A i j| * ∑ k : Fin n, |X j k| * |b k|) := by
                    ring
  calc
    |∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i|
        = |(∑ k : Fin n, inverseRightResidual n A X i k * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)| := by
          rw [hmain]
    _ ≤ |∑ k : Fin n, inverseRightResidual n A X i k * b k| +
          |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)| :=
          abs_add_le _ _
    _ ≤ fp.u * S + gamma fp n * S :=
          add_le_add hres_part hround_part
    _ = (fp.u + gamma fp n) * S := by ring
    _ ≤ gamma fp (n + 1) * S :=
          mul_le_mul_of_nonneg_right hcoeff hS_nonneg

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    residual bound.

If `Y` has a small left inverse residual, `|Y A - I| <= u |Y||A|`, and
`b = A x`, `y_hat = fl(Y b)`, then
`|A y_hat - b| <= gamma_{n+1} |A||Y||A||x|` componentwise. -/
theorem higham14_problem14_5_left_inverse_solve_residual_bound
    (n : ℕ) (fp : FPModel)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |matMulVec n A y_hat i - b i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A)
            (matMulVec n (absMatrix n Y)
              (matMulVec n (absMatrix n A) (absVec n x))) i := by
  intro b y_hat i
  have hn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  obtain ⟨ΔY, hΔY_bound, hΔY_eq⟩ :=
    matVec_backward_error fp n n Y (matMulVec n A x) hn
  change |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
      matMulVec n A x i| ≤ _
  let R := inverseLeftResidual n A Y
  let S : ℝ :=
    matMulVec n (absMatrix n A)
      (matMulVec n (absMatrix n Y)
        (matMulVec n (absMatrix n A) (absVec n x))) i
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  have hS_nonneg : 0 ≤ S := by
    simp only [S, matMulVec, absMatrix, absVec]
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun l _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))))
  have hyhat_vec :
      fl_matVec fp n n Y (matMulVec n A x) =
        matMulVec n (fun i j => Y i j + ΔY i j) (matMulVec n A x) := by
    ext j
    simpa [matMulVec] using hΔY_eq j
  have hYAx_split :
      matMulVec n Y (matMulVec n A x) =
        fun j => matMulVec n R x j + x j := by
    ext j
    rw [← matMulVec_matMul n Y A x j]
    simp only [R, inverseLeftResidual, matMulVec, matMul, idMatrix]
    have hdelta :
        (∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l) = x j := by
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    calc
      ∑ l : Fin n, (∑ k : Fin n, Y j k * A k l) * x l
          = ∑ l : Fin n,
              (((∑ k : Fin n, Y j k * A k l) -
                (if j = l then (1 : ℝ) else 0)) * x l +
                (if j = l then (1 : ℝ) else 0) * x l) := by
            apply Finset.sum_congr rfl
            intro l _
            ring
      _ = (∑ l : Fin n,
              ((∑ k : Fin n, Y j k * A k l) -
                (if j = l then (1 : ℝ) else 0)) * x l) +
            ∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l := by
            rw [Finset.sum_add_distrib]
      _ = (∑ l : Fin n,
              ((∑ k : Fin n, Y j k * A k l) -
                (if j = l then (1 : ℝ) else 0)) * x l) + x j := by
            rw [hdelta]
  have hmain :
      matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
          matMulVec n A x i =
        matMulVec n A (matMulVec n R x) i +
          matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i := by
    calc
      matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
          matMulVec n A x i
          = matMulVec n A
              (matMulVec n (fun j k => Y j k + ΔY j k) (matMulVec n A x)) i -
              matMulVec n A x i := by
                rw [hyhat_vec]
      _ = matMulVec n A
              (fun j => matMulVec n Y (matMulVec n A x) j +
                matMulVec n ΔY (matMulVec n A x) j) i -
              matMulVec n A x i := by
                rw [matMulVec_add_left]
      _ = (matMulVec n A (matMulVec n Y (matMulVec n A x)) i +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i) -
              matMulVec n A x i := by
                rw [matMulVec_add_right]
      _ = (matMulVec n A (fun j => matMulVec n R x j + x j) i +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i) -
              matMulVec n A x i := by
                rw [hYAx_split]
      _ = ((matMulVec n A (matMulVec n R x) i + matMulVec n A x i) +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i) -
              matMulVec n A x i := by
                rw [matMulVec_add_right]
      _ = matMulVec n A (matMulVec n R x) i +
            matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i := by
              ring
  have hres_part :
      |matMulVec n A (matMulVec n R x) i| ≤ fp.u * S := by
    calc
      |matMulVec n A (matMulVec n R x) i|
          ≤ ∑ j : Fin n, |A i j| * |matMulVec n R x j| :=
            abs_matMulVec_le n A (matMulVec n R x) i
      _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, |R j k| * |x k|) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left
              (abs_matMulVec_le n R x j) (abs_nonneg _)
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y j l| * |A l k|) * |x k|) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right
              (by simpa [R] using hLeftRes j k) (abs_nonneg _)
      _ = fp.u * S := by
            simp only [S, matMulVec, absMatrix, absVec]
            calc
              ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y j l| * |A l k|) *
                    |x k|)
                  = ∑ j : Fin n, |A i j| *
                      (fp.u * ∑ l : Fin n, |Y j l| *
                        (∑ k : Fin n, |A l k| * |x k|)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    congr 1
                    calc
                      ∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y j l| * |A l k|) *
                          |x k|
                          = ∑ k : Fin n, ∑ l : Fin n,
                              fp.u * (|Y j l| * |A l k|) * |x k| := by
                            apply Finset.sum_congr rfl
                            intro k _
                            rw [Finset.mul_sum, Finset.sum_mul]
                      _ = ∑ l : Fin n, ∑ k : Fin n,
                              fp.u * (|Y j l| * |A l k|) * |x k| := by
                            rw [Finset.sum_comm]
                      _ = fp.u * ∑ l : Fin n, |Y j l| *
                              (∑ k : Fin n, |A l k| * |x k|) := by
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro l _
                            calc
                              ∑ k : Fin n, fp.u * (|Y j l| * |A l k|) * |x k|
                                  = fp.u *
                                      (∑ k : Fin n, |Y j l| * (|A l k| * |x k|)) := by
                                    rw [Finset.mul_sum]
                                    apply Finset.sum_congr rfl
                                    intro k _
                                    ring
                              _ = fp.u * (|Y j l| *
                                      (∑ k : Fin n, |A l k| * |x k|)) := by
                                    congr 1
                                    rw [← Finset.mul_sum]
              _ = ∑ j : Fin n, fp.u *
                    (|A i j| * ∑ l : Fin n, |Y j l| *
                      (∑ k : Fin n, |A l k| * |x k|)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
              _ = fp.u * ∑ j : Fin n, |A i j| *
                    (∑ l : Fin n, |Y j l| *
                      (∑ k : Fin n, |A l k| * |x k|)) := by
                    rw [Finset.mul_sum]
  have hround_part :
      |matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i| ≤
        gamma fp n * S := by
    calc
      |matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i|
          ≤ ∑ j : Fin n, |A i j| *
              |matMulVec n ΔY (matMulVec n A x) j| :=
            abs_matMulVec_le n A (matMulVec n ΔY (matMulVec n A x)) i
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, |ΔY j k| * |matMulVec n A x k|) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left
              (abs_matMulVec_le n ΔY (matMulVec n A x) j) (abs_nonneg _)
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, (gamma fp n * |Y j k|) *
              (∑ l : Fin n, |A k l| * |x l|)) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul
              (hΔY_bound j k)
              (abs_matMulVec_le n A x k)
              (abs_nonneg _)
              (mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _))
      _ = gamma fp n * S := by
            change
              ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, (gamma fp n * |Y j k|) *
                    (∑ l : Fin n, |A k l| * |x l|)) =
                gamma fp n * ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, |Y j k| *
                    (∑ l : Fin n, |A k l| * |x l|))
            calc
              ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, (gamma fp n * |Y j k|) *
                    (∑ l : Fin n, |A k l| * |x l|))
                  = ∑ j : Fin n, gamma fp n *
                      (|A i j| * ∑ k : Fin n, |Y j k| *
                        (∑ l : Fin n, |A k l| * |x l|)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    have hinner :
                        (∑ k : Fin n, (gamma fp n * |Y j k|) *
                          (∑ l : Fin n, |A k l| * |x l|)) =
                        gamma fp n * ∑ k : Fin n, |Y j k| *
                          (∑ l : Fin n, |A k l| * |x l|) := by
                      calc
                        ∑ k : Fin n, (gamma fp n * |Y j k|) *
                            (∑ l : Fin n, |A k l| * |x l|)
                            = ∑ k : Fin n, gamma fp n *
                              (|Y j k| * (∑ l : Fin n, |A k l| * |x l|)) := by
                              apply Finset.sum_congr rfl
                              intro k _
                              ring
                        _ = gamma fp n * ∑ k : Fin n, |Y j k| *
                              (∑ l : Fin n, |A k l| * |x l|) := by
                              rw [Finset.mul_sum]
                    rw [hinner]
                    ring
              _ = gamma fp n * ∑ j : Fin n, |A i j| *
                    (∑ k : Fin n, |Y j k| *
                      (∑ l : Fin n, |A k l| * |x l|)) := by
                    rw [Finset.mul_sum]
  have hfinal :
      |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
        matMulVec n A x i| ≤ gamma fp (n + 1) * S := by
    calc
      |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
          matMulVec n A x i|
          = |matMulVec n A (matMulVec n R x) i +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i| := by
            rw [hmain]
      _ ≤ |matMulVec n A (matMulVec n R x) i| +
            |matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i| :=
            abs_add_le _ _
      _ ≤ fp.u * S + gamma fp n * S :=
            add_le_add hres_part hround_part
      _ = (fp.u + gamma fp n) * S := by ring
      _ ≤ gamma fp (n + 1) * S :=
            mul_le_mul_of_nonneg_right hcoeff hS_nonneg
  change |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
      matMulVec n A x i| ≤ gamma fp (n + 1) * S
  exact hfinal

/-- Higham, 2nd ed., Chapter 14, Problem 14.5 support:
    expanding the left inverse residual gives `Y(Ax) = (YA-I)x + x`. -/
lemma higham14_inverseLeftResidual_mulVec_add_self (n : ℕ)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    matMulVec n Y (matMulVec n A x) =
      fun j => matMulVec n (inverseLeftResidual n A Y) x j + x j := by
  ext j
  rw [← matMulVec_matMul n Y A x j]
  simp only [inverseLeftResidual, matMulVec, matMul, idMatrix]
  have hdelta :
      (∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l) = x j := by
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  calc
    ∑ l : Fin n, (∑ k : Fin n, Y j k * A k l) * x l
        = ∑ l : Fin n,
            (((∑ k : Fin n, Y j k * A k l) -
              (if j = l then (1 : ℝ) else 0)) * x l +
              (if j = l then (1 : ℝ) else 0) * x l) := by
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ = (∑ l : Fin n,
            ((∑ k : Fin n, Y j k * A k l) -
              (if j = l then (1 : ℝ) else 0)) * x l) +
          ∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l := by
          rw [Finset.sum_add_distrib]
    _ = (∑ l : Fin n,
            ((∑ k : Fin n, Y j k * A k l) -
              (if j = l then (1 : ℝ) else 0)) * x l) + x j := by
          rw [hdelta]

/-- Higham, 2nd ed., Chapter 14, Problem 14.5 support:
    a componentwise residual envelope transfers to a componentwise forward-error
    envelope by left multiplication with `|A⁻¹|`. -/
theorem higham14_problem14_5_forward_error_of_residual_bound
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (x x_hat b Eres : Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hres : ∀ i : Fin n, |matMulVec n A x_hat i - b i| ≤ Eres i) :
    ∀ i : Fin n,
      |x_hat i - x i| ≤ matMulVec n (absMatrix n A_inv) Eres i := by
  let r : Fin n → ℝ := fun k => matMulVec n A x_hat k - b k
  let d : Fin n → ℝ := fun j => x_hat j - x j
  have hr : r = matMulVec n A d := by
    ext i
    dsimp [r, d]
    rw [← congrFun hsolve i]
    unfold matMulVec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmat : matMul n A_inv A = idMatrix n := by
    ext i j
    exact hLeft i j
  have hd : d = matMulVec n A_inv r := by
    rw [hr]
    ext i
    rw [← matMulVec_matMul n A_inv A d i]
    rw [hmat, matMulVec_id]
  intro i
  calc
    |x_hat i - x i| = |d i| := rfl
    _ = |matMulVec n A_inv r i| := by rw [hd]
    _ ≤ ∑ j : Fin n, |A_inv i j| * |r j| :=
        abs_matMulVec_le n A_inv r i
    _ ≤ ∑ j : Fin n, |A_inv i j| * Eres j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hres j) (abs_nonneg _)
    _ = matMulVec n (absMatrix n A_inv) Eres i := by
        simp [matMulVec, absMatrix]

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    forward-error consequence.

If `X` has a small right inverse residual and `A x = b`, then the residual
bound for `x_hat = fl(X b)` gives the componentwise forward-error envelope
`|x_hat-x| <= gamma_{n+1} |A⁻¹||A||X||b|`. -/
theorem higham14_problem14_5_right_inverse_solve_forward_error_bound
    (n : ℕ) (fp : FPModel)
    (A A_inv X : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |x_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n X) (absVec n b))) i := by
  intro x_hat i
  let E : Fin n → ℝ :=
    matMulVec n (absMatrix n A)
      (matMulVec n (absMatrix n X) (absVec n b))
  have hres0 :=
    higham14_problem14_5_right_inverse_solve_residual_bound
      n fp A X b hn1 hRightRes
  have hres : ∀ k : Fin n,
      |matMulVec n A x_hat k - b k| ≤ gamma fp (n + 1) * E k := by
    intro k
    simpa [x_hat, E] using hres0 k
  have hfwd :=
    higham14_problem14_5_forward_error_of_residual_bound
      n A A_inv x x_hat b (fun k => gamma fp (n + 1) * E k)
      hLeft hsolve hres
  calc
    |x_hat i - x i|
        ≤ matMulVec n (absMatrix n A_inv)
            (fun k => gamma fp (n + 1) * E k) i := hfwd i
    _ = gamma fp (n + 1) * matMulVec n (absMatrix n A_inv) E i := by
        simp only [matMulVec, absMatrix]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    forward-error consequence.

If `Y` has a small left inverse residual and `b = A x`, then
`y_hat = fl(Y b)` satisfies the componentwise forward-error envelope
`|y_hat-x| <= gamma_{n+1} |Y||A||x|`. -/
theorem higham14_problem14_5_left_inverse_solve_forward_error_bound
    (n : ℕ) (fp : FPModel)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |y_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n Y)
            (matMulVec n (absMatrix n A) (absVec n x)) i := by
  intro b y_hat i
  have hn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  obtain ⟨ΔY, hΔY_bound, hΔY_eq⟩ :=
    matVec_backward_error fp n n Y (matMulVec n A x) hn
  change |fl_matVec fp n n Y (matMulVec n A x) i - x i| ≤ _
  let R := inverseLeftResidual n A Y
  let S : ℝ :=
    matMulVec n (absMatrix n Y)
      (matMulVec n (absMatrix n A) (absVec n x)) i
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  have hS_nonneg : 0 ≤ S := by
    simp only [S, matMulVec, absMatrix, absVec]
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hyhat_vec :
      fl_matVec fp n n Y (matMulVec n A x) =
        matMulVec n (fun i j => Y i j + ΔY i j) (matMulVec n A x) := by
    ext j
    simpa [matMulVec] using hΔY_eq j
  have hYAx_split :
      matMulVec n Y (matMulVec n A x) =
        fun j => matMulVec n R x j + x j := by
    simpa [R] using higham14_inverseLeftResidual_mulVec_add_self n A Y x
  have hmain :
      fl_matVec fp n n Y (matMulVec n A x) i - x i =
        matMulVec n R x i +
          matMulVec n ΔY (matMulVec n A x) i := by
    calc
      fl_matVec fp n n Y (matMulVec n A x) i - x i
          = matMulVec n
              (fun j k => Y j k + ΔY j k) (matMulVec n A x) i - x i := by
                rw [hyhat_vec]
      _ = (matMulVec n Y (matMulVec n A x) i +
              matMulVec n ΔY (matMulVec n A x) i) - x i := by
                rw [matMulVec_add_left]
      _ = ((matMulVec n R x i + x i) +
              matMulVec n ΔY (matMulVec n A x) i) - x i := by
                rw [hYAx_split]
      _ = matMulVec n R x i +
            matMulVec n ΔY (matMulVec n A x) i := by
              ring
  have hres_part :
      |matMulVec n R x i| ≤ fp.u * S := by
    calc
      |matMulVec n R x i|
          ≤ ∑ k : Fin n, |R i k| * |x k| :=
            abs_matMulVec_le n R x i
      _ ≤ ∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y i l| * |A l k|) * |x k| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right
              (by simpa [R] using hLeftRes i k) (abs_nonneg _)
      _ = fp.u * S := by
            simp only [S, matMulVec, absMatrix, absVec]
            calc
              ∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y i l| * |A l k|) * |x k|
                  = ∑ k : Fin n, ∑ l : Fin n,
                      fp.u * (|Y i l| * |A l k|) * |x k| := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ l : Fin n, ∑ k : Fin n,
                      fp.u * (|Y i l| * |A l k|) * |x k| := by
                    rw [Finset.sum_comm]
              _ = fp.u * ∑ l : Fin n, |Y i l| *
                      (∑ k : Fin n, |A l k| * |x k|) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro l _
                    calc
                      ∑ k : Fin n, fp.u * (|Y i l| * |A l k|) * |x k|
                          = fp.u *
                              (∑ k : Fin n, |Y i l| * (|A l k| * |x k|)) := by
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro k _
                            ring
                      _ = fp.u * (|Y i l| *
                              (∑ k : Fin n, |A l k| * |x k|)) := by
                            congr 1
                            rw [← Finset.mul_sum]
  have hround_part :
      |matMulVec n ΔY (matMulVec n A x) i| ≤ gamma fp n * S := by
    calc
      |matMulVec n ΔY (matMulVec n A x) i|
          ≤ ∑ k : Fin n, |ΔY i k| * |matMulVec n A x k| :=
            abs_matMulVec_le n ΔY (matMulVec n A x) i
      _ ≤ ∑ k : Fin n, (gamma fp n * |Y i k|) *
            (∑ l : Fin n, |A k l| * |x l|) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul
              (hΔY_bound i k)
              (abs_matMulVec_le n A x k)
              (abs_nonneg _)
              (mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _))
      _ = gamma fp n * S := by
            change
              ∑ k : Fin n, (gamma fp n * |Y i k|) *
                  (∑ l : Fin n, |A k l| * |x l|) =
                gamma fp n * ∑ k : Fin n, |Y i k| *
                  (∑ l : Fin n, |A k l| * |x l|)
            calc
              ∑ k : Fin n, (gamma fp n * |Y i k|) *
                  (∑ l : Fin n, |A k l| * |x l|)
                  = ∑ k : Fin n, gamma fp n *
                      (|Y i k| * (∑ l : Fin n, |A k l| * |x l|)) := by
                    apply Finset.sum_congr rfl
                    intro k _
                    ring
              _ = gamma fp n * ∑ k : Fin n, |Y i k| *
                    (∑ l : Fin n, |A k l| * |x l|) := by
                    rw [Finset.mul_sum]
  have hfinal :
      |fl_matVec fp n n Y (matMulVec n A x) i - x i| ≤
        gamma fp (n + 1) * S := by
    calc
      |fl_matVec fp n n Y (matMulVec n A x) i - x i|
          = |matMulVec n R x i +
              matMulVec n ΔY (matMulVec n A x) i| := by
            rw [hmain]
      _ ≤ |matMulVec n R x i| +
            |matMulVec n ΔY (matMulVec n A x) i| :=
            abs_add_le _ _
      _ ≤ fp.u * S + gamma fp n * S :=
            add_le_add hres_part hround_part
      _ = (fp.u + gamma fp n) * S := by ring
      _ ≤ gamma fp (n + 1) * S :=
            mul_le_mul_of_nonneg_right hcoeff hS_nonneg
  change |fl_matVec fp n n Y (matMulVec n A x) i - x i| ≤
    gamma fp (n + 1) * S
  exact hfinal

/-- Monotonicity of multiplication by an absolute-value matrix. -/
lemma higham14_absMatrix_matMulVec_mono (n : ℕ)
    (A : Fin n → Fin n → ℝ) {x y : Fin n → ℝ}
    (hxy : ∀ i : Fin n, x i ≤ y i) :
    ∀ i : Fin n,
      matMulVec n (absMatrix n A) x i ≤
        matMulVec n (absMatrix n A) y i := by
  intro i
  simp only [matMulVec, absMatrix]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (abs_nonneg _)

/-- Nonnegativity of multiplication by an absolute-value matrix against a
    nonnegative vector. -/
lemma higham14_absMatrix_matMulVec_nonneg (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : ∀ i : Fin n, 0 ≤ x i) :
    ∀ i : Fin n, 0 ≤ matMulVec n (absMatrix n A) x i := by
  intro i
  simp only [matMulVec, absMatrix]
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (abs_nonneg _) (hx j))

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    forward-error bound with an externally supplied first-order replacement
    envelope for `|X|`. -/
theorem higham14_problem14_5_right_inverse_solve_forward_error_bound_of_abs_X_le
    (n : ℕ) (fp : FPModel)
    (A A_inv X : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|)
    (X_bound : Fin n → Fin n → ℝ)
    (hX_bound : ∀ i j : Fin n, |X i j| ≤ X_bound i j) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |x_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n X_bound (absVec n b))) i := by
  intro x_hat i
  have hbase :=
    higham14_problem14_5_right_inverse_solve_forward_error_bound
      n fp A A_inv X x b hn1 hLeft hsolve hRightRes
  have hX_mono : ∀ j : Fin n,
      matMulVec n (absMatrix n X) (absVec n b) j ≤
        matMulVec n X_bound (absVec n b) j := by
    intro j
    simp only [matMulVec, absMatrix, absVec]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hX_bound j k) (abs_nonneg _)
  have hA_mono :=
    higham14_absMatrix_matMulVec_mono n A hX_mono
  have hAinv_mono :=
    higham14_absMatrix_matMulVec_mono n A_inv hA_mono
  calc
    |x_hat i - x i|
        ≤ gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n X) (absVec n b))) i := hbase i
    _ ≤ gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n X_bound (absVec n b))) i :=
        mul_le_mul_of_nonneg_left (hAinv_mono i) (gamma_nonneg fp hn1)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    first-order replacement form: if `|X|` is bounded by `|A⁻¹|`, the forward
    envelope uses `|A⁻¹||A||A⁻¹||b|`. -/
theorem higham14_problem14_5_right_inverse_solve_forward_error_firstorder_replacement
    (n : ℕ) (fp : FPModel)
    (A A_inv X : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|)
    (hX_first : ∀ i j : Fin n, |X i j| ≤ |A_inv i j|) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |x_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n A_inv) (absVec n b))) i := by
  exact
    higham14_problem14_5_right_inverse_solve_forward_error_bound_of_abs_X_le
      n fp A A_inv X x b hn1 hLeft hsolve hRightRes
      (absMatrix n A_inv) (by
        intro i j
        simpa [absMatrix] using hX_first i j)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    forward-error bound with an externally supplied first-order replacement
    envelope for `|Y|`. -/
theorem higham14_problem14_5_left_inverse_solve_forward_error_bound_of_abs_Y_le
    (n : ℕ) (fp : FPModel)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|)
    (Y_bound : Fin n → Fin n → ℝ)
    (hY_bound : ∀ i j : Fin n, |Y i j| ≤ Y_bound i j) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |y_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n Y_bound
            (matMulVec n (absMatrix n A) (absVec n x)) i := by
  intro b y_hat i
  have hbase :=
    higham14_problem14_5_left_inverse_solve_forward_error_bound
      n fp A Y x hn1 hLeftRes
  have hAx_nonneg : ∀ k : Fin n,
      0 ≤ matMulVec n (absMatrix n A) (absVec n x) k :=
    higham14_absMatrix_matMulVec_nonneg n A (absVec n x)
      (fun k => abs_nonneg (x k))
  have hY_mono : ∀ j : Fin n,
      matMulVec n (absMatrix n Y)
          (matMulVec n (absMatrix n A) (absVec n x)) j ≤
        matMulVec n Y_bound
          (matMulVec n (absMatrix n A) (absVec n x)) j := by
    intro j
    simp only [matMulVec, absMatrix]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hY_bound j k) (hAx_nonneg k)
  calc
    |y_hat i - x i|
        ≤ gamma fp (n + 1) *
          matMulVec n (absMatrix n Y)
            (matMulVec n (absMatrix n A) (absVec n x)) i := hbase i
    _ ≤ gamma fp (n + 1) *
          matMulVec n Y_bound
            (matMulVec n (absMatrix n A) (absVec n x)) i :=
        mul_le_mul_of_nonneg_left (hY_mono i) (gamma_nonneg fp hn1)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    first-order replacement form: if `|Y|` is bounded by `|A⁻¹|`, the forward
    envelope uses `|A⁻¹||A||x|`. -/
theorem higham14_problem14_5_left_inverse_solve_forward_error_firstorder_replacement
    (n : ℕ) (fp : FPModel)
    (A A_inv Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|)
    (hY_first : ∀ i j : Fin n, |Y i j| ≤ |A_inv i j|) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |y_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A) (absVec n x)) i := by
  exact
    higham14_problem14_5_left_inverse_solve_forward_error_bound_of_abs_Y_le
      n fp A Y x hn1 hLeftRes (absMatrix n A_inv) (by
        intro i j
        simpa [absMatrix] using hY_first i j)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5 interpretation:
    with an exact right-hand side `b = A x`, the right first-order envelope
    applies one extra nonnegative `|A⁻¹||A|` amplification to the left
    first-order envelope.  Since `A⁻¹A = I`, the left envelope is
    componentwise bounded by that amplified envelope. -/
theorem higham14_problem14_5_left_firstorder_envelope_le_right_exact_rhs_envelope
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    ∀ i : Fin n,
      matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A) (absVec n x)) i ≤
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A) (absVec n x)))) i := by
  intro i
  let z : Fin n → ℝ :=
    matMulVec n (absMatrix n A_inv)
      (matMulVec n (absMatrix n A) (absVec n x))
  have hAx_nonneg : ∀ k : Fin n,
      0 ≤ matMulVec n (absMatrix n A) (absVec n x) k :=
    higham14_absMatrix_matMulVec_nonneg n A (absVec n x)
      (fun k => abs_nonneg (x k))
  have hz_nonneg : ∀ k : Fin n, 0 ≤ z k :=
    higham14_absMatrix_matMulVec_nonneg n A_inv
      (matMulVec n (absMatrix n A) (absVec n x)) hAx_nonneg
  have hdiag : 1 ≤ ∑ j : Fin n, |A_inv i j| * |A j i| := by
    have hsum_eq : (∑ j : Fin n, A_inv i j * A j i) = 1 := by
      simpa using hLeft i i
    calc
      1 = |∑ j : Fin n, A_inv i j * A j i| := by
            rw [hsum_eq, abs_one]
      _ ≤ ∑ j : Fin n, |A_inv i j * A j i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A_inv i j| * |A j i| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
  change z i ≤
    matMulVec n (absMatrix n A_inv) (matMulVec n (absMatrix n A) z) i
  calc
    z i = 1 * z i := by ring
    _ ≤ (∑ j : Fin n, |A_inv i j| * |A j i|) * z i :=
        mul_le_mul_of_nonneg_right hdiag (hz_nonneg i)
    _ = ∑ j : Fin n, (|A_inv i j| * |A j i|) * z i := by
        rw [Finset.sum_mul]
    _ ≤ ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k| * z k) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          (|A_inv i j| * |A j i|) * z i
              = |A_inv i j| * (|A j i| * z i) := by ring
          _ ≤ |A_inv i j| * (∑ k : Fin n, |A j k| * z k) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              exact Finset.single_le_sum
                (fun k _ => mul_nonneg (abs_nonneg _) (hz_nonneg k))
                (Finset.mem_univ i)
    _ = matMulVec n (absMatrix n A_inv) (matMulVec n (absMatrix n A) z) i := by
        simp [matMulVec, absMatrix]

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    Euclidean norm of row `i`, the quantity `||A(i,:)||₂` used in the
    determinant normalization defining the Hadamard condition number. -/
noncomputable def higham14_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  vecNorm2 (fun j : Fin n => A i j)

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    diagonal matrix whose diagonal entries are the row 2-norms of `A`. -/
noncomputable def higham14_rowNormDiagonal {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i : Fin n => higham14_rowNorm2 A i)

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    Hadamard determinant condition number `ψ(A)`, modeled in the positive
    form used by the subsequent Hadamard-inequality statement.  The printed
    display omits absolute-value bars on `det(A)`, while the condition-number
    interpretation requires `|det(A)|` in the denominator. -/
noncomputable def higham14_hadamardConditionNumber {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, higham14_rowNorm2 A i) /
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    signed raw version of the displayed ratio `det(D)/det(A)`.  Use
    `higham14_hadamardConditionNumber` for the nonnegative condition-number
    surface that matches the following Hadamard inequality discussion. -/
noncomputable def higham14_hadamardConditionNumberRaw {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, higham14_rowNorm2 A i) /
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)

lemma higham14_rowNorm2_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ higham14_rowNorm2 A i :=
  vecNorm2_nonneg _

/-- The row-norm diagonal has determinant equal to the product of the row
    2-norms, the numerator in Higham's `ψ(A)`. -/
theorem higham14_det_rowNormDiagonal_eq_prod_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    Matrix.det (higham14_rowNormDiagonal A) =
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  simp [higham14_rowNormDiagonal]

/-- Source-facing bridge from the diagonal determinant notation to the
    product-of-row-norms definition of `ψ(A)`. -/
theorem higham14_hadamardConditionNumber_eq_det_rowNormDiagonal_div_abs_det
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    higham14_hadamardConditionNumber A =
      Matrix.det (higham14_rowNormDiagonal A) /
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
  rw [higham14_det_rowNormDiagonal_eq_prod_rowNorm2]
  rfl

/-- When `det(A)` is positive, the raw displayed ratio agrees with the
    nonnegative Hadamard condition-number form. -/
theorem higham14_hadamardConditionNumberRaw_eq_conditionNumber_of_det_pos
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : 0 < Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) :
    higham14_hadamardConditionNumberRaw A =
      higham14_hadamardConditionNumber A := by
  simp [higham14_hadamardConditionNumberRaw,
    higham14_hadamardConditionNumber, abs_of_pos hdet]

theorem higham14_hadamardConditionNumber_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    0 ≤ higham14_hadamardConditionNumber A := by
  unfold higham14_hadamardConditionNumber
  exact div_nonneg
    (Finset.prod_nonneg fun i _ => higham14_rowNorm2_nonneg A i)
    (abs_nonneg _)

lemma higham14_rowNorm2_pos_of_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (i : Fin n) :
    0 < higham14_rowNorm2 A i := by
  have hne : higham14_rowNorm2 A i ≠ 0 := by
    intro hzero
    have hrow : ∀ j : Fin n, A i j = 0 :=
      (vecNorm2_eq_zero_iff (fun j : Fin n => A i j)).mp hzero
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hrow)
  exact lt_of_le_of_ne (higham14_rowNorm2_nonneg A i) (Ne.symm hne)

theorem higham14_hadamardConditionNumber_pos_of_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 < higham14_hadamardConditionNumber A := by
  unfold higham14_hadamardConditionNumber
  exact div_pos
    (Finset.prod_pos fun i _ => higham14_rowNorm2_pos_of_det_ne_zero A hdet i)
    (abs_pos.mpr hdet)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    Hadamard's determinant inequality in squared row-norm form.  This is a
    Chapter 14 source-facing wrapper around the Chapter 9 Gram determinant
    proof. -/
theorem higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 ≤
      ∏ i : Fin n, higham14_rowNorm2 A i ^ 2 := by
  simpa [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq] using
    (higham9_hadamard_det_sq_le_prod_row_sq
      (A := (A : Matrix (Fin n) (Fin n) ℝ)))

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    Hadamard's determinant inequality in the form
    `|det(A)| <= prod_i ||A(i,:)||_2`. -/
theorem higham14_problem14_11_abs_det_le_prod_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ≤
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  have hsquare :
      (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 ≤
        (∏ i : Fin n, higham14_rowNorm2 A i) ^ 2 := by
    rw [← Finset.prod_pow]
    exact higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq A
  exact abs_le_of_sq_le_sq hsquare
    (Finset.prod_nonneg fun i _ => higham14_rowNorm2_nonneg A i)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    nonsingular matrices have Hadamard determinant condition number at least
    one, in the nonnegative `|det(A)|` denominator convention. -/
theorem higham14_problem14_11_hadamardConditionNumber_ge_one_of_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    1 ≤ higham14_hadamardConditionNumber A := by
  have hden_pos : 0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| :=
    abs_pos.mpr hdet
  unfold higham14_hadamardConditionNumber
  exact (one_le_div hden_pos).mpr
    (higham14_problem14_11_abs_det_le_prod_rowNorm2 A)

/-- Higham, 2nd ed., Chapter 14, equation (14.34), exact no-pivot/unit-lower
    LU core: the determinant is the product of the diagonal entries of `U`. -/
theorem higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i := by
  simpa using hLU.det_eq_prod_U_diag

/-- Higham, 2nd ed., Chapter 14, equation (14.34), absolute-value no-pivot
    determinant product form.  The row-interchange parity factor in GEPP is
    absent here because the certificate is an exact `A = L * U` factorization. -/
theorem higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      |∏ i : Fin n, U i i| := by
  rw [higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLU]

/-- Higham, 2nd ed., Chapter 14, equation (14.34), direct signed pivoted
    determinant relation.  If the row permutation `σ` gives `PA = L * U`,
    then `sign(σ) * det(A)` is the product of the computed pivots. -/
theorem higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    (Equiv.Perm.sign (Equiv.ofBijective σ hLU.perm) : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i := by
  let Aσ : Fin n → Fin n → ℝ := fun i j => A (σ i) j
  have hLUσ : LUFactSpec n Aσ L U :=
    { L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by
        intro i j
        exact hLU.product_eq i j }
  have hdetσ :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        ∏ i : Fin n, U i i :=
    higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLUσ
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hAσ :
      (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.submatrix (A : Matrix (Fin n) (Fin n) ℝ)
          eSigma (Equiv.refl (Fin n)) := by
    ext i j
    change A (σ i) j = A ((Equiv.ofBijective σ hLU.perm) i) j
    rfl
  have hperm :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        (Equiv.Perm.sign eSigma : ℝ) *
          Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hAσ]
    simpa using
      (Matrix.det_permute (R := ℝ) eSigma
        (A : Matrix (Fin n) (Fin n) ℝ))
  change
    (Equiv.Perm.sign eSigma : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i
  rw [← hdetσ]
  exact hperm.symm

/-- Higham, 2nd ed., Chapter 14, equation (14.34), source-oriented signed
    pivoted determinant product.  Since a permutation sign is its own inverse,
    the direct `sign(σ) * det(A)` relation is equivalent to the displayed
    `det(A) = sign(σ) * ∏ᵢ uᵢᵢ` form. -/
theorem higham14_eq14_34_det_eq_perm_sign_mul_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      (Equiv.Perm.sign (Equiv.ofBijective σ hLU.perm) : ℝ) *
        ∏ i : Fin n, U i i := by
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hdirect :=
    higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec
      (A := A) (L := L) (U := U) (σ := σ) hLU
  change
    (Equiv.Perm.sign eSigma : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i at hdirect
  have hsq : (Equiv.Perm.sign eSigma : ℝ) *
      (Equiv.Perm.sign eSigma : ℝ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign eSigma) with hsign | hsign <;>
      simp [hsign]
  calc
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)
        = 1 * Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by ring
    _ = ((Equiv.Perm.sign eSigma : ℝ) * (Equiv.Perm.sign eSigma : ℝ)) *
          Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
          rw [hsq]
    _ = (Equiv.Perm.sign eSigma : ℝ) *
          ((Equiv.Perm.sign eSigma : ℝ) *
            Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) := by
          ring
    _ = (Equiv.Perm.sign eSigma : ℝ) * ∏ i : Fin n, U i i := by
          rw [hdirect]

/-- Higham, 2nd ed., Chapter 14, equation (14.34), pivoted absolute-value
    determinant product form.  A row permutation can change only the sign of
    the determinant, so a `PA = L * U` certificate gives the same absolute
    determinant product as the no-pivot core. -/
theorem higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      |∏ i : Fin n, U i i| := by
  let Aσ : Fin n → Fin n → ℝ := fun i j => A (σ i) j
  have hLUσ : LUFactSpec n Aσ L U :=
    { L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by
        intro i j
        exact hLU.product_eq i j }
  have hdetσ :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        ∏ i : Fin n, U i i :=
    higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLUσ
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hAσ :
      (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.submatrix (A : Matrix (Fin n) (Fin n) ℝ)
          eSigma (Equiv.refl (Fin n)) := by
    ext i j
    change A (σ i) j = A ((Equiv.ofBijective σ hLU.perm) i) j
    rfl
  have hAbs :
      |Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ)| =
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
    rw [hAσ]
    simpa using
      (Matrix.abs_det_submatrix_equiv_equiv (R := ℝ)
        eSigma (Equiv.refl (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ))
  rw [hdetσ] at hAbs
  exact hAbs.symm

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the row vector `hᵀ T⁻¹` in Hyman's method.  We model the
    source `(n-1)`-by-`(n-1)` block as an arbitrary `Fin n` block. -/
noncomputable def higham14_hymanRowTimesInv {n : ℕ}
    (h : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun j => ∑ k : Fin n, h k * Tinv k j

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the Schur scalar `η - hᵀ T⁻¹ y` appearing in (14.35)--(14.36). -/
noncomputable def higham14_hymanSchur {n : ℕ}
    (h y : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) : ℝ :=
  η - ∑ j : Fin n, higham14_hymanRowTimesInv h Tinv j * y j

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the cyclically permuted Hessenberg block matrix
    `H₁ = [[T, y], [hᵀ, η]]` used by Hyman's method. -/
noncomputable def higham14_hymanBlockMatrix {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks T (fun i (_ : Unit) => y i) (fun (_ : Unit) j => h j)
    (fun _ _ => η)

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    the lower block factor `[[I,0],[hᵀT⁻¹,1]]` in Hyman's LU factorization. -/
noncomputable def higham14_hymanLowerFactor {n : ℕ}
    (h : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 0 (fun (_ : Unit) j => higham14_hymanRowTimesInv h Tinv j)
    (1 : Matrix Unit Unit ℝ)

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    the upper block factor `[[T,y],[0,η-hᵀT⁻¹y]]` in Hyman's LU factorization. -/
noncomputable def higham14_hymanUpperFactor {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ)
    (Tinv : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks T (fun i (_ : Unit) => y i) 0
    (fun _ _ => higham14_hymanSchur h y Tinv η)

lemma higham14_hymanRowTimesInv_mul_T {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hTinv : IsLeftInverse n T Tinv) (j : Fin n) :
    ∑ x : Fin n, higham14_hymanRowTimesInv h Tinv x * T x j = h j := by
  calc
    ∑ x : Fin n, higham14_hymanRowTimesInv h Tinv x * T x j
        = ∑ x : Fin n, (∑ k : Fin n, h k * Tinv k x) * T x j := rfl
    _ = ∑ k : Fin n, h k * (∑ x : Fin n, Tinv k x * T x j) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = ∑ k : Fin n, h k * (if k = j then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hTinv k j]
    _ = h j := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    exact Hyman block LU factorization of the cyclically permuted Hessenberg
    block matrix, assuming the displayed inverse certificate `T⁻¹T = I`. -/
theorem higham14_eq14_35_hyman_block_lu_factorization {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (hTinv : IsLeftInverse n T Tinv) :
    higham14_hymanBlockMatrix T y h η =
      higham14_hymanLowerFactor h Tinv *
        higham14_hymanUpperFactor T y h Tinv η := by
  ext a b
  cases a <;> cases b
  · rename_i i j
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply, Matrix.one_apply]
  · rename_i i u
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply, Matrix.one_apply]
  · rename_i u j
    simpa [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply]
      using (higham14_hymanRowTimesInv_mul_T T Tinv h hTinv j).symm
  · rename_i u v
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, higham14_hymanSchur, Matrix.mul_apply]

/-- Higham, 2nd ed., Chapter 14, equation (14.36), printed p.280:
    determinant of the cyclically permuted Hyman block matrix is
    `det(T) * (η - hᵀT⁻¹y)`.  The separate cyclic-permutation sign converts
    this to the determinant of the original Hessenberg matrix. -/
theorem higham14_eq14_36_hyman_det_cyclic_block {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (hTinv : IsLeftInverse n T Tinv) :
    Matrix.det (higham14_hymanBlockMatrix T y h η) =
      Matrix.det T * higham14_hymanSchur h y Tinv η := by
  rw [higham14_eq14_35_hyman_block_lu_factorization T Tinv y h η hTinv]
  rw [Matrix.det_mul]
  have hdetL : Matrix.det (higham14_hymanLowerFactor h Tinv) = 1 := by
    rw [higham14_hymanLowerFactor, Matrix.det_fromBlocks_zero₁₂]
    simp
  have hdetU : Matrix.det (higham14_hymanUpperFactor T y h Tinv η) =
      Matrix.det T * higham14_hymanSchur h y Tinv η := by
    rw [higham14_hymanUpperFactor, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [hdetL, hdetU]
  ring

/-- Higham, 2nd ed., Chapter 14, equation (14.36), printed p.280:
    signed determinant formula for an original Hessenberg matrix whose row
    permutation is the cyclic Hyman block matrix.  For the source's cyclic
    permutation, the sign is the printed `(-1)^(n-1)` factor. -/
theorem higham14_eq14_36_hyman_det_original_of_row_permutation {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T Tinv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η : ℝ) (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hH :
      higham14_hymanBlockMatrix T y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTinv : IsLeftInverse n T Tinv) :
    Matrix.det H =
      (Equiv.Perm.sign σ : ℝ) *
        Matrix.det T * higham14_hymanSchur h y Tinv η := by
  have hperm_det :
      Matrix.det (higham14_hymanBlockMatrix T y h η) =
        (Equiv.Perm.sign σ : ℝ) * Matrix.det H := by
    rw [hH]
    simpa using
      (Matrix.det_permute (R := ℝ) σ H)
  have hcyclic :=
    higham14_eq14_36_hyman_det_cyclic_block
      T Tinv y h η hTinv
  have hdirect :
      (Equiv.Perm.sign σ : ℝ) * Matrix.det H =
        Matrix.det T * higham14_hymanSchur h y Tinv η := by
    rw [← hperm_det, hcyclic]
  have hsq : (Equiv.Perm.sign σ : ℝ) *
      (Equiv.Perm.sign σ : ℝ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  calc
    Matrix.det H = 1 * Matrix.det H := by ring
    _ = ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ)) *
          Matrix.det H := by
          rw [hsq]
    _ = (Equiv.Perm.sign σ : ℝ) *
          ((Equiv.Perm.sign σ : ℝ) * Matrix.det H) := by
          ring
    _ = (Equiv.Perm.sign σ : ℝ) *
          (Matrix.det T * higham14_hymanSchur h y Tinv η) := by
          rw [hdirect]
    _ = (Equiv.Perm.sign σ : ℝ) *
          Matrix.det T * higham14_hymanSchur h y Tinv η := by
          ring

/-- Entry perturbation used in Higham Chapter 14, Problem 14.10:
    replace `aᵢⱼ` by `aᵢⱼ + t`, leaving every other entry unchanged. -/
noncomputable def matrixEntryPerturb (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.updateRow (A : Matrix (Fin n) (Fin n) ℝ) i
    ((A : Matrix (Fin n) (Fin n) ℝ) i +
      t • (Pi.single j (1 : ℝ) : Fin n → ℝ))

/-- Higham, 2nd ed., Chapter 14, Problem 14.10, cofactor form:
    changing entry `aᵢⱼ` by `t` changes the determinant by
    `t * adj(A)ⱼᵢ`. -/
theorem higham14_problem14_10_det_entry_perturb_eq
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    Matrix.det (matrixEntryPerturb n A i j t) =
      Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) +
        t * Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i := by
  unfold matrixEntryPerturb
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, Matrix.adjugate_apply]

/-- Higham, 2nd ed., Chapter 14, Problem 14.10:
    if the `(j,i)` cofactor/adjugate entry vanishes, then `det(A)` is
    independent of the entry `aᵢⱼ`. -/
theorem higham14_problem14_10_det_entry_independent_of_adjugate_eq_zero
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n)
    (hAdj : Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i = 0) :
    ∀ t : ℝ,
      Matrix.det (matrixEntryPerturb n A i j t) =
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
  intro t
  rw [higham14_problem14_10_det_entry_perturb_eq n A i j t, hAdj, mul_zero, add_zero]

/-- Higham, 2nd ed., Chapter 14, Problem 14.10:
    the determinant is independent of `aᵢⱼ` for all additive perturbations iff
    the `(j,i)` adjugate entry is zero. -/
theorem higham14_problem14_10_det_entry_independent_iff_adjugate_eq_zero
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∀ t : ℝ,
      Matrix.det (matrixEntryPerturb n A i j t) =
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ↔
      Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [higham14_problem14_10_det_entry_perturb_eq n A i j 1] at h1
    linarith
  · exact higham14_problem14_10_det_entry_independent_of_adjugate_eq_zero n A i j

/-- Higham, 2nd ed., Chapter 14, Problem 14.7:
    if one row of a nonsingular matrix consists entirely of ones, then the
    entries of its inverse sum to one. -/
theorem higham14_problem14_7_inverse_entries_sum_eq_one_of_row_ones (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv)
    (i : Fin n)
    (hrow : ∀ k : Fin n, A i k = 1) :
    (∑ j : Fin n, ∑ k : Fin n, A_inv k j) = 1 := by
  have hColSum : ∀ j : Fin n,
      (∑ k : Fin n, A_inv k j) = if i = j then (1 : ℝ) else 0 := by
    intro j
    have h := hRight i j
    simpa [hrow] using h
  calc
    (∑ j : Fin n, ∑ k : Fin n, A_inv k j)
        = ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hColSum j
    _ = 1 := by
          simp [Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 14, Problem 14.7:
    if one column of a nonsingular matrix consists entirely of ones, then the
    entries of its inverse sum to one. -/
theorem higham14_problem14_7_inverse_entries_sum_eq_one_of_col_ones (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (j : Fin n)
    (hcol : ∀ k : Fin n, A k j = 1) :
    (∑ i : Fin n, ∑ k : Fin n, A_inv i k) = 1 := by
  have hRowSum : ∀ i : Fin n,
      (∑ k : Fin n, A_inv i k) = if i = j then (1 : ℝ) else 0 := by
    intro i
    have h := hLeft i j
    simpa [hcol] using h
  calc
    (∑ i : Fin n, ∑ k : Fin n, A_inv i k)
        = ∑ i : Fin n, (if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hRowSum i
    _ = 1 := by
          simp [Finset.mem_univ]

end LeanFpAnalysis.FP
