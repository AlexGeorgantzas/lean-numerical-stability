-- Algorithms/StationaryIteration.lean
--
-- Higham Chapter 16: Error analysis of stationary iterative methods.
--
-- Covers §16.2 (forward error analysis) and §16.3 (backward/residual error
-- analysis) for iterations of the form  Mx_{k+1} = Nx_k + b  where A = M − N.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §16.2  Splitting specification and iteration matrices
-- ============================================================

/-- A splitting A = M − N with M invertible. -/
structure SplittingSpec (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ) : Prop where
  splitting : ∀ i j, A i j = M i j - N i j
  inv_left : IsLeftInverse n M M_inv
  inv_right : IsRightInverse n M M_inv

/-- Iteration matrix G = M⁻¹N. -/
noncomputable def iterMatrix (n : ℕ) (M_inv N : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := matMul n M_inv N

/-- Dual iteration matrix H = NM⁻¹. -/
noncomputable def dualIterMatrix (n : ℕ) (N M_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := matMul n N M_inv

-- ============================================================
-- AG = HA identity
-- ============================================================

/-- **AG = HA**: Since A = M − N, both sides equal N − NM⁻¹N. -/
theorem AG_eq_HA (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) :
    matMul n A (iterMatrix n M_inv N) =
    matMul n (dualIterMatrix n N M_inv) A := by
  ext i j
  show ∑ k : Fin n, A i k * (∑ l : Fin n, M_inv k l * N l j) =
       ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * A k j
  -- Expand A = M - N on both sides
  simp_rw [hS.splitting]
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  -- Show first terms both = N_{ij}
  have h1 : ∑ k : Fin n, M i k * ∑ l : Fin n, M_inv k l * N l j = N i j := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    simp_rw [show ∀ x x_1 : Fin n, M i x_1 * (M_inv x_1 x * N x j) =
        M i x_1 * M_inv x_1 x * N x j from fun _ _ => by ring]
    simp_rw [← Finset.sum_mul]
    conv_lhs => arg 2; ext l; rw [hS.inv_right i l]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have h2 : ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * M k j = N i j := by
    simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    simp_rw [show ∀ x x_1 : Fin n, N i x * M_inv x x_1 * M x_1 j =
        N i x * (M_inv x x_1 * M x_1 j) from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum]
    conv_lhs => arg 2; ext l; rw [hS.inv_left l j]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  -- Show second terms match: ∑ N*(M⁻¹N) = ∑ (NM⁻¹)*N
  have h3 : ∑ k : Fin n, N i k * ∑ l : Fin n, M_inv k l * N l j =
      ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * N k j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    simp_rw [show ∀ k l : Fin n, N i k * (M_inv k l * N l j) =
        N i k * M_inv k l * N l j from fun _ _ => by ring]
    rw [Finset.sum_comm]
  linarith

/-- **AG^k = H^kA** for all k, by induction. -/
theorem A_matPow_G_eq_matPow_H_A (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) (k : ℕ) :
    matMul n A (matPow n (iterMatrix n M_inv N) k) =
    matMul n (matPow n (dualIterMatrix n N M_inv) k) A := by
  induction k with
  | zero =>
    simp only [matPow]; rw [matMul_id_right, matMul_id_left]
  | succ k ih =>
    show matMul n A (matMul n (iterMatrix n M_inv N)
      (matPow n (iterMatrix n M_inv N) k)) =
      matMul n (matMul n (dualIterMatrix n N M_inv)
      (matPow n (dualIterMatrix n N M_inv) k)) A
    rw [← matMul_assoc n A, AG_eq_HA n A M N M_inv hS,
        matMul_assoc n _ A, ih, ← matMul_assoc]

-- ============================================================
-- §16.2  Computed iteration and one-step error
-- ============================================================

/-- Computed stationary iteration with local errors (eq 16.1). -/
structure ComputedIteration (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ)) : Prop where
  step : ∀ k i, ∑ j : Fin n, M i j * x_hat (k + 1) j =
         ∑ j : Fin n, N i j * x_hat k j + b i + ξ k i

/-- One-step error: x_i − x̂_{k+1,i} = ∑_j G_{ij}(x_j − x̂_{k,j}) − ∑_j M⁻¹_{ij} ξ_{k,j}. -/
theorem one_step_error (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) :
    ∀ k i, x i - x_hat (k + 1) i =
      ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) -
      ∑ j : Fin n, M_inv i j * ξ k j := by
  intro k i
  have hstep := hIter.step k
  -- Mx = Nx + b
  have hMx : ∀ l, ∑ j : Fin n, M l j * x j =
      ∑ j : Fin n, N l j * x j + b l := by
    intro l
    have : ∑ j : Fin n, M l j * x j - ∑ j : Fin n, N l j * x j = b l := by
      rw [← Finset.sum_sub_distrib]
      convert hAx l using 1; congr 1; ext j; rw [hS.splitting l j]; ring
    linarith
  -- M(x - x̂_{k+1})_l = N(x - x̂_k)_l - ξ_{k,l}
  have hMdiff : ∀ l, ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) =
      ∑ j : Fin n, N l j * (x j - x_hat k j) - ξ k l := by
    intro l
    have h1 : ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) =
        ∑ j, M l j * x j - ∑ j, M l j * x_hat (k + 1) j := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    have h2 : ∑ j : Fin n, N l j * (x j - x_hat k j) =
        ∑ j, N l j * x j - ∑ j, N l j * x_hat k j := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    rw [h1, h2]; linarith [hstep l, hMx l]
  -- Apply M⁻¹
  have h_start : x i - x_hat (k + 1) i =
      ∑ l : Fin n, M_inv i l * ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) := by
    symm
    calc ∑ l : Fin n, M_inv i l * ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j)
        = ∑ j : Fin n, (∑ l : Fin n, M_inv i l * M l j) *
            (x j - x_hat (k + 1) j) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          congr 1; ext j; congr 1; ext l; ring
      _ = ∑ j : Fin n, (if i = j then 1 else 0) * (x j - x_hat (k + 1) j) := by
          congr 1; ext j; congr 1; exact hS.inv_left i j
      _ = x i - x_hat (k + 1) i := by
          simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [h_start]
  -- Replace M·diff with N·diff - ξ
  conv_lhs => arg 2; ext l; rw [hMdiff l]
  -- LHS: ∑_l M⁻¹_{il} * (∑_j N_{lj} (x_j - x̂_{k,j}) - ξ_{k,l})
  -- RHS: ∑_j G_{ij}(x_j-x̂_{k,j}) - ∑_j M⁻¹_{ij}ξ_{k,j}
  -- Both sides equal ∑_l ∑_j M⁻¹_{il}N_{lj}d_j - ∑_l M⁻¹_{il}ξ_l
  -- Transform LHS
  simp_rw [show ∀ l : Fin n, M_inv i l *
      (∑ j : Fin n, N l j * (x j - x_hat k j) - ξ k l) =
      ∑ j : Fin n, M_inv i l * (N l j * (x j - x_hat k j)) -
      M_inv i l * ξ k l from fun l => by rw [mul_sub, Finset.mul_sum]]
  rw [Finset.sum_sub_distrib]
  congr 1
  -- ∑_l ∑_j M⁻¹_{il}*(N_{lj}*d_j) = ∑_j G_{ij}*d_j
  rw [Finset.sum_comm]
  congr 1; ext j
  simp_rw [show ∀ l : Fin n, M_inv i l * (N l j * (x j - x_hat k j)) =
      M_inv i l * N l j * (x j - x_hat k j) from fun l => by ring]
  rw [← Finset.sum_mul]; rfl

-- ============================================================
-- §16.2  Componentwise forward bound (eq 16.6)
-- ============================================================

/-- **Eq. 16.6 (Componentwise forward bound)**: triangle inequality bound on
    |∑_j G^{m+1}_{ij} e_{0,j} + ∑_{k=0}^m ∑_j G^k_{ij} w_{m-k,j}|. -/
theorem componentwise_forward_bound (n : ℕ)
    (G : Fin n → Fin n → ℝ) (e₀ : Fin n → ℝ) (m : ℕ)
    (w : ℕ → (Fin n → ℝ)) (μ : ℕ → (Fin n → ℝ))
    (hw : ∀ k i, |w k i| ≤ μ k i)
    (_hμ : ∀ k i, 0 ≤ μ k i) :
    ∀ i, |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j +
      ∑ k ∈ Finset.range (m + 1),
        ∑ j : Fin n, matPow n G k i j * w (m - k) j| ≤
      ∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j| +
      ∑ k ∈ Finset.range (m + 1),
        ∑ j : Fin n, |matPow n G k i j| * μ (m - k) j := by
  intro i
  calc |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, matPow n G k i j * w (m - k) j|
      ≤ |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j| +
        |∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, matPow n G k i j * w (m - k) j| := abs_add_le _ _
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j * e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          |∑ j : Fin n, matPow n G k i j * w (m - k) j| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ (Finset.univ : Finset (Fin n)))
          (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, |matPow n G k i j * w (m - k) j| := by
        gcongr with j _
        · exact le_of_eq (abs_mul _ _)
        · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, |matPow n G k i j| * μ (m - k) j := by
        gcongr with k _ j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hw _ _) (abs_nonneg _)

-- ============================================================
-- §16.2  Local error bound and simplification (eqs 16.2, 16.10)
-- ============================================================

/-- Eq. 16.2: local rounding error bound. -/
def LocalErrorBound (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ))
    (ξ : ℕ → (Fin n → ℝ)) (cn_u : ℝ) : Prop :=
  ∀ k i, |ξ k i| ≤ cn_u * (∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
                              ∑ j : Fin n, |N i j| * |x_hat k j| + |b i|)

/-- **Eq. 16.10**: |ξ_k,i| ≤ c_n u(1+θ_x) ∑_j (|M_{ij}|+|N_{ij}|)|x_j|. -/
theorem local_error_simplified (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (_hθ : 0 ≤ θ_x)
    (hx_bound : ∀ k i, |x_hat k i| ≤ θ_x * |x i|)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u) :
    ∀ k i, |ξ k i| ≤ cn_u * (1 + θ_x) *
      ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
  intro k i
  have hL := hLocal k i
  have hb : |b i| ≤ ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
    calc |b i| = |∑ j, (M i j - N i j) * x j| := by rw [hAx]
      _ ≤ ∑ j, |(M i j - N i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |M i j - N i j| * |x j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, (|M i j| + |N i j|) * |x j| := by
          gcongr with j _
          calc |M i j - N i j| = |M i j + (-(N i j))| := by ring_nf
            _ ≤ |M i j| + |-(N i j)| := abs_add_le _ _
            _ = |M i j| + |N i j| := by rw [abs_neg]
  have hM_bound : ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| ≤
      θ_x * ∑ j : Fin n, |M i j| * |x j| :=
    calc ∑ j, |M i j| * |x_hat (k + 1) j|
        ≤ ∑ j, |M i j| * (θ_x * |x j|) := by
          gcongr with j _; exact hx_bound _ _
      _ = θ_x * ∑ j, |M i j| * |x j| := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
  have hN_bound : ∑ j : Fin n, |N i j| * |x_hat k j| ≤
      θ_x * ∑ j : Fin n, |N i j| * |x j| :=
    calc ∑ j, |N i j| * |x_hat k j|
        ≤ ∑ j, |N i j| * (θ_x * |x j|) := by
          gcongr with j _; exact hx_bound _ _
      _ = θ_x * ∑ j, |N i j| * |x j| := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
  have hSum : ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
      ∑ j : Fin n, |N i j| * |x_hat k j| + |b i| ≤
      (1 + θ_x) * ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
    have split_sum : ∑ j : Fin n, (|M i j| + |N i j|) * |x j| =
        ∑ j : Fin n, |M i j| * |x j| + ∑ j : Fin n, |N i j| * |x j| := by
      rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
    rw [split_sum]; nlinarith
  calc |ξ k i|
      ≤ cn_u * (∑ j, |M i j| * |x_hat (k + 1) j| +
                ∑ j, |N i j| * |x_hat k j| + |b i|) := hL
    _ ≤ cn_u * ((1 + θ_x) * ∑ j, (|M i j| + |N i j|) * |x j|) := by
        apply mul_le_mul_of_nonneg_left hSum hcn
    _ = cn_u * (1 + θ_x) * ∑ j, (|M i j| + |N i j|) * |x j| := by ring

-- ============================================================
-- §16.2  c(A) constant and main bound (eqs 16.12–16.13)
-- ============================================================

/-- Partial sum bound (eq 16.12): ∑_{k=0}^m |G^k M⁻¹|_{ij} ≤ cA · |A⁻¹_{ij}|. -/
def PartialSumBound (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (cA : ℝ) (m : ℕ) : Prop :=
  ∀ i j, ∑ k ∈ Finset.range (m + 1),
    ∑ l : Fin n, |matPow n G k i l| * |M_inv l j| ≤ cA * |A_inv i j|

-- ============================================================
-- §16.2.1  Jacobi specialization
-- ============================================================

/-- **Eq. 16.16 (Jacobi)**: |M| + |N| = |A| for M = diag(A), N = diag(A) − A. -/
theorem jacobi_splitting_abs (n : ℕ) (A : Fin n → Fin n → ℝ)
    (M N : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M i j = if i = j then A i i else 0)
    (hN : ∀ i j, N i j = M i j - A i j) :
    ∀ i j, |M i j| + |N i j| = |A i j| := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hM i i, if_pos rfl, hN i i, hM i i, if_pos rfl, sub_self, abs_zero, add_zero]
  · rw [hM i j, if_neg hij, hN i j, hM i j, if_neg hij, zero_sub, abs_zero, zero_add, abs_neg]

-- ============================================================
-- §16.2.2  SOR specialization
-- ============================================================

/-- **Eq. 16.17 (SOR)**: |M| + |N| ≤ f(ω)|A| where f(ω) = (1+|1−ω|)/ω. -/
theorem sor_splitting_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (ω : ℝ) (hω_pos : 0 < ω)
    (D L U : Fin n → Fin n → ℝ)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (M_sor N_sor : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j)) :
    ∀ i j, |M_sor i j| + |N_sor i j| ≤ ((1 + |1 - ω|) / ω) * |A i j| := by
  have hω_ne : ω ≠ 0 := ne_of_gt hω_pos
  have hfω : 1 ≤ (1 + |1 - ω|) / ω := by
    rw [le_div_iff₀ hω_pos]
    by_cases h : ω ≤ 1
    · have : |1 - ω| = 1 - ω := abs_of_nonneg (by linarith)
      nlinarith
    · push_neg at h
      have h1 : (1 : ℝ) - ω < 0 := by linarith
      have : |1 - ω| = -(1 - ω) := abs_of_neg h1
      linarith
  intro i j
  by_cases hij : i = j
  · -- Diagonal case: L_{ii} = U_{ii} = 0
    have hLii := hL i i (le_refl _)
    have hUii := hU i i (le_refl _)
    have hAii : A i i = D i i := by
      have := hDecomp i i; rw [hLii, hUii] at this; linarith
    subst hij
    have hMval : M_sor i i = D i i / ω := by
      rw [hM, hLii, mul_zero, add_zero]; field_simp
    have hNval : N_sor i i = (1 - ω) * D i i / ω := by
      rw [hN, hUii, mul_zero, sub_zero]; field_simp
    rw [hMval, hNval, ← hAii]
    rw [abs_div, abs_div, abs_mul, ← add_div, abs_of_pos hω_pos, div_mul_eq_mul_div]
    ring_nf; rfl
  · -- Off-diagonal: D_{ij} = 0
    have hDij := hD i j hij
    have hMval : M_sor i j = L i j := by
      rw [hM, hDij, zero_add]; field_simp
    have hNval : N_sor i j = -(U i j) := by
      rw [hN, hDij, mul_zero, zero_sub]; field_simp
    rw [hMval, hNval, abs_neg]
    have hAij : A i j = L i j + U i j := by
      have := hDecomp i j; rw [hDij] at this; linarith
    by_cases hlj : j.val < i.val
    · have hUij := hU i j (le_of_lt hlj)
      rw [hUij, abs_zero, add_zero, hAij, hUij, add_zero]
      exact le_mul_of_one_le_left (abs_nonneg _) hfω
    · push_neg at hlj
      have hji : i.val < j.val := by
        rcases hlj.eq_or_lt with heq | hlt
        · exact absurd (Fin.ext heq.symm) (Ne.symm hij)
        · exact hlt
      have hLij := hL i j (le_of_lt hji)
      rw [hLij, abs_zero, zero_add, hAij, hLij, zero_add]
      exact le_mul_of_one_le_left (abs_nonneg _) hfω

-- ============================================================
-- §16.3  Backward error — residual identity and sigma bound
-- ============================================================

/-- The residual r_k = b − Ax̂_k equals A(x − x̂_k). -/
theorem residual_eq_A_error (n : ℕ) (A : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : Fin n → ℝ) :
    ∀ i, b i - ∑ j : Fin n, A i j * x_hat j =
      ∑ j : Fin n, A i j * (x j - x_hat j) := by
  intro i
  rw [← hAx i, ← Finset.sum_sub_distrib]
  congr 1; ext j; ring

/-- Geometric series partial sum bound: ∑_{k=0}^m q^k ≤ 1/(1-q) for 0 ≤ q < 1. -/
private theorem geom_partial_sum_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), q ^ k ≤ 1 / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  rw [le_div_iff₀ hq1']
  calc (∑ k ∈ Finset.range (m + 1), q ^ k) * (1 - q)
      = ∑ k ∈ Finset.range (m + 1), (q ^ k - q ^ (k + 1)) := by
        rw [Finset.sum_mul]; congr 1; ext k; ring
    _ = 1 - q ^ (m + 1) := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ]; linarith
    _ ≤ 1 := by linarith [pow_nonneg hq (m + 1)]

/-- **σ bound** (§16.3): ∑_{k=0}^m ‖H^k(I−H)‖∞ ≤ ‖I−H‖∞/(1−q) when ‖H‖∞ ≤ q < 1. -/
theorem sigma_bound (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm hn H ≤ q) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      infNorm hn (matMul n (matPow n H k) (matSub_id n H)) ≤
    infNorm hn (matSub_id n H) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  calc ∑ k ∈ Finset.range (m + 1),
        infNorm hn (matMul n (matPow n H k) (matSub_id n H))
      ≤ ∑ k ∈ Finset.range (m + 1),
        (q ^ k * infNorm hn (matSub_id n H)) := by
        gcongr with k _
        calc infNorm hn (matMul n (matPow n H k) (matSub_id n H))
            ≤ infNorm hn (matPow n H k) * infNorm hn (matSub_id n H) :=
              infNorm_matMul_le hn _ _
          _ ≤ q ^ k * infNorm hn (matSub_id n H) := by
              apply mul_le_mul_of_nonneg_right _ (infNorm_nonneg hn _)
              exact (infNorm_matPow_le hn H k).trans (pow_le_pow_left₀ (infNorm_nonneg hn H) hH k)
    _ = (∑ k ∈ Finset.range (m + 1), q ^ k) * infNorm hn (matSub_id n H) := by
        rw [Finset.sum_mul]
    _ ≤ (1 / (1 - q)) * infNorm hn (matSub_id n H) := by
        apply mul_le_mul_of_nonneg_right (geom_partial_sum_le q hq hq1 m) (infNorm_nonneg hn _)
    _ = infNorm hn (matSub_id n H) / (1 - q) := by
        rw [one_div, mul_comm, div_eq_mul_inv]

-- ============================================================
-- §16.3  Residual recurrence: r_{k+1} = Hr_k − (I−H)ξ_k
-- ============================================================

/-- AM⁻¹ = I − H: since A = M − N, AM⁻¹ = MM⁻¹ − NM⁻¹ = I − H. -/
theorem A_matMul_Minv_eq_sub (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) :
    matMul n A M_inv = matSub_id n (dualIterMatrix n N M_inv) := by
  ext i j
  show ∑ k, A i k * M_inv k j = idMatrix n i j - ∑ k, N i k * M_inv k j
  simp_rw [hS.splitting, sub_mul, Finset.sum_sub_distrib]
  have hMM := hS.inv_right i j; unfold idMatrix at *; linarith

/-- **One-step residual recurrence** (eq 16.18 base case): r_{k+1} = Hr_k − (I−H)ξ_k.
    Obtained by left-multiplying e_{k+1} = Ge_k − M⁻¹ξ_k by A
    and using AG = HA, AM⁻¹ = I − H. -/
theorem one_step_residual (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) :
    ∀ k i, (b i - ∑ j, A i j * x_hat (k + 1) j) =
      matMulVec n (dualIterMatrix n N M_inv)
        (fun j => b j - ∑ l, A j l * x_hat k l) i -
      matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i := by
  intro k i
  -- r_{k+1,i} = ∑_j A_{ij}(x_j − x̂_{k+1,j})
  rw [residual_eq_A_error n A b x hAx (x_hat (k + 1)) i]
  -- Substitute one_step_error
  have hstep := one_step_error n A M N M_inv hS b x hAx x_hat ξ hIter k
  conv_lhs => arg 2; ext j; rw [hstep j, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- A·(G·e_k) = H·r_k  via  A(Gd) = (AG)d = (HA)d = H(Ad) = H·r_k
    show matMulVec n A (matMulVec n (iterMatrix n M_inv N)
        (fun l => x l - x_hat k l)) i =
      matMulVec n (dualIterMatrix n N M_inv)
        (fun j => b j - ∑ l, A j l * x_hat k l) i
    rw [← matMulVec_matMul, AG_eq_HA n A M N M_inv hS, matMulVec_matMul]
    suffices h : matMulVec n A (fun l => x l - x_hat k l) =
        fun j => b j - ∑ l, A j l * x_hat k l by rw [h]
    ext j; exact (residual_eq_A_error n A b x hAx (x_hat k) j).symm
  · -- A·(M⁻¹·ξ_k) = (I−H)·ξ_k  via  AM⁻¹ = I − H
    show matMulVec n A (matMulVec n M_inv (ξ k)) i =
      matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i
    rw [← matMulVec_matMul, A_matMul_Minv_eq_sub n A M N M_inv hS]

-- ============================================================
-- §16.2  Normwise one-step bound and forward bound (eqs 16.5, 16.8)
-- ============================================================

/-- ‖Av‖∞ ≤ ‖A‖∞ · ‖v‖∞: submultiplicativity for matrix-vector product. -/
theorem infNormVec_matMulVec_le {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    infNormVec hn (matMulVec n A v) ≤ infNorm hn A * infNormVec hn v := by
  unfold infNormVec matMulVec
  apply Finset.sup'_le; intro i _
  calc |∑ j : Fin n, A i j * v j|
      ≤ ∑ j : Fin n, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |v j| := by congr 1; ext j; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A i j| * Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => |v i|) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun i => |v i|) (Finset.mem_univ j)) (abs_nonneg _)
    _ = (∑ j : Fin n, |A i j|) * Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => |v i|) := by
        rw [Finset.sum_mul]
    _ ≤ infNorm hn A * Finset.sup' Finset.univ
          (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => |v i|) := by
        apply mul_le_mul_of_nonneg_right (row_sum_le_infNorm hn A i)
        apply Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, hn⟩)
        exact abs_nonneg _

/-- Normwise one-step error bound from `one_step_error`:
    ‖e_{k+1}‖∞ ≤ ‖G‖∞·‖e_k‖∞ + ‖M⁻¹‖∞·‖ξ_k‖∞. -/
theorem normwise_one_step_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) (k : ℕ) :
    infNormVec hn (fun i => x i - x_hat (k + 1) i) ≤
      infNorm hn (iterMatrix n M_inv N) *
        infNormVec hn (fun i => x i - x_hat k i) +
      infNorm hn M_inv * infNormVec hn (ξ k) := by
  have hstep := one_step_error n A M N M_inv hS b x hAx x_hat ξ hIter k
  -- Suffices to show for each component i
  suffices h : ∀ i : Fin n, |x i - x_hat (k + 1) i| ≤
      infNorm hn (iterMatrix n M_inv N) *
        infNormVec hn (fun i => x i - x_hat k i) +
      infNorm hn M_inv * infNormVec hn (ξ k) by
    unfold infNormVec; apply Finset.sup'_le; intro i _; exact h i
  intro i; rw [hstep i]
  -- |∑ G_{ij}(x_j - x̂_{k,j}) - ∑ M⁻¹_{ij}ξ_{k,j}| ≤ ‖G‖·‖e_k‖ + ‖M⁻¹‖·‖ξ_k‖
  -- Step 1: triangle inequality
  set a := ∑ j, iterMatrix n M_inv N i j * (x j - x_hat k j) with ha_def
  set b := ∑ j, M_inv i j * ξ k j with hb_def
  have htri : |a - b| ≤ |a| + |b| :=
    (abs_add_le a (-b)).trans (by rw [abs_neg])
  -- Step 2: bound each absolute sum
  have ha_bound : |a| ≤ ∑ j, |iterMatrix n M_inv N i j| * |x j - x_hat k j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => le_of_eq (abs_mul _ _)))
  have hb_bound : |b| ≤ ∑ j, |M_inv i j| * |ξ k j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => le_of_eq (abs_mul _ _)))
  -- Step 3: bound sums using infNormVec
  have ha2 : ∑ j : Fin n, |iterMatrix n M_inv N i j| * |x j - x_hat k j| ≤
      (∑ j, |iterMatrix n M_inv N i j|) *
        infNormVec hn (fun i => x i - x_hat k i) := by
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact Finset.le_sup' (fun i => |x i - x_hat k i|) (Finset.mem_univ j)
  have hb2 : ∑ j : Fin n, |M_inv i j| * |ξ k j| ≤
      (∑ j, |M_inv i j|) * infNormVec hn (ξ k) := by
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact Finset.le_sup' (fun i => |ξ k i|) (Finset.mem_univ j)
  -- Combine
  calc |a - b| ≤ |a| + |b| := htri
    _ ≤ (∑ j, |iterMatrix n M_inv N i j|) *
          infNormVec hn (fun i => x i - x_hat k i) +
        (∑ j, |M_inv i j|) * infNormVec hn (ξ k) := by
        linarith [ha_bound.trans ha2, hb_bound.trans hb2]
    _ ≤ infNorm hn (iterMatrix n M_inv N) *
          infNormVec hn (fun i => x i - x_hat k i) +
        infNorm hn M_inv * infNormVec hn (ξ k) := by
        apply add_le_add <;>
          exact mul_le_mul_of_nonneg_right (row_sum_le_infNorm hn _ i)
            (infNormVec_nonneg hn _)

/-- **Eq. 16.8 (Normwise forward bound)**: ‖e_{m+1}‖∞ ≤ q^{m+1}·‖e₀‖∞ + μ·‖M⁻¹‖∞/(1−q)
    where q ≥ ‖G‖∞ and μ ≥ ‖ξ_k‖∞ for all k.  Proved by induction
    from `normwise_one_step_bound` using geometric contraction. -/
theorem normwise_forward_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hG : infNorm hn (iterMatrix n M_inv N) ≤ q)
    (μ : ℝ) (hμ : 0 ≤ μ) (hξ_bound : ∀ k, infNormVec hn (ξ k) ≤ μ)
    (m : ℕ) :
    infNormVec hn (fun i => x i - x_hat (m + 1) i) ≤
      q ^ (m + 1) * infNormVec hn (fun i => x i - x_hat 0 i) +
      μ * infNorm hn M_inv / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hMn : 0 ≤ infNorm hn M_inv := infNorm_nonneg hn _
  have he₀ := infNormVec_nonneg hn (fun i => x i - x_hat 0 i)
  induction m with
  | zero =>
    have hone := normwise_one_step_bound n hn A M N M_inv hS b x hAx x_hat ξ hIter 0
    calc infNormVec hn (fun i => x i - x_hat 1 i)
        ≤ infNorm hn (iterMatrix n M_inv N) *
            infNormVec hn (fun i => x i - x_hat 0 i) +
          infNorm hn M_inv * infNormVec hn (ξ 0) := hone
      _ ≤ q * infNormVec hn (fun i => x i - x_hat 0 i) +
          infNorm hn M_inv * μ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hG (infNormVec_nonneg hn _)
          · exact mul_le_mul_of_nonneg_left (hξ_bound 0) hMn
      _ = q ^ 1 * infNormVec hn (fun i => x i - x_hat 0 i) +
          μ * infNorm hn M_inv := by rw [pow_one]; ring
      _ ≤ q ^ 1 * infNormVec hn (fun i => x i - x_hat 0 i) +
          μ * infNorm hn M_inv / (1 - q) := by
          have hnn : 0 ≤ μ * infNorm hn M_inv := mul_nonneg hμ hMn
          have hdiv : μ * infNorm hn M_inv ≤ μ * infNorm hn M_inv / (1 - q) := by
            rw [le_div_iff₀ hq1']; nlinarith
          linarith
  | succ m ih =>
    have hone := normwise_one_step_bound n hn A M N M_inv hS b x hAx x_hat ξ hIter (m + 1)
    calc infNormVec hn (fun i => x i - x_hat (m + 2) i)
        ≤ infNorm hn (iterMatrix n M_inv N) *
            infNormVec hn (fun i => x i - x_hat (m + 1) i) +
          infNorm hn M_inv * infNormVec hn (ξ (m + 1)) := hone
      _ ≤ q * (q ^ (m + 1) * infNormVec hn (fun i => x i - x_hat 0 i) +
            μ * infNorm hn M_inv / (1 - q)) +
          infNorm hn M_inv * μ := by
          apply add_le_add
          · exact le_trans (mul_le_mul_of_nonneg_right hG (infNormVec_nonneg hn _))
              (mul_le_mul_of_nonneg_left ih hq)
          · exact mul_le_mul_of_nonneg_left (hξ_bound _) hMn
      _ = q ^ (m + 2) * infNormVec hn (fun i => x i - x_hat 0 i) +
          (q * (μ * infNorm hn M_inv / (1 - q)) + μ * infNorm hn M_inv) := by ring
      _ = q ^ (m + 2) * infNormVec hn (fun i => x i - x_hat 0 i) +
          μ * infNorm hn M_inv / (1 - q) := by
          congr 1
          field_simp
          ring

-- ============================================================
-- §16.2  Main forward bound (eq 16.13)
-- ============================================================

/-- **Eq. 16.13 (Main componentwise forward bound)**: Composes the componentwise
    forward bound (eq 16.6) with local error simplification (eq 16.10) and the
    partial-sum bound c(A) (eq 16.12).  Given as hypotheses rather than
    re-deriving; this is a straightforward composition. -/
theorem main_forward_bound (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (M N : Fin n → Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (_hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x) (m : ℕ)
    (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    ∀ i, ∑ k ∈ Finset.range (m + 1),
      ∑ j : Fin n, (∑ l : Fin n, |matPow n G k i l| * |M_inv l j|) *
        (cn_u * (1 + θ_x) * ∑ p : Fin n, (|M j p| + |N j p|) * |x p|) ≤
      cn_u * (1 + θ_x) * cA *
        ∑ j : Fin n, |A_inv i j| *
          ∑ p : Fin n, (|M j p| + |N j p|) * |x p| := by
  intro i
  have hcoeff : 0 ≤ cn_u * (1 + θ_x) := mul_nonneg hcn (by linarith)
  calc ∑ k ∈ Finset.range (m + 1),
      ∑ j : Fin n, (∑ l, |matPow n G k i l| * |M_inv l j|) *
        (cn_u * (1 + θ_x) * ∑ p, (|M j p| + |N j p|) * |x p|)
      = cn_u * (1 + θ_x) * ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, (∑ l, |matPow n G k i l| * |M_inv l j|) *
            ∑ p, (|M j p| + |N j p|) * |x p| := by
        rw [Finset.mul_sum]; congr 1; ext k
        rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ cn_u * (1 + θ_x) * (cA * ∑ j : Fin n, |A_inv i j| *
          ∑ p, (|M j p| + |N j p|) * |x p|) := by
        apply mul_le_mul_of_nonneg_left _ hcoeff
        rw [Finset.sum_comm]; rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro j _
        rw [← Finset.sum_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hPartial i j) (Finset.sum_nonneg (fun p _ =>
          mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)))
    _ = cn_u * (1 + θ_x) * cA *
          ∑ j, |A_inv i j| * ∑ p, (|M j p| + |N j p|) * |x p| := by ring

-- ============================================================
-- §16.3  Normwise residual bound (eq 16.19)
-- ============================================================

/-- Normwise one-step residual bound from `one_step_residual`:
    ‖r_{k+1}‖∞ ≤ ‖H‖∞·‖r_k‖∞ + ‖I−H‖∞·‖ξ_k‖∞. -/
theorem normwise_one_step_residual_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) (k : ℕ) :
    infNormVec hn (fun i => b i - ∑ j, A i j * x_hat (k + 1) j) ≤
      infNorm hn (dualIterMatrix n N M_inv) *
        infNormVec hn (fun i => b i - ∑ j, A i j * x_hat k j) +
      infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) *
        infNormVec hn (ξ k) := by
  have hres := one_step_residual n A M N M_inv hS b x hAx x_hat ξ hIter
  suffices h : ∀ i : Fin n, |b i - ∑ j, A i j * x_hat (k + 1) j| ≤
      infNorm hn (dualIterMatrix n N M_inv) *
        infNormVec hn (fun i => b i - ∑ j, A i j * x_hat k j) +
      infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) *
        infNormVec hn (ξ k) by
    unfold infNormVec; apply Finset.sup'_le; intro i _; exact h i
  intro i; rw [hres k i]
  -- |Hr_k - (I-H)ξ_k| ≤ |Hr_k| + |(I-H)ξ_k| ≤ ‖H‖·‖r_k‖ + ‖I-H‖·‖ξ_k‖
  set a := matMulVec n (dualIterMatrix n N M_inv)
      (fun j => b j - ∑ l, A j l * x_hat k l) i
  set c := matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i
  have htri : |a - c| ≤ |a| + |c| := (abs_add_le a (-c)).trans (by rw [abs_neg])
  have ha : |a| ≤ infNorm hn (dualIterMatrix n N M_inv) *
      infNormVec hn (fun i => b i - ∑ j, A i j * x_hat k j) := by
    change |∑ j : Fin n, dualIterMatrix n N M_inv i j *
        (b j - ∑ l, A j l * x_hat k l)| ≤ _
    calc |∑ j, dualIterMatrix n N M_inv i j *
            (b j - ∑ l, A j l * x_hat k l)|
        ≤ ∑ j, |dualIterMatrix n N M_inv i j *
            (b j - ∑ l, A j l * x_hat k l)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |dualIterMatrix n N M_inv i j| *
            |b j - ∑ l, A j l * x_hat k l| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, |dualIterMatrix n N M_inv i j| *
            infNormVec hn (fun i => b i - ∑ j, A i j * x_hat k j) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Finset.le_sup' (fun i => |b i - ∑ j, A i j * x_hat k j|)
            (Finset.mem_univ j)
      _ = (∑ j, |dualIterMatrix n N M_inv i j|) *
            infNormVec hn (fun i => b i - ∑ j, A i j * x_hat k j) := by
          rw [Finset.sum_mul]
      _ ≤ infNorm hn (dualIterMatrix n N M_inv) *
            infNormVec hn (fun i => b i - ∑ j, A i j * x_hat k j) :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm hn _ i)
            (infNormVec_nonneg hn _)
  have hc : |c| ≤ infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) *
      infNormVec hn (ξ k) := by
    change |∑ j : Fin n, matSub_id n (dualIterMatrix n N M_inv) i j *
        ξ k j| ≤ _
    calc |∑ j, matSub_id n (dualIterMatrix n N M_inv) i j * ξ k j|
        ≤ ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j * ξ k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j| * |ξ k j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j| *
            infNormVec hn (ξ k) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact Finset.le_sup' (fun i => |ξ k i|) (Finset.mem_univ j)
      _ = (∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j|) *
            infNormVec hn (ξ k) := by rw [Finset.sum_mul]
      _ ≤ infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec hn (ξ k) :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm hn _ i)
            (infNormVec_nonneg hn _)
  linarith

/-- **Eq. 16.19 (Normwise residual bound)**: ‖r_{m+1}‖∞ ≤ q^{m+1}·‖r₀‖∞ + μ·‖I−H‖∞/(1−q)
    where q ≥ ‖H‖∞ and μ ≥ ‖ξ_k‖∞ for all k.  Derived by induction
    from `normwise_one_step_residual_bound` using geometric contraction. -/
theorem normwise_residual_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm hn (dualIterMatrix n N M_inv) ≤ q)
    (μ : ℝ) (hμ : 0 ≤ μ) (hξ_bound : ∀ k, infNormVec hn (ξ k) ≤ μ)
    (m : ℕ) :
    infNormVec hn (fun i => b i - ∑ j, A i j * x_hat (m + 1) j) ≤
      q ^ (m + 1) * infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
      μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hImH := infNorm_nonneg hn (matSub_id n (dualIterMatrix n N M_inv))
  induction m with
  | zero =>
    have hone := normwise_one_step_residual_bound n hn A M N M_inv hS b x hAx
        x_hat ξ hIter 0
    calc infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 1 j)
        ≤ infNorm hn (dualIterMatrix n N M_inv) *
            infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec hn (ξ 0) := hone
      _ ≤ q * infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) * μ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hH (infNormVec_nonneg hn _)
          · exact mul_le_mul_of_nonneg_left (hξ_bound 0) hImH
      _ = q ^ 1 * infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) := by
          rw [pow_one]; ring
      _ ≤ q ^ 1 * infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q) := by
          have hnn : 0 ≤ μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) :=
            mul_nonneg hμ hImH
          have hdiv : μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) ≤
              μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) /
                (1 - q) := by
            rw [le_div_iff₀ hq1']; nlinarith
          linarith
  | succ m ih =>
    have hone := normwise_one_step_residual_bound n hn A M N M_inv hS b x hAx
        x_hat ξ hIter (m + 1)
    calc infNormVec hn (fun i => b i - ∑ j, A i j * x_hat (m + 2) j)
        ≤ infNorm hn (dualIterMatrix n N M_inv) *
            infNormVec hn (fun i => b i - ∑ j, A i j * x_hat (m + 1) j) +
          infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec hn (ξ (m + 1)) := hone
      _ ≤ q * (q ^ (m + 1) *
              infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
            μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) /
              (1 - q)) +
          infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) * μ := by
          apply add_le_add
          · exact le_trans (mul_le_mul_of_nonneg_right hH (infNormVec_nonneg hn _))
              (mul_le_mul_of_nonneg_left ih hq)
          · exact mul_le_mul_of_nonneg_left (hξ_bound _) hImH
      _ = q ^ (m + 2) *
            infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          (q * (μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q)) +
           μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv))) := by
          ring
      _ = q ^ (m + 2) *
            infNormVec hn (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q) := by
          congr 1; field_simp; ring

end LeanFpAnalysis.FP
