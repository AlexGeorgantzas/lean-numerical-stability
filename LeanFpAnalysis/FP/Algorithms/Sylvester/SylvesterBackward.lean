-- Algorithms/Sylvester/SylvesterBackward.lean
--
-- SVD-based backward error analysis for the Sylvester equation (Higham §16.2).
-- Eqs 16.13-16.19: backward error characterization via SVD coordinates,
-- lower/upper bounds on η(Y), amplification factor μ, and the Lyapunov
-- scalar-coordinate and xi/mu analogues in §16.2.1.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- SVD representation (§16.2, eq 16.13)
-- ============================================================

/-- **SVD representation**: Y = U · diag(σ) · Vᵀ.
    We represent this as the pointwise identity
    Y_{ij} = ∑_k U_{ik} σ_k V_{jk}. -/
def IsSVD (n : ℕ) (Y : Fin n → Fin n → ℝ)
    (U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) : Prop :=
  IsOrthogonal n U ∧ IsOrthogonal n V ∧
  (∀ i j, Y i j = ∑ k : Fin n, U i k * (σ k * V j k)) ∧
  (∀ i, 0 ≤ σ i)

-- ============================================================
-- Transformed residual in SVD coordinates (§16.2, eq 16.13)
-- ============================================================

/-- **Transformed residual** in SVD coordinates: R̃ = UᵀRV where
    R is the Sylvester residual. -/
noncomputable def svdResidual (n : ℕ)
    (U V : Fin n → Fin n → ℝ)
    (R : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (matMul n (matTranspose U) R) V

/-- The SVD-transformed residual has the same Frobenius norm as R:
    ‖R̃‖²_F = ‖R‖²_F, since orthogonal transformations preserve ‖·‖_F. -/
theorem svdResidual_frobNormSq (n : ℕ) (U V R : Fin n → Fin n → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    frobNormSq (svdResidual n U V R) = frobNormSq R := by
  unfold svdResidual
  -- ‖(UᵀR)V‖²_F = ‖UᵀR‖²_F = ‖R‖²_F
  rw [frobNormSq_orthogonal_right _ _ hV, frobNormSq_orthogonal_left _ _ hU.transpose]

-- ============================================================
-- Backward error ξ² definition (§16.2, eq 16.16)
-- ============================================================

/-- **ξ² functional** (eq 16.16): given transformed residual R̃ and
    singular values σ, with tolerances α, β, γ:
      ξ² = ∑_{i,j} r̃²_{ij} / (α²σ²_j + β²σ²_i + γ²). -/
noncomputable def xiSq (n : ℕ) (R_tilde : Fin n → Fin n → ℝ)
    (σ : Fin n → ℝ) (α β γ : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    R_tilde i j ^ 2 / (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)

/-- ξ² is nonneg when all denominators are positive. -/
lemma xiSq_nonneg {n : ℕ} (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    0 ≤ xiSq n R_tilde σ α β γ := by
  unfold xiSq
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact div_nonneg (sq_nonneg _) (le_of_lt (hpos i j))

-- ============================================================
-- Backward error lower bound (§16.2, eq 16.15 lower)
-- ============================================================

/-- **Backward error lower bound** (eq 16.15, lower direction):
    For ANY perturbations ΔÃ, ΔB̃, ΔC̃ satisfying the entry-wise
    backward error equation ΔÃ_{ij}σ_j - σ_iΔB̃_{ij} - ΔC̃_{ij} = R̃_{ij},
    we have ξ² ≤ ‖ΔÃ‖²_F/α² + ‖ΔB̃‖²_F/β² + ‖ΔC̃‖²_F/γ².

    This is a consequence of the Cauchy-Schwarz inequality applied entry by
    entry: R̃² = (ασ_j · ΔÃ/α - βσ_i · ΔB̃/β - γ · ΔC̃/γ)²
    ≤ (α²σ²_j + β²σ²_i + γ²)(ΔÃ²/α² + ΔB̃²/β² + ΔC̃²/γ²). -/
theorem backward_error_lower_sq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (DA DB DC : Fin n → Fin n → ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)
    (hEq : ∀ i j : Fin n,
      DA i j * σ j - σ i * DB i j - DC i j = R_tilde i j) :
    xiSq n R_tilde σ α β γ ≤
    ∑ i : Fin n, ∑ j : Fin n,
      (DA i j ^ 2 / α ^ 2 + DB i j ^ 2 / β ^ 2 + DC i j ^ 2 / γ ^ 2) := by
  unfold xiSq
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  have hd := hpos i j
  -- R̃² / denom ≤ ΔA²/α² + ΔB²/β² + ΔC²/γ²
  rw [div_le_iff₀ hd, ← hEq i j]
  -- (ΔA·σ_j - σ_i·ΔB - ΔC)² ≤ (ΔA²/α² + ΔB²/β² + ΔC²/γ²)(α²σ²_j + β²σ²_i + γ²)
  -- Goal: (DA·σ_j - σ_i·DB - DC)² ≤ (DA²/α² + DB²/β² + DC²/γ²) · denom
  -- Suffices to prove: denom · LHS ≤ denom · RHS, i.e.,
  -- (DA·σ_j - σ_i·DB - DC)² · 1 ≤ (DA²/α² + DB²/β² + DC²/γ²) · denom
  -- By Cauchy-Schwarz: (ασ_j·(DA/α) + (-βσ_i)·(DB/β) + (-γ)·(DC/γ))²
  --   ≤ (α²σ²_j + β²σ²_i + γ²) · (DA²/α² + DB²/β² + DC²/γ²)
  -- We verify: ασ_j·(DA/α) = DA·σ_j, βσ_i·(DB/β) = σ_i·DB, γ·(DC/γ) = DC ✓
  -- Multiply both sides by α²β²γ² to clear denominators:
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  rw [show DA i j ^ 2 / α ^ 2 + DB i j ^ 2 / β ^ 2 + DC i j ^ 2 / γ ^ 2 =
      (DA i j ^ 2 * β ^ 2 * γ ^ 2 + DB i j ^ 2 * α ^ 2 * γ ^ 2 +
       DC i j ^ 2 * α ^ 2 * β ^ 2) / (α ^ 2 * β ^ 2 * γ ^ 2) from by
    field_simp]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by positivity)]
  -- Cauchy-Schwarz: (∑ a_k x_k)² ≤ (∑ a²_k)(∑ x²_k)
  -- a = (ασ_j, -βσ_i, -γ), x = (DA·βγ, DB·αγ, DC·αβ)
  -- (∑ ax)² = (αβγ(DA·σ_j - σ_i·DB - DC))²
  -- Hints: three cross-term squares that encode Cauchy-Schwarz
  nlinarith [sq_nonneg (α * σ j * DB i j * α * γ - (-β * σ i) * DA i j * β * γ),
             sq_nonneg (α * σ j * DC i j * α * β - (-γ) * DA i j * β * γ),
             sq_nonneg ((-β * σ i) * DC i j * α * β - (-γ) * DB i j * α * γ)]

-- ============================================================
-- Backward error upper bound (§16.2, eq 16.15 upper)
-- ============================================================

/-- **Backward error upper bound** (eq 16.15, upper direction):
    The optimal perturbations in SVD coordinates achieve cost exactly ξ².
    We prove one component: ∑ (Δã_opt)² ≤ α² · ξ² where
      Δã_opt_{ij} = α²σ_j · r̃_{ij} / (α²σ²_j + β²σ²_i + γ²). -/
theorem backward_error_upper_component (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) :
    ∑ i : Fin n, ∑ j : Fin n,
      (α ^ 2 * σ j * R_tilde i j /
       (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2 ≤
    α ^ 2 * xiSq n R_tilde σ α β γ := by
  unfold xiSq; rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  have hd := hpos i j
  have hd_ne : (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ≠ 0 := ne_of_gt hd
  -- (α²σ_j r̃ / d)² ≤ α² · (r̃² / d)
  -- Multiply out: α⁴σ²_j r̃² ≤ α² r̃² d = α² r̃²(α²σ²_j + β²σ²_i + γ²)
  -- which simplifies to α²σ²_j ≤ α²σ²_j + β²σ²_i + γ² ✓
  -- (α²σ_j r̃ / d)² = α⁴σ²_j r̃² / d²
  -- α²(r̃²/d) = α² r̃² / d
  -- Need: α⁴σ²_j r̃²/d² ≤ α² r̃²/d, i.e., α⁴σ²_j r̃² · d ≤ α² r̃² · d²
  -- i.e., α²σ²_j ≤ d = α²σ²_j + β²σ²_i + γ² ✓
  have key : (α ^ 2 * σ j * R_tilde i j) ^ 2 ≤
      α ^ 2 * R_tilde i j ^ 2 *
      (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
    nlinarith [sq_nonneg (R_tilde i j * β * σ i), sq_nonneg (R_tilde i j * γ)]
  calc (α ^ 2 * σ j * R_tilde i j /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) ^ 2
      = (α ^ 2 * σ j * R_tilde i j) ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        rw [div_pow]
    _ ≤ (α ^ 2 * R_tilde i j ^ 2 *
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ^ 2 := by
        exact div_le_div_of_nonneg_right key (sq_nonneg _)
    _ = α ^ 2 * R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) := by
        rw [sq]; field_simp
    _ = α ^ 2 * (R_tilde i j ^ 2 /
        (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)) := by
        rw [mul_div_assoc]

-- ============================================================
-- Amplification factor (§16.2, eqs 16.17-16.19)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equation (16.18):
    scalar amplification factor `mu` comparing the backward error scale with
    the normwise relative residual.  The singular-value arguments are the
    source's zero-extended `sigma_m` and `sigma_n` slots for an `m x n`
    approximate solution. -/
noncomputable def sylvesterAmplificationMu
    (α β γ yNorm σm σn : ℝ) : ℝ :=
  ((α + β) * yNorm + γ) /
    Real.sqrt (α ^ 2 * σn ^ 2 + β ^ 2 * σm ^ 2 + γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.19):
    square-case specialization of the amplification factor. -/
noncomputable def sylvesterAmplificationMuSquare
    (α β γ yNorm σmin : ℝ) : ℝ :=
  ((α + β) * yNorm + γ) /
    Real.sqrt ((α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2)

/-- In the square case, the two singular-value slots in (16.18) coincide,
    giving the source formula (16.19). -/
theorem sylvesterAmplificationMu_square_eq
    (α β γ yNorm σmin : ℝ) :
    sylvesterAmplificationMu α β γ yNorm σmin σmin =
      sylvesterAmplificationMuSquare α β γ yNorm σmin := by
  unfold sylvesterAmplificationMu sylvesterAmplificationMuSquare
  rw [show α ^ 2 * σmin ^ 2 + β ^ 2 * σmin ^ 2 + γ ^ 2 =
      (α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2 by ring]

/-- Higham, 2nd ed., Chapter 16.2, prose after equation (16.18):
    in the square case the amplification factor is at least one, provided the
    singular-value slot is bounded by the Frobenius norm of the approximate
    solution.  The latter is the singular-value foundation still kept explicit
    in this square API. -/
theorem one_le_sylvesterAmplificationMuSquare
    (α β γ yNorm σmin : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hy : 0 ≤ yNorm) (hσ : 0 ≤ σmin) (hσ_le : σmin ≤ yNorm)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2) :
    1 ≤ sylvesterAmplificationMuSquare α β γ yNorm σmin := by
  unfold sylvesterAmplificationMuSquare
  have hsqrt_pos :
      0 < Real.sqrt ((α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2) :=
    Real.sqrt_pos.2 hDenom
  have hσsq : σmin ^ 2 ≤ yNorm ^ 2 :=
    (sq_le_sq₀ hσ hy).mpr hσ_le
  have hN_nonneg : 0 ≤ (α + β) * yNorm + γ := by
    nlinarith [mul_nonneg (add_nonneg hα hβ) hy]
  have hD_le :
      (α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2 ≤
        ((α + β) * yNorm + γ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hσsq (sq_nonneg α),
      mul_le_mul_of_nonneg_left hσsq (sq_nonneg β),
      mul_nonneg hα hβ,
      mul_nonneg (add_nonneg hα hβ) hy,
      mul_nonneg hγ (mul_nonneg (add_nonneg hα hβ) hy)]
  have hsqrt_le :
      Real.sqrt ((α ^ 2 + β ^ 2) * σmin ^ 2 + γ ^ 2) ≤
        (α + β) * yNorm + γ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hN_nonneg).mp
    rw [Real.sq_sqrt (le_of_lt hDenom)]
    exact hD_le
  exact (one_le_div hsqrt_pos).mpr hsqrt_le

/-- **Amplification factor bound** (eqs 16.17-16.18):
    ξ² ≤ ‖R̃‖²_F / ((α²+β²)σ²_min + γ²)
    when all singular values satisfy σ_i ≥ σ_min.

    Combined with ‖R̃‖²_F = ‖R‖²_F (orthogonal invariance), this gives
    ξ ≤ ‖R‖_F / √((α²+β²)σ²_min + γ²). -/
theorem xiSq_amplification_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ σ_min : ℝ) (hσ_min : ∀ i : Fin n, σ_min ≤ σ i)
    (hσ_min_nn : 0 ≤ σ_min)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) :
    xiSq n R_tilde σ α β γ ≤
    frobNormSq R_tilde / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := by
  unfold xiSq
  -- Each term: r̃²/(α²σ²_j + β²σ²_i + γ²) ≤ r̃²/((α²+β²)σ²_min + γ²)
  -- Sum of RHS = (∑∑ r̃²) / d = ‖R̃‖²_F / d
  have hd_ne : (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 ≠ 0 := ne_of_gt hDenom
  -- First show ∑∑ r̃²/denom_ij ≤ ∑∑ r̃²/denom_min
  suffices h : ∑ i : Fin n, ∑ j : Fin n,
      R_tilde i j ^ 2 / (α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n,
      R_tilde i j ^ 2 / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) by
    rwa [show ∑ i : Fin n, ∑ j : Fin n,
        R_tilde i j ^ 2 / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) =
        frobNormSq R_tilde / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) from by
      unfold frobNormSq
      rw [eq_div_iff hd_ne]
      rw [Finset.sum_mul]; congr 1; ext i
      rw [Finset.sum_mul]; congr 1; ext j
      exact div_mul_cancel₀ _ hd_ne] at h
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  have hσi : σ_min ^ 2 ≤ σ i ^ 2 :=
    sq_le_sq' (by linarith [hσ_min i]) (hσ_min i)
  have hσj : σ_min ^ 2 ≤ σ j ^ 2 :=
    sq_le_sq' (by linarith [hσ_min j]) (hσ_min j)
  have hdenom_le : (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 ≤
      α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2 := by nlinarith [sq_nonneg α, sq_nonneg β]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hDenom hdenom_le

/-- **Amplification factor with orthogonal invariance** (eq 16.19, m=n case):
    ξ² ≤ ‖R‖²_F / ((α²+β²)σ²_min + γ²). -/
theorem amplification_factor_bound (n : ℕ)
    (Y R : Fin n → Fin n → ℝ)
    (U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ σ_min : ℝ)
    (hSVD : IsSVD n Y U V σ)
    (hσ_min : ∀ i : Fin n, σ_min ≤ σ i) (hσ_min_nn : 0 ≤ σ_min)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) :
    xiSq n (svdResidual n U V R) σ α β γ ≤
    frobNormSq R / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := by
  have hle := xiSq_amplification_bound n (svdResidual n U V R) σ α β γ σ_min
    hσ_min hσ_min_nn hDenom
  rw [svdResidual_frobNormSq n U V R hSVD.1 hSVD.2.1] at hle
  exact hle

/-- Higham, 2nd ed., Chapter 16.2, equations (16.17)-(16.19):
    the existing square xi-squared residual bound written with the source's
    amplification factor `mu`.  This is still a bound for `xi`; the separate
    optimizer step relating `eta(Y)` and `xi` remains the open part of
    equation (16.15). -/
theorem xiSq_le_mu_relative_residual_sq (n : ℕ)
    (Y R : Fin n → Fin n → ℝ)
    (U V : Fin n → Fin n → ℝ) (σ : Fin n → ℝ)
    (α β γ σ_min : ℝ)
    (hSVD : IsSVD n Y U V σ)
    (hσ_min : ∀ i : Fin n, σ_min ≤ σ i) (hσ_min_nn : 0 ≤ σ_min)
    (hDenom : 0 < (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2)
    (hScale : 0 < (α + β) * frobNorm Y + γ) :
    xiSq n (svdResidual n U V R) σ α β γ ≤
      (sylvesterAmplificationMuSquare α β γ (frobNorm Y) σ_min *
        (frobNorm R / ((α + β) * frobNorm Y + γ))) ^ 2 := by
  have hle := amplification_factor_bound n Y R U V σ α β γ σ_min
    hSVD hσ_min hσ_min_nn hDenom
  have hScale_ne : (α + β) * frobNorm Y + γ ≠ 0 := ne_of_gt hScale
  have hD_ne : (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 ≠ 0 := ne_of_gt hDenom
  have hSqrt_ne : Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hDenom)
  have hSqrt_sq :
      Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) ^ 2 =
        (α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2 :=
    Real.sq_sqrt (le_of_lt hDenom)
  calc
    xiSq n (svdResidual n U V R) σ α β γ ≤
        frobNormSq R / ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := hle
    _ = (sylvesterAmplificationMuSquare α β γ (frobNorm Y) σ_min *
        (frobNorm R / ((α + β) * frobNorm Y + γ))) ^ 2 := by
        unfold sylvesterAmplificationMuSquare
        have hmul :
            ((α + β) * frobNorm Y + γ) /
                Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) *
              (frobNorm R / ((α + β) * frobNorm Y + γ)) =
                frobNorm R /
                  Real.sqrt ((α ^ 2 + β ^ 2) * σ_min ^ 2 + γ ^ 2) := by
          field_simp [hScale_ne, hSqrt_ne]
        rw [hmul, div_pow, hSqrt_sq, frobNorm_sq]

-- ============================================================
-- Backward error η bound via cost (§16.2)
-- ============================================================

/-- **Backward error η bound via perturbation cost**:
    If ‖ΔA‖²_F ≤ η²α², ‖ΔB‖²_F ≤ η²β², ‖ΔC‖²_F ≤ η²γ²,
    and the entry-wise backward error equation holds in SVD coordinates,
    then ξ² ≤ η²(α² + β² + γ²). -/
theorem backward_error_eta_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (σ : Fin n → ℝ) (α β γ η : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (DA DB DC : Fin n → Fin n → ℝ)
    (hpos : ∀ i j : Fin n, 0 < α ^ 2 * σ j ^ 2 + β ^ 2 * σ i ^ 2 + γ ^ 2)
    (hEq : ∀ i j : Fin n,
      DA i j * σ j - σ i * DB i j - DC i j = R_tilde i j)
    (hDA : frobNormSq DA ≤ (η * α) ^ 2)
    (hDB : frobNormSq DB ≤ (η * β) ^ 2)
    (hDC : frobNormSq DC ≤ (η * γ) ^ 2) :
    xiSq n R_tilde σ α β γ ≤ 3 * η ^ 2 := by
  have hle := backward_error_lower_sq n R_tilde σ α β γ hα hβ hγ DA DB DC hpos hEq
  -- ξ² ≤ ∑ (DA²/α² + DB²/β² + DC²/γ²) = ‖DA‖²_F/α² + ‖DB‖²_F/β² + ‖DC‖²_F/γ²
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      (DA i j ^ 2 / α ^ 2 + DB i j ^ 2 / β ^ 2 + DC i j ^ 2 / γ ^ 2) =
      frobNormSq DA / α ^ 2 + frobNormSq DB / β ^ 2 + frobNormSq DC / γ ^ 2 := by
    unfold frobNormSq; simp_rw [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul]
  rw [hsum] at hle
  -- ‖DA‖²/α² ≤ (ηα)²/α² = η², etc.
  have hα2 : (0 : ℝ) < α ^ 2 := sq_pos_of_pos hα
  have hβ2 : (0 : ℝ) < β ^ 2 := sq_pos_of_pos hβ
  have hγ2 : (0 : ℝ) < γ ^ 2 := sq_pos_of_pos hγ
  have h1 : frobNormSq DA / α ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hα2]; nlinarith
  have h2 : frobNormSq DB / β ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hβ2]; nlinarith
  have h3 : frobNormSq DC / γ ^ 2 ≤ η ^ 2 := by
    rw [div_le_iff₀ hγ2]; nlinarith
  linarith

-- ============================================================
-- Residual-based backward error bound (combining eqs 16.12 + 16.16)
-- ============================================================

/-- **Combined backward error bound** (eqs 16.12 + 16.16):
    If the backward error equation holds with cost η, then
    η ≥ ‖R‖_F / ((α+β)‖Y‖_F + γ)
    (from residual_bound, rearranged). This is the easy lower bound. -/
theorem backward_error_residual_lower (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ)
    (α β γ η : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hEq : ∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j)
    (hΔA : frobNorm ΔA ≤ η * α)
    (hΔB : frobNorm ΔB ≤ η * β)
    (hΔC : frobNorm ΔC ≤ η * γ)
    (_hd : 0 < (α + β) * frobNorm Y + γ) :
    frobNorm (sylvesterResidual n A B C Y) ≤
    ((α + β) * frobNorm Y + γ) * η := by
  exact residual_bound n A B C Y ΔA ΔB ΔC α β γ η hα hβ hγ hη hEq hΔA hΔB hΔC

-- ============================================================
-- Lyapunov spectral-coordinate backward error (§16.2.1, eq 16.21)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    spectral-coordinate transform `U^T M U` used for the Lyapunov residual and
    perturbations. -/
noncomputable def lyapunovSpectralTransform (n : ℕ)
    (U M : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n (matMul n (matTranspose U) M) U

/-- Orthogonal spectral coordinates preserve the squared Frobenius norm. -/
theorem lyapunovSpectralTransform_frobNormSq (n : ℕ)
    (U M : Fin n → Fin n → ℝ) (hU : IsOrthogonal n U) :
    frobNormSq (lyapunovSpectralTransform n U M) = frobNormSq M := by
  unfold lyapunovSpectralTransform
  rw [frobNormSq_orthogonal_right _ _ hU, frobNormSq_orthogonal_left _ _ hU.transpose]

/-- Spectral-coordinate transforms distribute over the `M + N - P` matrix
    combination used in the Lyapunov perturbation residual. -/
theorem lyapunovSpectralTransform_add_sub (n : ℕ)
    (U M N P : Fin n → Fin n → ℝ) :
    lyapunovSpectralTransform n U (fun i j => M i j + N i j - P i j) =
      fun i j => lyapunovSpectralTransform n U M i j +
        lyapunovSpectralTransform n U N i j -
          lyapunovSpectralTransform n U P i j := by
  ext i j
  unfold lyapunovSpectralTransform matMul matTranspose
  simp only [sub_eq_add_neg, add_mul, neg_mul, mul_add, mul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- Higham, 2nd ed., Chapter 16.2.1:
    original-coordinate Lyapunov perturbation residual
    `DeltaA * Y + Y * DeltaA^T - DeltaC`. -/
noncomputable def lyapunovBackwardResidual (n : ℕ)
    (DA DC Y : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n DA Y i j + matMul n Y (matTranspose DA) i j - DC i j

/-- If `Y = U * Lambda * U^T`, the left perturbation product transforms to
    `DeltaA_tilde * Lambda`. -/
theorem lyapunovSpectralTransform_mul_spectral_right (n : ℕ)
    (U DA : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    lyapunovSpectralTransform n U
      (matMul n DA (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))) =
        matMul n (lyapunovSpectralTransform n U DA) (diagMatrix lam) := by
  unfold lyapunovSpectralTransform
  have hUtU : matMul n (matTranspose U) U = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.left_inv i j
  simp [matMul_assoc, hUtU, matMul_id_right]

/-- If `Y = U * Lambda * U^T`, the right perturbation product transforms to
    `Lambda * DeltaA_tilde^T`. -/
theorem lyapunovSpectralTransform_spectral_left_transpose (n : ℕ)
    (U DA : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    lyapunovSpectralTransform n U
      (matMul n (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
        (matTranspose DA)) =
        matMul n (diagMatrix lam)
          (matTranspose (lyapunovSpectralTransform n U DA)) := by
  unfold lyapunovSpectralTransform
  have hUtU : matMul n (matTranspose U) U = idMatrix n := by
    ext i j
    simpa [matMul, idMatrix] using hU.left_inv i j
  calc
    matMul n (matMul n (matTranspose U)
        (matMul n (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
          (matTranspose DA))) U
        = matMul n (matMul n (matMul n (matTranspose U) U)
            (matMul n (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA))) U := by
            rw [matMul_assoc n U (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA)]
            rw [(matMul_assoc n (matTranspose U) U
              (matMul n (matMul n (diagMatrix lam) (matTranspose U))
                (matTranspose DA))).symm]
    _ = matMul n (matMul n (idMatrix n)
            (matMul n (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA))) U := by
            rw [hUtU]
    _ = matMul n
            (matMul n (matMul n (diagMatrix lam) (matTranspose U))
              (matTranspose DA)) U := by
            rw [matMul_id_left]
    _ = matMul n (diagMatrix lam)
            (matMul n (matTranspose U) (matMul n (matTranspose DA) U)) := by
            rw [matMul_assoc n (diagMatrix lam) (matTranspose U) (matTranspose DA)]
            rw [matMul_assoc n (diagMatrix lam)
              (matMul n (matTranspose U) (matTranspose DA)) U]
            rw [matMul_assoc n (matTranspose U) (matTranspose DA) U]
    _ = matMul n (diagMatrix lam)
            (matTranspose (matMul n (matMul n (matTranspose U) DA) U)) := by
            rw [matTranspose_matMul]
            rw [matTranspose_matMul]
            rw [matTranspose_involutive]

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    the transformed Lyapunov backward-error residual
    `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde`, written
    entrywise in the diagonal spectral coordinates of the symmetric approximate
    solution. -/
noncomputable def lyapunovSpectralBackwardResidual (n : ℕ)
    (DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => DA i j * lam j + lam i * DA j i - DC i j

/-- The entrywise residual from equation (16.21) is the diagonal-matrix
    expression `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde`. -/
theorem lyapunovSpectralBackwardResidual_eq_diagMatrix (n : ℕ)
    (DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) :
    lyapunovSpectralBackwardResidual n DA DC lam =
      fun i j =>
        matMul n DA (diagMatrix lam) i j +
          matMul n (diagMatrix lam) (matTranspose DA) i j -
            DC i j := by
  ext i j
  unfold lyapunovSpectralBackwardResidual
  rw [matMul_diagMatrix_right DA lam i j,
    matMul_diagMatrix_left lam (matTranspose DA) i j]
  simp [matTranspose]

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    transforming the original-coordinate Lyapunov perturbation residual with
    `Y = U * Lambda * U^T` gives the diagonal spectral-coordinate residual
    `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde`. -/
theorem lyapunovSpectralTransform_backwardResidual (n : ℕ)
    (U DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (hU : IsOrthogonal n U) :
    lyapunovSpectralTransform n U
      (lyapunovBackwardResidual n DA DC
        (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))) =
      lyapunovSpectralBackwardResidual n
        (lyapunovSpectralTransform n U DA)
        (lyapunovSpectralTransform n U DC) lam := by
  unfold lyapunovBackwardResidual
  rw [lyapunovSpectralTransform_add_sub n U
    (matMul n DA (matMul n U (matMul n (diagMatrix lam) (matTranspose U))))
    (matMul n (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
      (matTranspose DA))
    DC]
  rw [lyapunovSpectralTransform_mul_spectral_right n U DA lam hU]
  rw [lyapunovSpectralTransform_spectral_left_transpose n U DA lam hU]
  rw [lyapunovSpectralBackwardResidual_eq_diagMatrix n
    (lyapunovSpectralTransform n U DA) (lyapunovSpectralTransform n U DC) lam]

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    the printed scaled scalar equation in Lyapunov spectral coordinates. -/
def lyapunovBackwardScalarEq (n : ℕ) (lam : Fin n → ℝ) (α γ : ℝ)
    (DA DC R_tilde : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n,
    (DA i j / α) * (α * lam j) +
      (α * lam i) * (DA j i / α) -
        γ * (DC i j / γ) = R_tilde i j

/-- Equation (16.21) is equivalent to the unscaled transformed residual equation
    when the source scaling parameters are nonzero. -/
theorem lyapunovBackwardScalarEq_iff_unscaled (n : ℕ) (lam : Fin n → ℝ)
    (α γ : ℝ) (DA DC R_tilde : Fin n → Fin n → ℝ)
    (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ DA DC R_tilde ↔
      ∀ i j : Fin n, DA i j * lam j + lam i * DA j i - DC i j = R_tilde i j := by
  constructor
  · intro h i j
    have hscale :
        (DA i j / α) * (α * lam j) +
          (α * lam i) * (DA j i / α) -
            γ * (DC i j / γ) =
          DA i j * lam j + lam i * DA j i - DC i j := by
      field_simp [hα, hγ]
    simpa [hscale] using h i j
  · intro h i j
    have hscale :
        (DA i j / α) * (α * lam j) +
          (α * lam i) * (DA j i / α) -
            γ * (DC i j / γ) =
          DA i j * lam j + lam i * DA j i - DC i j := by
      field_simp [hα, hγ]
    rw [hscale]
    exact h i j

/-- Equation (16.21) as an equality between the transformed Lyapunov residual
    matrix and the transformed residual right-hand side. -/
theorem lyapunovBackwardScalarEq_iff_residual_eq (n : ℕ) (lam : Fin n → ℝ)
    (α γ : ℝ) (DA DC R_tilde : Fin n → Fin n → ℝ)
    (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ DA DC R_tilde ↔
      lyapunovSpectralBackwardResidual n DA DC lam = R_tilde := by
  rw [lyapunovBackwardScalarEq_iff_unscaled n lam α γ DA DC R_tilde hα hγ]
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    the printed scaled scalar equation follows from the original residual
    equation after the orthogonal spectral decomposition `Y = U * Lambda * U^T`. -/
theorem lyapunovBackwardScalarEq_of_spectral_decomposition (n : ℕ)
    (U DA DC : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hU : IsOrthogonal n U) (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ
      (lyapunovSpectralTransform n U DA)
      (lyapunovSpectralTransform n U DC)
      (lyapunovSpectralTransform n U
        (lyapunovBackwardResidual n DA DC
          (matMul n U (matMul n (diagMatrix lam) (matTranspose U))))) := by
  rw [lyapunovBackwardScalarEq_iff_residual_eq n lam α γ
    (lyapunovSpectralTransform n U DA)
    (lyapunovSpectralTransform n U DC)
    (lyapunovSpectralTransform n U
      (lyapunovBackwardResidual n DA DC
        (matMul n U (matMul n (diagMatrix lam) (matTranspose U)))))
    hα hγ]
  exact (lyapunovSpectralTransform_backwardResidual n U DA DC lam hU).symm

/-- Equation (16.21) as the diagonal-matrix residual equation
    `DeltaA_tilde * Lambda + Lambda * DeltaA_tilde^T - DeltaC_tilde = R_tilde`. -/
theorem lyapunovBackwardScalarEq_iff_diagMatrix_eq (n : ℕ) (lam : Fin n → ℝ)
    (α γ : ℝ) (DA DC R_tilde : Fin n → Fin n → ℝ)
    (hα : α ≠ 0) (hγ : γ ≠ 0) :
    lyapunovBackwardScalarEq n lam α γ DA DC R_tilde ↔
      (fun i j =>
        matMul n DA (diagMatrix lam) i j +
          matMul n (diagMatrix lam) (matTranspose DA) i j -
            DC i j) = R_tilde := by
  rw [lyapunovBackwardScalarEq_iff_residual_eq n lam α γ DA DC R_tilde hα hγ]
  rw [lyapunovSpectralBackwardResidual_eq_diagMatrix n DA DC lam]

/-- Higham, 2nd ed., Chapter 16.2.1, unnumbered formula after equation (16.21):
    Lyapunov-structured squared `xi` functional in spectral coordinates. -/
noncomputable def lyapunovXiSq (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2) /
      (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) ^ 2

/-- The simple upper summand appearing after the Lyapunov `xi^2` formula. -/
noncomputable def lyapunovXiSqSimpleBound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (2 * R_tilde i j ^ 2) /
      (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)

/-- Higham, 2nd ed., Chapter 16.2.1, unnumbered inequality after equation
    (16.21): the exact Lyapunov `xi^2` summand is bounded by the simpler
    residual-weighted summand when the displayed denominators are positive. -/
theorem lyapunovXiSq_le_simple_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (α γ : ℝ)
    (hpos : ∀ i j : Fin n, 0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2) :
    lyapunovXiSq n R_tilde lam α γ ≤
      lyapunovXiSqSimpleBound n R_tilde lam α γ := by
  unfold lyapunovXiSq lyapunovXiSqSimpleBound
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  let D : ℝ := 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2
  have hD : 0 < D := hpos i j
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hD_ne : D ≠ 0 := ne_of_gt hD
  have hkey :
      (4 * α ^ 2 * lam j ^ 2 + γ ^ 2) * R_tilde i j ^ 2 ≤
        (2 * R_tilde i j ^ 2) * D := by
    nlinarith [sq_nonneg (R_tilde i j * α * lam i),
      sq_nonneg (R_tilde i j * γ)]
  have hright :
      (2 * R_tilde i j ^ 2 / D) * D ^ 2 =
        (2 * R_tilde i j ^ 2) * D := by
    field_simp [hD_ne]
  rw [div_le_iff₀ hD2]
  rw [hright]
  exact hkey

/-- Higham, 2nd ed., Chapter 16.2.1, final display:
    Lyapunov analogue of the amplification factor `mu`. -/
noncomputable def lyapunovAmplificationMu (α γ yNorm lamStar : ℝ) : ℝ :=
  Real.sqrt 2 * (2 * α * yNorm + γ) /
    Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)

/-- Lyapunov xi-squared residual bound using an explicit lower square bound on
    the spectral magnitudes.  This is the xi-level foundation behind the final
    Lyapunov analogue of equations (16.17)-(16.18). -/
theorem lyapunovXiSq_le_min_eigen_bound (n : ℕ)
    (R_tilde : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) :
    lyapunovXiSq n R_tilde lam α γ ≤
      2 * frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
  have hdenom_le : ∀ i j : Fin n,
      4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 ≤
        2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 := by
    intro i j
    nlinarith [sq_nonneg α, hLam i, hLam j]
  have hpos : ∀ i j : Fin n, 0 < 2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2 := by
    intro i j
    exact lt_of_lt_of_le hDenom (hdenom_le i j)
  have hsimple := lyapunovXiSq_le_simple_bound n R_tilde lam α γ hpos
  have hD_ne : 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 ≠ 0 := ne_of_gt hDenom
  have hbound :
      lyapunovXiSqSimpleBound n R_tilde lam α γ ≤
        2 * frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
    unfold lyapunovXiSqSimpleBound
    suffices h :
        (∑ i : Fin n, ∑ j : Fin n,
          (2 * R_tilde i j ^ 2) /
            (2 * α ^ 2 * (lam i ^ 2 + lam j ^ 2) + γ ^ 2)) ≤
          (∑ i : Fin n, ∑ j : Fin n,
            (2 * R_tilde i j ^ 2) /
              (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)) by
      rwa [show
          (∑ i : Fin n, ∑ j : Fin n,
            (2 * R_tilde i j ^ 2) /
              (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)) =
            2 * frobNormSq R_tilde / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) from by
        unfold frobNormSq
        rw [eq_div_iff hD_ne]
        rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact div_mul_cancel₀ _ hD_ne] at h
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact div_le_div_of_nonneg_left (by positivity) hDenom (hdenom_le i j)
  exact le_trans hsimple hbound

/-- Lyapunov xi-squared residual bound after the orthogonal spectral transform
    `R_tilde = U^T R U`. -/
theorem lyapunovXiSq_spectral_le_min_eigen_bound (n : ℕ)
    (R U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hU : IsOrthogonal n U)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) :
    lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
      2 * frobNormSq R / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
  have hle :=
    lyapunovXiSq_le_min_eigen_bound n (lyapunovSpectralTransform n U R) lam
      α γ lamStar hLam hDenom
  rw [lyapunovSpectralTransform_frobNormSq n U R hU] at hle
  exact hle

/-- Higham, 2nd ed., Chapter 16.2.1, final display:
    the Lyapunov xi-squared residual bound written with the source amplification
    factor `mu`.  This is still an xi-level result; the eta optimizer bridge
    remains open. -/
theorem lyapunovXiSq_le_mu_relative_residual_sq (n : ℕ)
    (Y R U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (α γ lamStar : ℝ)
    (hU : IsOrthogonal n U)
    (hLam : ∀ i : Fin n, lamStar ^ 2 ≤ lam i ^ 2)
    (hDenom : 0 < 4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)
    (hScale : 0 < 2 * α * frobNorm Y + γ) :
    lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
      (lyapunovAmplificationMu α γ (frobNorm Y) lamStar *
        (frobNorm R / (2 * α * frobNorm Y + γ))) ^ 2 := by
  have hle :=
    lyapunovXiSq_spectral_le_min_eigen_bound n R U lam α γ lamStar
      hU hLam hDenom
  have hScale_ne : 2 * α * frobNorm Y + γ ≠ 0 := ne_of_gt hScale
  have hSqrt_ne : Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hDenom)
  have hSqrt_sq :
      Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) ^ 2 =
        4 * α ^ 2 * lamStar ^ 2 + γ ^ 2 :=
    Real.sq_sqrt (le_of_lt hDenom)
  have hsqrt_two_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by linarith)
  calc
    lyapunovXiSq n (lyapunovSpectralTransform n U R) lam α γ ≤
        2 * frobNormSq R / (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := hle
    _ = (lyapunovAmplificationMu α γ (frobNorm Y) lamStar *
        (frobNorm R / (2 * α * frobNorm Y + γ))) ^ 2 := by
        unfold lyapunovAmplificationMu
        have hmul :
            (Real.sqrt 2 * (2 * α * frobNorm Y + γ) /
                Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2)) *
              (frobNorm R / (2 * α * frobNorm Y + γ)) =
                Real.sqrt 2 * frobNorm R /
                  Real.sqrt (4 * α ^ 2 * lamStar ^ 2 + γ ^ 2) := by
          field_simp [hScale_ne, hSqrt_ne]
        rw [hmul, div_pow, mul_pow, hsqrt_two_sq, hSqrt_sq, frobNorm_sq]

end LeanFpAnalysis.FP
