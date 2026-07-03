-- Algorithms/Sylvester/SylvesterBackward.lean
--
-- SVD-based backward error analysis for the Sylvester equation (Higham §16.2).
-- Eqs 16.13-16.19: backward error characterization via SVD coordinates,
-- lower/upper bounds on η(Y), and amplification factor μ.

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

end LeanFpAnalysis.FP
