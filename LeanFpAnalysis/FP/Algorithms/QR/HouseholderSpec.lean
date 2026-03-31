-- Algorithms/QR/HouseholderSpec.lean
--
-- Householder reflector definition and algebraic properties (Higham §18.1),
-- plus backward error model for Householder application (Lemma 18.2).
--
-- A Householder matrix P = I − β·v·vᵀ is symmetric and orthogonal when
-- β = 2/(vᵀv). Applying P to a vector in floating-point yields
-- ŷ = (P + ΔP)b with ‖ΔP‖_F bounded (Lemma 18.2).

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §18.1  Householder matrix definition
-- ============================================================

/-- **Householder reflector** P = I − β·v·vᵀ (eq 18.1).

    Given a nonzero vector v ∈ ℝⁿ and scalar β, the Householder matrix
    is defined by P_{ij} = δ_{ij} − β·v_i·v_j. When β = 2/(vᵀv),
    P is both symmetric and orthogonal. -/
noncomputable def householder (n : ℕ) (v : Fin n → ℝ) (β : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - β * v i * v j

/-- P = Pᵀ: Householder matrices are symmetric. -/
theorem householder_symmetric (n : ℕ) (v : Fin n → ℝ) (β : ℝ) :
    matTranspose (householder n v β) = householder n v β := by
  ext i j; unfold matTranspose householder idMatrix
  simp [eq_comm (a := i) (b := j)]
  ring

/-- (vvᵀ)(vvᵀ) = (vᵀv)·vvᵀ: key identity for Householder orthogonality.

    The outer product of v with itself, squared as a matrix product,
    equals the scalar (vᵀv) times the outer product. -/
theorem outerProd_self_mul (n : ℕ) (v : Fin n → ℝ) :
    ∀ i j, matMul n (fun a b => v a * v b) (fun a b => v a * v b) i j =
      (∑ k : Fin n, v k * v k) * (v i * v j) := by
  intro i j; unfold matMul
  -- ∑_k (v_i · v_k)(v_k · v_j) = v_i · (∑_k v_k²) · v_j
  have : ∀ k : Fin n,
      v i * v k * (v k * v j) = v i * v j * (v k * v k) := by
    intro k; ring
  simp_rw [this, ← Finset.mul_sum]; ring

/-- P is orthogonal when β·(vᵀv) = 2 (Higham eq 18.1).

    Proof: P² = (I − βvvᵀ)² = I − 2βvvᵀ + β²(vᵀv)vvᵀ = I
    since β²(vᵀv) = 2β when β(vᵀv) = 2. Combined with Pᵀ = P,
    this gives PᵀP = P² = I. -/
theorem householder_orthogonal (n : ℕ) (v : Fin n → ℝ) (β : ℝ)
    (hβ : β * (∑ k : Fin n, v k * v k) = 2) :
    IsOrthogonal n (householder n v β) := by
  have hsym := householder_symmetric n v β
  -- Since P = Pᵀ, both PᵀP and PPᵀ equal P². We prove P²=I.
  suffices hPP : ∀ i j : Fin n,
      ∑ k : Fin n, householder n v β i k * householder n v β k j =
        if i = j then 1 else 0 by
    exact ⟨fun i j => by rw [hsym]; exact hPP i j,
           fun i j => by rw [hsym]; exact hPP i j⟩
  intro i j
  simp only [householder]
  -- Goal: ∑_k (δ_{ik} - β v_i v_k)(δ_{kj} - β v_k v_j) = δ_{ij}
  -- Expand into four terms: T1 - T2 - T3 + T4
  have expand : ∀ k : Fin n,
      (idMatrix n i k - β * v i * v k) * (idMatrix n k j - β * v k * v j) =
      idMatrix n i k * idMatrix n k j - idMatrix n i k * (β * v k * v j) -
      β * v i * v k * idMatrix n k j + β * v i * v k * (β * v k * v j) := by
    intro k; ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- Compute each term:
  -- T1: ∑_k δ_{ik} δ_{kj} = δ_{ij}
  have T1 : ∑ k : Fin n, idMatrix n i k * idMatrix n k j = idMatrix n i j := by
    simp only [idMatrix, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  -- T2: ∑_k δ_{ik} (β v_k v_j) = β v_i v_j
  have T2 : ∑ k : Fin n, idMatrix n i k * (β * v k * v j) = β * v i * v j := by
    simp only [idMatrix, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  -- T3: ∑_k (β v_i v_k) δ_{kj} = β v_i v_j
  have T3 : ∑ k : Fin n, β * v i * v k * idMatrix n k j = β * v i * v j := by
    simp only [idMatrix, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  -- T4: ∑_k β² v_i v_k² v_j = β²(∑v²) v_i v_j
  have T4 : ∑ k : Fin n, β * v i * v k * (β * v k * v j) =
      β ^ 2 * v i * v j * ∑ k : Fin n, v k * v k := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  rw [T1, T2, T3, T4]
  -- idMatrix n i j - βv_iv_j - βv_iv_j + β²(∑v²)v_iv_j = δ_{ij}
  -- Use β(∑v²) = 2, so β²(∑v²) = 2β
  have hβ2 : β ^ 2 * (∑ k : Fin n, v k * v k) = 2 * β := by
    have : β ^ 2 * (∑ k, v k * v k) = β * (β * (∑ k, v k * v k)) := by ring
    rw [this, hβ]; ring
  rw [show β ^ 2 * v i * v j * ∑ k, v k * v k =
      v i * v j * (β ^ 2 * ∑ k, v k * v k) by ring, hβ2]
  -- idMatrix n i j + v_i * v_j * (-2β + 2β) = δ_{ij}
  unfold idMatrix; ring

-- ============================================================
-- §18.3  Lemma 18.2: Householder application backward error
-- ============================================================

/-- **Backward error model for Householder application** (Lemma 18.2).

    When a Householder matrix P is applied to a vector b in
    floating-point arithmetic, the computed result ŷ satisfies
    ŷ = (P + ΔP)b where ‖ΔP‖_F ≤ c.

    This axiomatizes the result of Lemma 18.2 since the detailed proof
    requires low-level FP analysis of the dot product + outer product
    computation pattern (Lemma 18.1 + eq 18.3). The bound c is
    typically γ̃_{cm} where c is a small constant and m = n. -/
structure HouseholderAppError (n : ℕ) (P : Fin n → Fin n → ℝ)
    (b y_hat : Fin n → ℝ) (c : ℝ) : Prop where
  /-- P is orthogonal. -/
  orth : IsOrthogonal n P
  /-- The computed result satisfies ŷ = (P + ΔP)b with ‖ΔP‖_F ≤ c. -/
  pert : ∃ ΔP : Fin n → Fin n → ℝ,
    frobNorm ΔP ≤ c ∧
    ∀ i, y_hat i = matMulVec n (fun a b => P a b + ΔP a b) b i

end LeanFpAnalysis.FP
