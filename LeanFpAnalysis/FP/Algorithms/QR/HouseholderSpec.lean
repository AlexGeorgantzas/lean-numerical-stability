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

open scoped BigOperators Matrix.Norms.Frobenius

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

/-- Normalized vector corresponding to the unnormalized Householder form
    `I - beta * v * vᵀ`.

    If `0 ≤ beta`, then `sqrt(beta) * v` turns the reflector into the
    normalized form `I - w*wᵀ` used in Higham's equation (18.3). -/
noncomputable def householderNormalizedVector (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt beta * v i

/-- The normalized `beta = 1` Householder form is algebraically the same as
    the unnormalized `beta` form when `beta ≥ 0`. -/
theorem householder_normalizedVector_eq (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    householder n (householderNormalizedVector n v beta) 1 =
      householder n v beta := by
  ext i j
  unfold householder householderNormalizedVector
  have hsqrt : Real.sqrt beta * Real.sqrt beta = beta :=
    Real.mul_self_sqrt hbeta
  rw [show 1 * (Real.sqrt beta * v i) * (Real.sqrt beta * v j) =
      beta * v i * v j by
    calc
      1 * (Real.sqrt beta * v i) * (Real.sqrt beta * v j)
          = (Real.sqrt beta * Real.sqrt beta) * v i * v j := by ring
      _ = beta * v i * v j := by rw [hsqrt]]

/-- If `beta * (vᵀv) = 2`, then the normalized Householder vector has
    squared 2-norm equal to `2`. -/
theorem householderNormalizedVector_norm_sq (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (hbeta_nonneg : 0 ≤ beta)
    (hbeta : beta * (∑ i : Fin n, v i * v i) = 2) :
    (∑ i : Fin n,
      householderNormalizedVector n v beta i *
        householderNormalizedVector n v beta i) = 2 := by
  unfold householderNormalizedVector
  have hsqrt : Real.sqrt beta * Real.sqrt beta = beta :=
    Real.mul_self_sqrt hbeta_nonneg
  calc
    (∑ i : Fin n, (Real.sqrt beta * v i) * (Real.sqrt beta * v i))
        = ∑ i : Fin n, beta * (v i * v i) := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            (Real.sqrt beta * v i) * (Real.sqrt beta * v i)
                = (Real.sqrt beta * Real.sqrt beta) * (v i * v i) := by ring
            _ = beta * (v i * v i) := by rw [hsqrt]
    _ = beta * (∑ i : Fin n, v i * v i) := by
          rw [Finset.mul_sum]
    _ = 2 := hbeta

-- ============================================================
-- §18.3  Lemma 18.2: Householder application backward error
-- ============================================================

/-- **Householder vector perturbation model** (Higham equation 18.3).

    After Lemma 18.1, Higham rewrites Householder matrices in the normalized
    form `P = I - v vᵀ`, where `‖v‖₂ = sqrt 2`, and assumes the computed vector
    satisfies `v_hat = v + Δv` with componentwise bound
    `|Δv| ≤ eps |v|`.  In the book, `eps` is written as a generic
    `γ_{cm}` constant.

    This structure is the precise intermediate contract that should be proved
    from the concrete `fl_householderVector` construction before proving the
    `HouseholderAppError` bridge below. -/
structure HouseholderVectorError (n : ℕ) (v v_hat : Fin n → ℝ)
    (eps : ℝ) : Prop where
  /-- Normalized Householder-vector convention: `‖v‖₂² = 2`. -/
  norm_sq : (∑ i : Fin n, v i * v i) = 2
  /-- Computed vector is a componentwise small perturbation of the exact vector. -/
  pert : ∃ Δv : Fin n → ℝ,
    (∀ i, v_hat i = v i + Δv i) ∧
    ∀ i, |Δv i| ≤ eps * |v i|

/-- **Backward error model for Householder application** (Lemma 18.2).

    When a Householder matrix P is applied to a vector b in
    floating-point arithmetic, the computed result ŷ satisfies
    ŷ = (P + ΔP)b where ‖ΔP‖_F ≤ c.

    Lemma 18.2 assumes the computed Householder vector satisfies
    `HouseholderVectorError` above, then analyzes the dot-product and vector
    update computation.  Until the concrete bridge from `fl_householderVector`
    and `fl_householderApply` is proved, this structure is a specification
    interface rather than an end-to-end result.  The bound c is typically
    a generic `γ_{cm}` where c is a small integer and m = n. -/
structure HouseholderAppError (n : ℕ) (P : Fin n → Fin n → ℝ)
    (b y_hat : Fin n → ℝ) (c : ℝ) : Prop where
  /-- P is orthogonal. -/
  orth : IsOrthogonal n P
  /-- The computed result satisfies ŷ = (P + ΔP)b with ‖ΔP‖_F ≤ c. -/
  pert : ∃ ΔP : Fin n → Fin n → ℝ,
    frobNorm ΔP ≤ c ∧
    ∀ i, y_hat i = matMulVec n (fun a b => P a b + ΔP a b) b i

end LeanFpAnalysis.FP
