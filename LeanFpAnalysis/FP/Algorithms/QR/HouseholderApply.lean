-- Algorithms/QR/HouseholderApply.lean
--
-- Concrete floating-point application of a Householder reflector.
--
-- This file is the first bridge from the QR contracts in HouseholderSpec.lean
-- toward implementation-backed QR stability results.  It keeps the existing
-- Higham-style contracts unchanged and exposes the actual rounded computation
-- used for applying P = I - βvvᵀ to a vector b:
--
--   σ̂ = fl(vᵀ b)
--   τ̂ = fl(β σ̂)
--   ŷᵢ = fl(bᵢ - fl(τ̂ vᵢ)).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Algorithms.DotProduct
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §18.1  Concrete rounded Householder application
-- ============================================================

/-- Floating-point application of the Householder reflector `I - βvvᵀ` to `b`.

    The operation order follows the usual compact Householder application:

      σ̂ = fl(vᵀ b)
      τ̂ = fl(β σ̂)
      ŷᵢ = fl(bᵢ - fl(τ̂ vᵢ))

    The vector `v` and scalar `β` are assumed already chosen.  The lower-level
    reflector-construction helpers live in `HouseholderReflector.lean`; this
    file focuses only on applying a supplied reflector. -/
noncomputable def fl_householderApply (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  let σ := fl_dotProduct fp n v b
  let τ := fp.fl_mul β σ
  fun i => fp.fl_sub (b i) (fp.fl_mul τ (v i))

/-- Unrolled rounding-error form for `fl_householderApply`.

    This theorem is intentionally local: it records the exact rounded operation
    order without claiming the final Higham Lemma 18.2 Frobenius-norm bound.
    It is the low-level fact needed before proving that the concrete
    implementation satisfies `HouseholderAppError` with the book's bound. -/
theorem fl_householderApply_unroll (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ (η : Fin n → ℝ) (δτ : ℝ) (δmul δsub : Fin n → ℝ),
      (∀ j : Fin n, |η j| ≤ gamma fp n) ∧
      |δτ| ≤ fp.u ∧
      (∀ i : Fin n, |δmul i| ≤ fp.u) ∧
      (∀ i : Fin n, |δsub i| ≤ fp.u) ∧
      ∀ i : Fin n,
        fl_householderApply fp n v β b i =
          (b i -
            (β * (∑ j : Fin n, v j * b j * (1 + η j))) *
              (1 + δτ) * v i * (1 + δmul i)) *
            (1 + δsub i) := by
  obtain ⟨η, hη, hdot⟩ := dotProduct_backward_error fp n v b hn
  let σ := fl_dotProduct fp n v b
  let δτ : ℝ := Classical.choose (fp.model_mul β σ)
  have hδτ :
      |δτ| ≤ fp.u ∧ fp.fl_mul β σ = β * σ * (1 + δτ) :=
    Classical.choose_spec (fp.model_mul β σ)
  let τ := fp.fl_mul β σ
  let δmul : Fin n → ℝ := fun i => Classical.choose (fp.model_mul τ (v i))
  have hδmul : ∀ i : Fin n,
      |δmul i| ≤ fp.u ∧ fp.fl_mul τ (v i) = τ * v i * (1 + δmul i) :=
    fun i => Classical.choose_spec (fp.model_mul τ (v i))
  let δsub : Fin n → ℝ :=
    fun i => Classical.choose (fp.model_sub (b i) (fp.fl_mul τ (v i)))
  have hδsub : ∀ i : Fin n,
      |δsub i| ≤ fp.u ∧
        fp.fl_sub (b i) (fp.fl_mul τ (v i)) =
          (b i - fp.fl_mul τ (v i)) * (1 + δsub i) :=
    fun i => Classical.choose_spec (fp.model_sub (b i) (fp.fl_mul τ (v i)))
  refine ⟨η, δτ, δmul, δsub, hη, hδτ.1,
    (fun i => (hδmul i).1), (fun i => (hδsub i).1), ?_⟩
  intro i
  unfold fl_householderApply
  change fp.fl_sub (b i) (fp.fl_mul τ (v i)) = _
  rw [(hδsub i).2, (hδmul i).2]
  rw [show τ = fp.fl_mul β σ by rfl, hδτ.2]
  rw [show σ = fl_dotProduct fp n v b by rfl, hdot]

/-- Exact matrix-perturbation representation for `fl_householderApply`.

    This proves the algebraic heart of `HouseholderAppError`: the concrete
    rounded application can be written as the exact application of
    `householder n v β + ΔP` to `b`.  The theorem deliberately does not yet
    prove a Higham Lemma 18.2 norm bound on `ΔP`; that is the next layer. -/
theorem fl_householderApply_matrix_perturbation (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ ΔP : Fin n → Fin n → ℝ,
      ∀ i : Fin n,
        fl_householderApply fp n v β b i =
          matMulVec n (fun a j => householder n v β a j + ΔP a j) b i := by
  obtain ⟨η, δτ, δmul, δsub, _hη, _hδτ, _hδmul, _hδsub, happly⟩ :=
    fl_householderApply_unroll fp n v β b hn
  let ΔP : Fin n → Fin n → ℝ := fun i j =>
    idMatrix n i j * δsub i -
      β * v i * v j *
        ((1 + δτ) * (1 + δmul i) * (1 + δsub i) * (1 + η j) - 1)
  refine ⟨ΔP, ?_⟩
  intro i
  rw [happly i]
  unfold matMulVec
  have hterm : ∀ j : Fin n,
      (householder n v β i j + ΔP i j) * b j =
        idMatrix n i j * b j * (1 + δsub i) -
          (β * v i * ((1 + δτ) * (1 + δmul i) * (1 + δsub i))) *
            (v j * b j * (1 + η j)) := by
    intro j
    unfold householder ΔP
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have hid : ∑ j : Fin n, idMatrix n i j * b j = b i := by
    exact congr_fun (idMatrix_mulVec n b) i
  have hleft :
      ∑ j : Fin n, idMatrix n i j * b j * (1 + δsub i) =
        b i * (1 + δsub i) := by
    rw [← Finset.sum_mul, hid]
  have hright :
      ∑ j : Fin n,
          (β * v i * ((1 + δτ) * (1 + δmul i) * (1 + δsub i))) *
            (v j * b j * (1 + η j)) =
        (β * (∑ j : Fin n, v j * b j * (1 + η j))) *
          (1 + δτ) * v i * (1 + δmul i) * (1 + δsub i) := by
    rw [← Finset.mul_sum]
    ring
  rw [hleft, hright]
  ring

/-- The concrete rounded Householder application satisfies the existing
    application contract with its actual perturbation norm as the bound.

    This is not yet Higham's closed-form Lemma 18.2 bound.  It is the bridge
    showing that the contract is now connected to a real implementation rather
    than being only an external assumption. -/
theorem fl_householderApply_appError_actualBound (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (horth : IsOrthogonal n (householder n v β)) :
    ∃ c : ℝ,
      HouseholderAppError n (householder n v β) b
        (fl_householderApply fp n v β b) c := by
  obtain ⟨ΔP, hΔP⟩ :=
    fl_householderApply_matrix_perturbation fp n v β b hn
  exact ⟨frobNorm ΔP, ⟨horth, ⟨ΔP, le_rfl, hΔP⟩⟩⟩

end LeanFpAnalysis.FP
