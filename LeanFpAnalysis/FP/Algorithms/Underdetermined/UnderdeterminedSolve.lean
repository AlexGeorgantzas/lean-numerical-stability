-- Algorithms/Underdetermined/UnderdeterminedSolve.lean
--
-- Error analysis of solution methods for underdetermined systems
-- (Higham §21.3).
--
-- Q method (Theorem 21.4): backward stable; currently represented by
-- an abstract Gram-system predicate while the rectangular QR bridge is open.
-- The full source theorem requires rectangular QR.
--
-- SNE method: solves RᵀRy = b via Cholesky-like approach. The
-- backward error is proved by composing with existing Cholesky
-- solve results. The forward error (eq. 21.11) follows from
-- normwise_perturbation_bound (Theorem 7.2).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.PerturbationTheory
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySolve
import LeanFpAnalysis.FP.Algorithms.Underdetermined.UnderdeterminedSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================

/-- **Theorem 21.4** (Higham): The Q method for underdetermined systems
    is row-wise backward stable.

    The Q method solves Rᵀy₁ = b and forms x = Q[y₁; 0]ᵀ using
    the QR factorization Aᵀ = Q[R; 0]. The computed x̂ is the
    minimum 2-norm solution to (A + ΔA)x = b, where:

    ‖ΔA‖_F ≤ mγ_{cn}‖A‖_F  (normwise)
    |ΔA| ≤ mnγ_{cn}|A|G, ‖G‖_F = 1  (componentwise)

    Note: b is not perturbed (unlike the least-squares QR result in
    Theorem 20.3).

    Recorded as an abstract predicate until the rectangular QR factorization
    bridge and Lemma 21.2 symmetrization route are fully formalized. -/
structure QMethodBackwardStable (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b y_hat : Fin m → ℝ)
    (c_bound : ℝ) : Prop where
  /-- c_bound is nonneg. -/
  bound_nonneg : 0 ≤ c_bound
  /-- The computed ŷ satisfies perturbed normal equations
      (AAᵀ + ΔG)ŷ = b with bounded ΔG.
      This captures the Q method's backward stability projected
      to the m×m Gram system AAᵀ. -/
  result : ∃ (ΔG : Fin m → Fin m → ℝ),
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) y_hat i = b i) ∧
    frobNorm ΔG ≤ c_bound

-- ============================================================
-- §21.3  SNE method backward error
-- ============================================================

/-- **SNE method backward error for underdetermined systems** (Higham §21.3).

    The SNE method solves RᵀRy = b where Aᵀ = Q[R; 0], then forms
    x = Aᵀy. The solve RᵀRy = b is equivalent to Cholesky-solving
    the m×m system AAᵀy = b (since AAᵀ = RᵀR for the exact R).

    The backward error of the Cholesky solve gives:
    (RᵀR + ΔC)ŷ = b where |ΔC| ≤ (γ(m+1) + 2γ(m) + γ(m)²)·|R̂ᵀ||R̂|

    This is a direct application of `cholesky_solve_backward_error_expanded`
    from CholeskySolve.lean with n := m (the Gram matrix is m×m). -/
theorem sne_backward_error (fp : FPModel) (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1)) :
    let R_hatT := fun i j : Fin m => R_hat j i
    let y_hat := fl_forwardSub fp m R_hatT b
    let x_hat := fl_backSub fp m R_hat y_hat
    ∃ ΔC : Fin m → Fin m → ℝ,
      (∀ i j, |ΔC i j| ≤
        (gamma fp (m + 1) + 2 * gamma fp m + gamma fp m ^ 2) *
          ∑ k : Fin m, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * x_hat j = b i) :=
  cholesky_solve_backward_error_expanded fp m AAT R_hat b hR_diag hChol hm1

-- ============================================================
-- §21.3  Forward error bound (eq. 21.11)
-- ============================================================

/-- **Forward error for underdetermined system solve** (Higham §21.3, eq. 21.11).

    For both the Q method and SNE method, the forward error satisfies:
    ‖x̂ − x‖₂/‖x‖₂ ≤ mnγ'_{cn} · cond₂(A) + O(u²)

    where cond₂(A) = ‖|A⁺||A|‖₂. Note this bound is independent
    of the row scaling of A.

    We prove the componentwise form: given backward error in the
    m×m Gram system, the forward error is bounded by
    |ŷ − y| ≤ |(AAᵀ)⁻¹| · |ΔG · ŷ|.

    This reuses `normwise_perturbation_bound` (Theorem 7.2) from
    PerturbationTheory.lean, noting that Δb = 0 for the Q method
    (the right-hand side b is not perturbed). -/
theorem underdetermined_forward_error (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| := by
  -- Since Δb = 0, the bound from Theorem 7.2 simplifies to
  -- |ŷ − y| ≤ |(AAᵀ)⁻¹| · (|ΔG|·|ŷ| + 0)
  -- We apply normwise_perturbation_bound with Δb := 0.
  let Δb : Fin m → ℝ := fun _ => 0
  have hPerturbed' : ∀ i, ∑ j, (AAT i j + ΔG i j) * y_hat j = b i + Δb i := by
    intro i; simp [Δb]; exact hPerturbed i
  have hExact' : ∀ i, ∑ j, AAT i j * y j = b i := fun i => hExact i
  have hBound := normwise_perturbation_bound m AAT AAT_inv y y_hat b ΔG Δb
    hInv.1 hExact' hPerturbed'
  intro i
  rw [abs_sub_comm]
  have h := hBound i
  -- Simplify: |Δb_j| = 0, so ∑|ΔG|·|ŷ| + |Δb| = ∑|ΔG|·|ŷ| + 0
  calc |y i - y_hat i|
      ≤ ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + |Δb j|) := h
    _ = ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + 0) := by
        simp [Δb]
    _ = ∑ j, |AAT_inv i j| * ∑ k, |ΔG j k| * |y_hat k| := by
        apply Finset.sum_congr rfl; intro j _; ring_nf

/-- **SNE method is NOT backward stable** (Higham §21.3, remark).

    Unlike the Q method (Theorem 21.4), the SNE method does not
    guarantee that x̂ is the minimum 2-norm solution to a nearby
    system. The SNE only guarantees a small residual in the normal
    equations RᵀRŷ ≈ b.

    However, both methods achieve the same forward error bound (eq. 21.11):
    ‖x̂−x‖₂/‖x‖₂ ≤ mnγ'_{cn} · cond₂(A) + O(u²)

    This means the forward error from SNE is as good as from Q method,
    even though the backward error characterization is weaker. -/
theorem sne_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| := by
  -- Same proof as underdetermined_forward_error: apply Theorem 7.2 with Δb = 0
  have hPert' : ∀ i, matMulVec m (fun a c => AAT a c + ΔC a c) y_hat i = b i :=
    fun i => hPerturbed i
  exact underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔC hPert'

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.11):
    source-facing wrapper for the currently formalized Gram-system forward
    perturbation consequence.  This is not the full printed asymptotic
    `mn * gamma * cond_2(A) + O(u^2)` bound; it is the exact componentwise
    perturbation inequality used as a dependency for that row. -/
theorem higham21_eq21_11_gram_forward_error
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed :
      ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| :=
  underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔG hPerturbed

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    source-facing wrapper for the proved statement that the SNE Gram-system
    perturbation route has the same componentwise forward-error consequence as
    the Q-method Gram-system route.  The full source statement still requires
    instantiating the QR/SNE computed-object bounds. -/
theorem higham21_sne_gram_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| :=
  sne_forward_error_matches_q_method m AAT AAT_inv hInv b y y_hat hExact ΔC
    hPerturbed

end LeanFpAnalysis.FP
