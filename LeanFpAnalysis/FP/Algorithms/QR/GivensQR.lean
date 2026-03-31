-- Algorithms/QR/GivensQR.lean
--
-- Backward error analysis for Givens QR factorization (Higham §18.5).
--
-- Lemma 18.8: A sequence of r Givens rotations with per-step error ≤ c
--   yields Â_{r+1} = Qᵀ(A + ΔA) with ‖ΔA‖_F ≤ r·c·‖A‖_F.
--
-- Theorem 18.9: Givens QR gives A + ΔA = Q·R̂ with ‖ΔA‖_F bounded.
--   For an n×n matrix, r = n(n-1)/2 Givens rotations are used.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.QR.GivensSpec
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §18.5  Lemma 18.8: Sequence of Givens rotations backward error
-- ============================================================

/-- **Backward error from a sequence of perturbed Givens rotations**
    (Lemma 18.8, normwise form).

    Given r Givens rotations G₁,...,Gᵣ, if each computed application
    satisfies ‖ΔGₖ‖_F ≤ c, then the product
    (Gᵣ + ΔGᵣ)···(G₁ + ΔG₁)A = Qᵀ(A + ΔA)
    where Q is orthogonal and ‖ΔA‖_F ≤ r·c·‖A‖_F.

    This is an instance of OrthogonalSequenceBackwardError since
    Givens rotations are orthogonal matrices and the accumulation
    mechanism is identical to Lemma 18.3 for Householder. -/
abbrev GivensSequenceBackwardError (n : ℕ) (A : Fin n → Fin n → ℝ)
    (A_hat : Fin n → Fin n → ℝ) (r : ℕ) (c : ℝ) :=
  OrthogonalSequenceBackwardError n A A_hat r c

-- ============================================================
-- §18.5  Theorem 18.9: Givens QR backward error
-- ============================================================

/-- **Theorem 18.9**: Givens QR factorization backward error (normwise).

    The computed R̂ from Givens QR satisfies A + ΔA = Q·R̂
    where Q is orthogonal and ‖ΔA‖_F ≤ c_bound.

    For an n×n matrix, r = n(n-1)/2 Givens rotations are used,
    each with per-step error ≤ √2·γ₆. The total bound is
    c_bound = r · √2·γ₆ · ‖A‖_F. -/
structure GivensQRBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (c_bound : ℝ) : Prop where
  /-- There exists an orthogonal Q such that A + ΔA = Q·R̂ with bounded ΔA. -/
  result : ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
    IsOrthogonal n Q ∧
    (∀ i j, matMul n Q R_hat i j = A i j + ΔA i j) ∧
    frobNorm ΔA ≤ c_bound

/-- Theorem 18.9 instantiation: r Givens rotations with per-step error ≤ c
    yield total backward error ≤ r · c · ‖A‖_F.

    The proof is identical to Theorem 18.4 since both use the same
    orthogonal sequence backward error structure (Lemma 18.3/18.8). -/
theorem givens_qr_backward (n : ℕ) (r : ℕ) (hr : 0 < r)
    (A R_hat : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hSeq : GivensSequenceBackwardError n A R_hat r c) :
    GivensQRBackwardError n A R_hat (↑r * c * frobNorm A) := by
  obtain ⟨Q, ΔA, hQ, hAhat, hbound⟩ := hSeq.result
  exact ⟨⟨Q, ΔA, hQ, by
    intro i j
    have hR : R_hat = matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) :=
      funext fun k => funext fun l => hAhat k l
    have hQQT : matMul n Q (matTranspose Q) = idMatrix n :=
      funext fun a => funext fun b => hQ.right_inv a b
    rw [hR, ← matMul_assoc, hQQT, matMul_id_left], hbound⟩⟩

end LeanFpAnalysis.FP
