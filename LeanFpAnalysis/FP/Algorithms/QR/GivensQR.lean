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
import LeanFpAnalysis.FP.Algorithms.QR.GivensMatrixStep
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

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
    GivensQRBackwardError n A R_hat
      (↑r * c * frobNorm A) := by
  obtain ⟨Q, ΔA, hQ, hAhat, hbound⟩ := hSeq.result
  exact ⟨⟨Q, ΔA, hQ, by
    intro i j
    have hR : R_hat = matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) :=
      funext fun k => funext fun l => hAhat k l
    have hQQT : matMul n Q (matTranspose Q) = idMatrix n :=
      funext fun a => funext fun b => hQ.right_inv a b
    rw [hR, ← matMul_assoc, hQQT, matMul_id_left], hbound⟩⟩

/-- Repeated concrete computed-coefficient Givens matrix applications.

    This theorem is the implementation-backed sequence bridge below the full
    Givens QR loop.  It does not choose the QR annihilation schedule.  Instead,
    it assumes a concrete matrix sequence whose step `k` is exactly
    `fl_givensApplyMatrix` with the supplied row pair and two-vector used to
    construct the rotation coefficients.  Each step is proved from the concrete
    `fl_givensC`/`fl_givensS`/`fl_givensApply` kernels, then accumulated by the
    generic residual-form orthogonal sequence theorem. -/
theorem fl_givens_sequence_backward_error (fp : FPModel) {n r : ℕ}
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (pseq qseq : ℕ → Fin n)
    (xiseq xjseq : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hstep_bound : ∀ k : ℕ, k < r →
      gamma fp 8 *
        frobNorm (givensRotation n (pseq k) (qseq k)
          (givensC (xiseq k) (xjseq k))
          (givensS (xiseq k) (xjseq k))) ≤ c)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrix fp n (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  let Pseq : ℕ → Fin n → Fin n → ℝ := fun k =>
    givensRotation n (pseq k) (qseq k)
      (givensC (xiseq k) (xjseq k))
      (givensS (xiseq k) (xjseq k))
  apply residual_orthogonal_sequence_backward_error n r Aseq Pseq c hc
  · intro k hk
    exact givensRotation_constructed_orthogonal n (pseq k) (qseq k)
      (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
  · intro k hk
    have hraw :=
      fl_givensApply_computed_matrix_step_error fp n (pseq k) (qseq k)
        (xiseq k) (xjseq k) (Aseq k) (hpq k hk) (hnz k hk) hvalid
    have hcstep : 0 ≤
        gamma fp 8 *
          frobNorm (givensRotation n (pseq k) (qseq k)
            (givensC (xiseq k) (xjseq k))
            (givensS (xiseq k) (xjseq k))) := by
      exact mul_nonneg (gamma_nonneg fp hvalid) (frobNorm_nonneg _)
    obtain ⟨E, hNext, hE⟩ := hraw.exists_residual_matrix_bound hcstep
    refine ⟨E, ?_, ?_⟩
    · intro i j
      rw [hAstep k hk]
      simpa [Pseq] using hNext i j
    · exact le_trans hE
        (mul_le_mul_of_nonneg_right (hstep_bound k hk)
          (frobNorm_nonneg (Aseq k)))

/-- Uniform-bound corollary for repeated computed Givens matrix applications.

    Since every exact Givens rotation is orthogonal, its Frobenius norm is
    `sqrt n`.  This removes the explicit per-step bound assumption from
    `fl_givens_sequence_backward_error`, while keeping the conservative
    `gamma fp 8` constant inherited from the computed-coefficient bridge. -/
theorem fl_givens_sequence_backward_error_uniform (fp : FPModel) {n r : ℕ}
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (pseq qseq : ℕ → Fin n)
    (xiseq xjseq : ℕ → ℝ)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrix fp n (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (n : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_sequence_backward_error fp Aseq pseq qseq xiseq xjseq
    (gamma fp 8 * Real.sqrt (n : ℝ))
  · exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  · exact hpq
  · exact hnz
  · exact hvalid
  · intro k hk
    have hG :=
      givensRotation_constructed_orthogonal n (pseq k) (qseq k)
        (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
    rw [hG.frobNorm_eq_sqrt_card]
  · exact hAstep

/-- Uniform-bound sequence theorem for concrete Givens column steps.

    Compared with `fl_givens_sequence_backward_error_uniform`, this theorem
    obtains each rotation's two-vector from the current matrix column
    `(Aseq k (pseq k) (colseq k), Aseq k (qseq k) (colseq k))`.  This is one
    layer closer to a full Givens QR loop; the remaining missing piece is the
    actual annihilation schedule and triangular-shape proof. -/
theorem fl_givens_column_sequence_backward_error_uniform (fp : FPModel)
    {n r : ℕ}
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (pseq qseq colseq : ℕ → Fin n)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r →
      Aseq k (pseq k) (colseq k) ^ 2 +
        Aseq k (qseq k) (colseq k) ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensColumnStepMatrix fp n (pseq k) (qseq k)
          (colseq k) (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (n : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_sequence_backward_error_uniform fp Aseq pseq qseq
    (fun k => Aseq k (pseq k) (colseq k))
    (fun k => Aseq k (qseq k) (colseq k)) hpq hnz hvalid
  intro k hk
  simpa [fl_givensColumnStepMatrix] using hAstep k hk

/-- Rectangular-panel version of `fl_givens_sequence_backward_error`. -/
theorem fl_givens_panel_sequence_backward_error (fp : FPModel)
    {m cols r : ℕ}
    (Aseq : ℕ → Fin m → Fin cols → ℝ)
    (pseq qseq : ℕ → Fin m)
    (xiseq xjseq : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hstep_bound : ∀ k : ℕ, k < r →
      gamma fp 8 *
        frobNorm (givensRotation m (pseq k) (qseq k)
          (givensC (xiseq k) (xjseq k))
          (givensS (xiseq k) (xjseq k))) ≤ c)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrixRect fp m cols (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin cols → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  let Pseq : ℕ → Fin m → Fin m → ℝ := fun k =>
    givensRotation m (pseq k) (qseq k)
      (givensC (xiseq k) (xjseq k))
      (givensS (xiseq k) (xjseq k))
  apply residual_orthogonal_sequence_backward_error_rect m cols r Aseq Pseq c hc
  · intro k hk
    exact givensRotation_constructed_orthogonal m (pseq k) (qseq k)
      (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
  · intro k hk
    have hraw :=
      fl_givensApply_computed_matrix_step_error_rect fp m cols
        (pseq k) (qseq k) (xiseq k) (xjseq k) (Aseq k)
        (hpq k hk) (hnz k hk) hvalid
    have hcstep : 0 ≤
        gamma fp 8 *
          frobNorm (givensRotation m (pseq k) (qseq k)
            (givensC (xiseq k) (xjseq k))
            (givensS (xiseq k) (xjseq k))) := by
      exact mul_nonneg (gamma_nonneg fp hvalid) (frobNorm_nonneg _)
    obtain ⟨E, hNext, hE⟩ := hraw.exists_residual_matrix_bound hcstep
    refine ⟨E, ?_, ?_⟩
    · intro i j
      rw [hAstep k hk]
      simpa [Pseq] using hNext i j
    · exact le_trans hE
        (mul_le_mul_of_nonneg_right (hstep_bound k hk)
          (frobNorm_nonneg (Aseq k)))

/-- Uniform-bound rectangular-panel corollary for repeated computed Givens
    applications. -/
theorem fl_givens_panel_sequence_backward_error_uniform (fp : FPModel)
    {m cols r : ℕ}
    (Aseq : ℕ → Fin m → Fin cols → ℝ)
    (pseq qseq : ℕ → Fin m)
    (xiseq xjseq : ℕ → ℝ)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r → xiseq k ^ 2 + xjseq k ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensApplyMatrixRect fp m cols (pseq k) (qseq k)
          (xiseq k) (xjseq k) (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin cols → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (m : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_panel_sequence_backward_error fp Aseq pseq qseq xiseq xjseq
    (gamma fp 8 * Real.sqrt (m : ℝ))
  · exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)
  · exact hpq
  · exact hnz
  · exact hvalid
  · intro k hk
    have hG :=
      givensRotation_constructed_orthogonal m (pseq k) (qseq k)
        (xiseq k) (xjseq k) (hpq k hk) (hnz k hk)
    rw [hG.frobNorm_eq_sqrt_card]
  · exact hAstep

/-- Uniform-bound rectangular-panel sequence theorem for concrete Givens
    column steps. -/
theorem fl_givens_column_panel_sequence_backward_error_uniform (fp : FPModel)
    {m cols r : ℕ}
    (Aseq : ℕ → Fin m → Fin cols → ℝ)
    (pseq qseq : ℕ → Fin m)
    (colseq : ℕ → Fin cols)
    (hpq : ∀ k : ℕ, k < r → pseq k ≠ qseq k)
    (hnz : ∀ k : ℕ, k < r →
      Aseq k (pseq k) (colseq k) ^ 2 +
        Aseq k (qseq k) (colseq k) ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8)
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_givensColumnStepMatrixRect fp m cols (pseq k) (qseq k)
          (colseq k) (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin cols → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin cols), Aseq r i j =
        matMulRect m m cols (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (gamma fp 8 * Real.sqrt (m : ℝ)) r *
          frobNorm (Aseq 0) := by
  apply fl_givens_panel_sequence_backward_error_uniform fp Aseq pseq qseq
    (fun k => Aseq k (pseq k) (colseq k))
    (fun k => Aseq k (qseq k) (colseq k)) hpq hnz hvalid
  intro k hk
  simpa [fl_givensColumnStepMatrixRect] using hAstep k hk

end LeanFpAnalysis.FP
