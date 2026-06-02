-- Algorithms/QR/HouseholderQR.lean
--
-- Backward error analysis for Householder QR factorization (Higham §18.3).
--
-- Lemma 18.3: r orthogonal transformations with per-step error ≤ c give
--   Â_{r+1} = Qᵀ(A + ΔA) with ‖ΔA‖_F ≤ r·c·‖A‖_F (normwise).
--
-- Theorem 18.4: Householder QR gives A + ΔA = Q·R̂ with
--   ‖ΔA‖_F ≤ n·c·‖A‖_F where c = γ̃_{cm}.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpec
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderMatrixStep

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §18.3  Lemma 18.3: Sequence of orthogonal transformations
-- ============================================================

/-- **Backward error from a sequence of perturbed orthogonal transformations**
    (Lemma 18.3, normwise form).

    Given a sequence of r orthogonal matrices P₁,...,Pᵣ, if each computed
    application satisfies ‖ΔPₖ‖_F ≤ c, then the product
    (Pᵣ + ΔPᵣ)···(P₁ + ΔP₁)A = Qᵀ(A + ΔA)
    where Q = P₁ᵀ···Pᵣᵀ is orthogonal and ‖ΔA‖_F ≤ r·c·‖A‖_F
    (to first order in c, assuming r·c < 1).

    This structure records the final sequence-level conclusion.  The residual
    one-step bridge below is now proved, but the repeated concrete QR loop still
    has to be connected to this structure by an induction over reflectors. -/
structure OrthogonalSequenceBackwardError (n : ℕ) (A : Fin n → Fin n → ℝ)
    (A_hat : Fin n → Fin n → ℝ) (r : ℕ) (c : ℝ) : Prop where
  /-- There exist an orthogonal Q and perturbation ΔA such that
      Â = Qᵀ(A + ΔA) with ‖ΔA‖_F ≤ r·c·‖A‖_F. -/
  result : ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
    IsOrthogonal n Q ∧
    (∀ i j, A_hat i j =
      matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
    frobNorm ΔA ≤
      ↑r * c * frobNorm A

/-- **Single-step backward error accumulation** (Lemma 18.3 engine).

    If Â = Qᵀ(A + ΔA) with ‖ΔA‖_F ≤ c₁·‖A‖_F, and we apply
    one more perturbed orthogonal transformation (P + ΔP) with
    ‖ΔP‖_F ≤ c₂, then the result is Q'ᵀ(A + ΔA') with
    ‖ΔA'‖_F ≤ ‖ΔA‖_F + c₂·‖A + ΔA‖_F.

    To first order (ignoring c₁·c₂ terms), this gives additive
    accumulation: ‖ΔA‖_F grows by c₂·‖A‖_F per step.

    Proof: Set Q' = Q·Pᵀ and ΔA' = ΔA + Q'·ΔP·Â. Then
    Q'ᵀ(A+ΔA') = P·Qᵀ·(B+E) = P·Â + ΔP·Â = (P+ΔP)·Â = A_next,
    and ‖ΔA'‖_F ≤ ‖ΔA‖_F + ‖Q'·ΔP·Â‖_F = ‖ΔA‖_F + ‖ΔP‖_F·‖Â‖_F
    = ‖ΔA‖_F + ‖ΔP‖_F·‖B‖_F ≤ ‖ΔA‖_F + c₂·‖B‖_F. -/
theorem orthogonal_sequence_one_step (n : ℕ)
    (A A_hat : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hAhat : ∀ i j, A_hat i j =
      matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) i j)
    (P : Fin n → Fin n → ℝ) (ΔP : Fin n → Fin n → ℝ)
    (hP : IsOrthogonal n P)
    (hΔP : frobNorm ΔP ≤ c_step)
    (_hc_step : 0 ≤ c_step)
    (A_next : Fin n → Fin n → ℝ)
    (hNext : ∀ i j, A_next i j =
      matMul n (fun a b => P a b + ΔP a b) A_hat i j) :
    ∃ (Q' : Fin n → Fin n → ℝ) (ΔA' : Fin n → Fin n → ℝ),
      IsOrthogonal n Q' ∧
      (∀ i j, A_next i j =
        matMul n (matTranspose Q') (fun a b => A a b + ΔA' a b) i j) ∧
      frobNorm ΔA' ≤
        frobNorm ΔA +
          c_step * frobNorm (fun a b => A a b + ΔA a b) := by
  -- Witnesses: Q' = Q·Pᵀ, ΔA' = ΔA + E where E = Q'·ΔP·Â
  let Q' := matMul n Q (matTranspose P)
  let B : Fin n → Fin n → ℝ := fun a b => A a b + ΔA a b
  let E : Fin n → Fin n → ℝ := matMul n (matMul n Q' ΔP) A_hat
  let ΔA' : Fin n → Fin n → ℝ := fun a b => ΔA a b + E a b
  -- Key lemmas
  have hQ' : IsOrthogonal n Q' := hQ.mul hP.transpose
  have hÂ : A_hat = matMul n (matTranspose Q) B :=
    funext fun k => funext fun l => hAhat k l
  have hQ'inv : matMul n (matTranspose Q') Q' = idMatrix n :=
    funext fun a => funext fun b => hQ'.left_inv a b
  -- Q'ᵀ = (Q·Pᵀ)ᵀ = P·Qᵀ
  have hQ'T : matTranspose Q' = matMul n P (matTranspose Q) := by
    show matTranspose (matMul n Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  -- Q'ᵀ · B = P · Â (since Q'ᵀ B = P Qᵀ B = P Â)
  have eq1 : matMul n (matTranspose Q') B = matMul n P A_hat := by
    rw [hQ'T, matMul_assoc, ← hÂ]
  -- Q'ᵀ · E = ΔP · Â (since Q'ᵀ Q' = I)
  have eq2 : matMul n (matTranspose Q') E = matMul n ΔP A_hat := by
    show matMul n (matTranspose Q') (matMul n (matMul n Q' ΔP) A_hat) = _
    rw [← matMul_assoc, ← matMul_assoc, hQ'inv, matMul_id_left]
  use Q', ΔA'
  refine ⟨hQ', ?_, ?_⟩
  · -- Representation: A_next = Q'ᵀ(A + ΔA')
    -- (P+ΔP)·Â = P·Â + ΔP·Â = Q'ᵀB + Q'ᵀE = Q'ᵀ(B+E) = Q'ᵀ(A+ΔA')
    have hBE : (fun a b => A a b + ΔA' a b) = fun a b => B a b + E a b :=
      funext fun a => funext fun b =>
        show A a b + (ΔA a b + E a b) = (A a b + ΔA a b) + E a b from by ring
    intro i j; rw [hNext i j, hBE]
    calc matMul n (fun a b => P a b + ΔP a b) A_hat i j
        = matMul n P A_hat i j + matMul n ΔP A_hat i j :=
          congr_fun (congr_fun (matMul_add_left n P ΔP A_hat) i) j
      _ = matMul n (matTranspose Q') B i j + matMul n (matTranspose Q') E i j := by
          rw [← congr_fun (congr_fun eq1 i) j, ← congr_fun (congr_fun eq2 i) j]
      _ = matMul n (matTranspose Q') (fun a b => B a b + E a b) i j :=
          (congr_fun (congr_fun (matMul_add_right n (matTranspose Q') B E) i) j).symm
  · -- Bound: ‖ΔA'‖_F ≤ ‖ΔA‖_F + c_step · ‖B‖_F
    show frobNorm (fun a b => ΔA a b + E a b) ≤
      frobNorm ΔA +
        c_step * frobNorm B
    have hfE :
        frobNorm E =
          frobNorm (matMul n ΔP A_hat) := by
      show frobNorm (matMul n (matMul n Q' ΔP) A_hat) = _
      rw [matMul_assoc]; exact frobNorm_orthogonal_left Q' _ hQ'
    have hfÂ :
        frobNorm A_hat =
          frobNorm B := by
      rw [hÂ]; exact frobNorm_orthogonal_left (matTranspose Q) B hQ.transpose
    calc frobNorm (fun a b => ΔA a b + E a b)
        ≤ frobNorm ΔA +
            frobNorm E := frobNorm_add_le ΔA E
      _ = frobNorm ΔA +
            frobNorm (matMul n ΔP A_hat) := by
          rw [hfE]
      _ ≤ frobNorm ΔA +
            frobNorm ΔP *
              frobNorm A_hat := by
          linarith [frobNorm_matMul_le ΔP A_hat]
      _ = frobNorm ΔA +
            frobNorm ΔP *
              frobNorm B := by rw [hfÂ]
      _ ≤ frobNorm ΔA +
            c_step * frobNorm B := by
          linarith [mul_le_mul_of_nonneg_right hΔP (frobNorm_nonneg B)]

/-- **Residual-form single-step backward error accumulation**.

    This is the one-step engine needed after columnwise Householder
    perturbations have been aggregated to a single residual matrix `E`.
    Compared with `orthogonal_sequence_one_step`, this theorem does not require
    one global perturbation matrix `ΔP` satisfying
    `A_next = (P + ΔP) A_hat`.  It only needs the weaker and source-aligned
    residual form `A_next = P A_hat + E` with `‖E‖_F ≤ c_step‖A_hat‖_F`. -/
theorem orthogonal_sequence_one_step_of_residual (n : ℕ)
    (A A_hat : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hAhat : ∀ i j, A_hat i j =
      matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) i j)
    (P : Fin n → Fin n → ℝ)
    (hP : IsOrthogonal n P)
    (A_next E : Fin n → Fin n → ℝ)
    (hNext : ∀ i j, A_next i j = matMul n P A_hat i j + E i j)
    (hE : frobNorm E ≤ c_step * frobNorm A_hat) :
    ∃ (Q' : Fin n → Fin n → ℝ) (ΔA' : Fin n → Fin n → ℝ),
      IsOrthogonal n Q' ∧
      (∀ i j, A_next i j =
        matMul n (matTranspose Q') (fun a b => A a b + ΔA' a b) i j) ∧
      frobNorm ΔA' ≤
        frobNorm ΔA +
          c_step * frobNorm (fun a b => A a b + ΔA a b) := by
  let Q' := matMul n Q (matTranspose P)
  let B : Fin n → Fin n → ℝ := fun a b => A a b + ΔA a b
  let E' : Fin n → Fin n → ℝ := matMul n Q' E
  let ΔA' : Fin n → Fin n → ℝ := fun a b => ΔA a b + E' a b
  have hQ' : IsOrthogonal n Q' := hQ.mul hP.transpose
  have hÂ : A_hat = matMul n (matTranspose Q) B :=
    funext fun k => funext fun l => hAhat k l
  have hQ'inv : matMul n (matTranspose Q') Q' = idMatrix n :=
    funext fun a => funext fun b => hQ'.left_inv a b
  have hQ'T : matTranspose Q' = matMul n P (matTranspose Q) := by
    show matTranspose (matMul n Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  have eq1 : matMul n (matTranspose Q') B = matMul n P A_hat := by
    rw [hQ'T, matMul_assoc, ← hÂ]
  have eq2 : matMul n (matTranspose Q') E' = E := by
    show matMul n (matTranspose Q') (matMul n Q' E) = _
    rw [← matMul_assoc, hQ'inv, matMul_id_left]
  use Q', ΔA'
  refine ⟨hQ', ?_, ?_⟩
  · have hBE : (fun a b => A a b + ΔA' a b) = fun a b => B a b + E' a b :=
      funext fun a => funext fun b =>
        show A a b + (ΔA a b + E' a b) = (A a b + ΔA a b) + E' a b from by ring
    intro i j
    rw [hNext i j, hBE]
    calc matMul n P A_hat i j + E i j
        = matMul n (matTranspose Q') B i j +
            matMul n (matTranspose Q') E' i j := by
          rw [← congr_fun (congr_fun eq1 i) j, ← congr_fun (congr_fun eq2 i) j]
      _ = matMul n (matTranspose Q') (fun a b => B a b + E' a b) i j :=
          (congr_fun (congr_fun (matMul_add_right n (matTranspose Q') B E') i) j).symm
  · have hfE' : frobNorm E' = frobNorm E := by
      show frobNorm (matMul n Q' E) = _
      exact frobNorm_orthogonal_left Q' E hQ'
    have hfÂ :
        frobNorm A_hat =
          frobNorm B := by
      rw [hÂ]; exact frobNorm_orthogonal_left (matTranspose Q) B hQ.transpose
    show frobNorm (fun a b => ΔA a b + E' a b) ≤
      frobNorm ΔA +
        c_step * frobNorm B
    calc frobNorm (fun a b => ΔA a b + E' a b)
        ≤ frobNorm ΔA + frobNorm E' := frobNorm_add_le ΔA E'
      _ = frobNorm ΔA + frobNorm E := by rw [hfE']
      _ ≤ frobNorm ΔA + c_step * frobNorm A_hat := by
          linarith [hE]
      _ = frobNorm ΔA + c_step * frobNorm B := by rw [hfÂ]

/-- Residual-form accumulation specialized to a columnwise Householder matrix
    step.  The residual bound is produced by
    `ColumnwiseHouseholderStepError.exists_residual_matrix_bound`. -/
theorem orthogonal_sequence_one_step_of_columnwise_error (n : ℕ)
    (A A_hat : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hAhat : ∀ i j, A_hat i j =
      matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) i j)
    (P : Fin n → Fin n → ℝ) (A_next : Fin n → Fin n → ℝ)
    (hStep : ColumnwiseHouseholderStepError n P A_hat A_next c_step)
    (hc_step : 0 ≤ c_step) :
    ∃ (Q' : Fin n → Fin n → ℝ) (ΔA' : Fin n → Fin n → ℝ),
      IsOrthogonal n Q' ∧
      (∀ i j, A_next i j =
        matMul n (matTranspose Q') (fun a b => A a b + ΔA' a b) i j) ∧
      frobNorm ΔA' ≤
        frobNorm ΔA +
          c_step * frobNorm (fun a b => A a b + ΔA a b) := by
  obtain ⟨E, hNext, hE⟩ := hStep.exists_residual_matrix_bound hc_step
  exact orthogonal_sequence_one_step_of_residual n A A_hat Q ΔA hQ hAhat
    P hStep.orth A_next E hNext hE

/-- Recurrence for the normwise error accumulated by repeated residual-form
    orthogonal steps.  It keeps the higher-order terms rather than replacing
    the bound by the first-order approximation `r*c`. -/
def residualAccumBound (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => residualAccumBound c k + c * (1 + residualAccumBound c k)

/-- The residual accumulation recurrence is nonnegative for nonnegative step
    bounds. -/
lemma residualAccumBound_nonneg (c : ℝ) (hc : 0 ≤ c) :
    ∀ r : ℕ, 0 ≤ residualAccumBound c r := by
  intro r
  induction r with
  | zero =>
      simp [residualAccumBound]
  | succ r ih =>
      simp [residualAccumBound]
      nlinarith

/-- **Repeated residual-form orthogonal sequence theorem**.

    If each step has the form `A_{k+1} = P_k A_k + E_k`, with `P_k`
    orthogonal and `‖E_k‖_F ≤ c‖A_k‖_F`, then the final matrix has the
    backward-error representation
    `A_r = Qᵀ(A_0 + ΔA)` with
    `‖ΔA‖_F ≤ residualAccumBound c r * ‖A_0‖_F`.

    This is a sound repeated-step version of Higham Lemma 18.3 before the
    usual first-order/gamma simplification to a bound of the form `r*c`. -/
theorem residual_orthogonal_sequence_backward_error (n r : ℕ)
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (Pseq : ℕ → Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hP : ∀ k : ℕ, k < r → IsOrthogonal n (Pseq k))
    (hStep : ∀ k : ℕ, k < r → ∃ E : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, Aseq (k + 1) i j =
        matMul n (Pseq k) (Aseq k) i j + E i j) ∧
      frobNorm E ≤ c * frobNorm (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  induction r with
  | zero =>
      let Z : Fin n → Fin n → ℝ := fun _ _ => 0
      refine ⟨idMatrix n, Z, idMatrix_orthogonal n, ?_, ?_⟩
      · intro i j
        simp [Z, matTranspose_id, matMul_id_left]
      · have hZ : frobNorm Z = 0 := by
          rw [frobNorm_eq_zero_iff]
          intro i j
          rfl
        simp [residualAccumBound, Z, hZ]
  | succ r ih =>
      have hP_prefix : ∀ k : ℕ, k < r → IsOrthogonal n (Pseq k) := by
        intro k hk
        exact hP k (Nat.lt_trans hk (Nat.lt_succ_self r))
      have hStep_prefix : ∀ k : ℕ, k < r → ∃ E : Fin n → Fin n → ℝ,
        (∀ i j : Fin n, Aseq (k + 1) i j =
          matMul n (Pseq k) (Aseq k) i j + E i j) ∧
        frobNorm E ≤ c * frobNorm (Aseq k) := by
        intro k hk
        exact hStep k (Nat.lt_trans hk (Nat.lt_succ_self r))
      obtain ⟨Q, ΔA, hQ, hAhat, hΔA⟩ := ih hP_prefix hStep_prefix
      obtain ⟨E, hNext, hE⟩ := hStep r (Nat.lt_succ_self r)
      obtain ⟨Q', ΔA', hQ', hRep, hStepBound⟩ :=
        orthogonal_sequence_one_step_of_residual n (Aseq 0) (Aseq r)
          Q ΔA hQ hAhat (Pseq r) (hP r (Nat.lt_succ_self r))
          (Aseq (r + 1)) E hNext hE
      refine ⟨Q', ΔA', hQ', ?_, ?_⟩
      · simpa using hRep
      · let α : ℝ := residualAccumBound c r
        let N : ℝ := frobNorm (Aseq 0)
        have hΔA' : frobNorm ΔA ≤ α * N := by
          simpa [α, N] using hΔA
        have hB :
            frobNorm (fun a b => Aseq 0 a b + ΔA a b) ≤
              (1 + α) * N := by
          calc
            frobNorm (fun a b => Aseq 0 a b + ΔA a b)
                ≤ frobNorm (Aseq 0) + frobNorm ΔA :=
                  frobNorm_add_le (Aseq 0) ΔA
            _ ≤ N + α * N := by
                simpa [N] using add_le_add_left hΔA' (frobNorm (Aseq 0))
            _ = (1 + α) * N := by ring
        have htotal :
            frobNorm ΔA' ≤ α * N + c * ((1 + α) * N) := by
          calc
            frobNorm ΔA'
                ≤ frobNorm ΔA +
                    c * frobNorm (fun a b => Aseq 0 a b + ΔA a b) :=
                  hStepBound
            _ ≤ α * N + c * ((1 + α) * N) := by
                exact add_le_add hΔA'
                  (mul_le_mul_of_nonneg_left hB hc)
        have hrec :
            residualAccumBound c (r + 1) * N =
              α * N + c * ((1 + α) * N) := by
          simp [residualAccumBound, α]
          ring
        rw [show residualAccumBound c (r + 1) * frobNorm (Aseq 0) =
            α * N + c * ((1 + α) * N) from by
          rw [← hrec]]
        exact htotal

/-- Sequence theorem specialized to columnwise Householder step contracts. -/
theorem columnwise_householder_sequence_backward_error (n r : ℕ)
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (Pseq : ℕ → Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ k : ℕ, k < r →
      ColumnwiseHouseholderStepError n (Pseq k) (Aseq k) (Aseq (k + 1)) c) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  apply residual_orthogonal_sequence_backward_error n r Aseq Pseq c hc
  · intro k hk
    exact (hStep k hk).orth
  · intro k hk
    obtain ⟨E, hNext, hE⟩ := (hStep k hk).exists_residual_matrix_bound hc
    exact ⟨E, hNext, hE⟩

/-- Raw bound produced by the concrete one-step Householder construction and
    application bridge. -/
noncomputable def householderConstructApplyBound (fp : FPModel) (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * fp.u ^ 2) + 2 * gamma fp (11 * n + 23)

/-- The concrete one-step Householder construction/application bound is
    nonnegative under the corresponding gamma-validity side condition. -/
lemma householderConstructApplyBound_nonneg (fp : FPModel) (n : ℕ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    0 ≤ householderConstructApplyBound fp n := by
  unfold householderConstructApplyBound
  have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) * fp.u ^ 2) := Real.sqrt_nonneg _
  have hγ : 0 ≤ gamma fp (11 * n + 23) := gamma_nonneg fp hvalid
  nlinarith

/-- Repeated concrete Householder construction/application sequence.

    This theorem is not yet a full QR factorization theorem: `xseq` supplies the
    vectors from which each reflector is constructed, and `hAstep` states that
    the matrix sequence is updated by applying the corresponding concrete
    rounded reflector to all columns.  It proves that such a concrete sequence
    satisfies the residual-form orthogonal-sequence backward-error result. -/
theorem fl_householder_sequence_backward_error (fp : FPModel) {n r : ℕ}
    (hn0 : 0 < n)
    (Aseq : ℕ → Fin n → Fin n → ℝ)
    (xseq : ℕ → Fin n → ℝ)
    (hx : ∀ k : ℕ, k < r → xseq k ≠ 0)
    (hvalid : gammaValid fp (11 * n + 23))
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_householderApplyMatrix fp n
          (fl_householderNormalizedVector fp hn0 (xseq k)) 1 (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (householderConstructApplyBound fp n) r *
          frobNorm (Aseq 0) := by
  let Pseq : ℕ → Fin n → Fin n → ℝ := fun k =>
    householder n
      (householderNormalizedVector n
        (householderVector hn0 (xseq k)) (householderBetaFromScale hn0 (xseq k))) 1
  apply columnwise_householder_sequence_backward_error n r Aseq Pseq
    (householderConstructApplyBound fp n)
    (householderConstructApplyBound_nonneg fp n hvalid)
  intro k hk
  have hraw :=
    fl_householderConstructApply_matrix_step_error fp hn0 (xseq k) (Aseq k)
      (hx k hk) hvalid
  rw [hAstep k hk]
  simpa [Pseq, householderConstructApplyBound] using hraw

/-- Residual-form single-step accumulation for rectangular panels. -/
theorem orthogonal_sequence_one_step_of_residual_rect (m p : ℕ)
    (A A_hat : Fin m → Fin p → ℝ)
    (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin p → ℝ)
    (hQ : IsOrthogonal m Q)
    (hAhat : ∀ i j, A_hat i j =
      matMulRect m m p (matTranspose Q) (fun a b => A a b + ΔA a b) i j)
    (P : Fin m → Fin m → ℝ)
    (hP : IsOrthogonal m P)
    (A_next E : Fin m → Fin p → ℝ)
    (hNext : ∀ i j, A_next i j =
      matMulRect m m p P A_hat i j + E i j)
    (hE : frobNorm E ≤ c_step * frobNorm A_hat) :
    ∃ (Q' : Fin m → Fin m → ℝ) (ΔA' : Fin m → Fin p → ℝ),
      IsOrthogonal m Q' ∧
      (∀ i j, A_next i j =
        matMulRect m m p (matTranspose Q')
          (fun a b => A a b + ΔA' a b) i j) ∧
      frobNorm ΔA' ≤
        frobNorm ΔA +
          c_step * frobNorm (fun a b => A a b + ΔA a b) := by
  let Q' := matMul m Q (matTranspose P)
  let B : Fin m → Fin p → ℝ := fun a b => A a b + ΔA a b
  let E' : Fin m → Fin p → ℝ := matMulRect m m p Q' E
  let ΔA' : Fin m → Fin p → ℝ := fun a b => ΔA a b + E' a b
  have hQ' : IsOrthogonal m Q' := hQ.mul hP.transpose
  have hÂ : A_hat = matMulRect m m p (matTranspose Q) B :=
    funext fun k => funext fun l => hAhat k l
  have hQ'inv : matMul m (matTranspose Q') Q' = idMatrix m :=
    funext fun a => funext fun b => hQ'.left_inv a b
  have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
    show matTranspose (matMul m Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  have eq1 :
      matMulRect m m p (matTranspose Q') B =
        matMulRect m m p P A_hat := by
    rw [hQ'T, matMulRect_assoc_square_left, ← hÂ]
  have eq2 : matMulRect m m p (matTranspose Q') E' = E := by
    show matMulRect m m p (matTranspose Q') (matMulRect m m p Q' E) = _
    rw [← matMulRect_assoc_square_left, hQ'inv, matMulRect_id_left]
  use Q', ΔA'
  refine ⟨hQ', ?_, ?_⟩
  · have hBE : (fun a b => A a b + ΔA' a b) = fun a b => B a b + E' a b :=
      funext fun a => funext fun b =>
        show A a b + (ΔA a b + E' a b) = (A a b + ΔA a b) + E' a b from by ring
    intro i j
    rw [hNext i j, hBE]
    calc matMulRect m m p P A_hat i j + E i j
        = matMulRect m m p (matTranspose Q') B i j +
            matMulRect m m p (matTranspose Q') E' i j := by
          rw [← congr_fun (congr_fun eq1 i) j, ← congr_fun (congr_fun eq2 i) j]
      _ = matMulRect m m p (matTranspose Q') (fun a b => B a b + E' a b) i j :=
          (congr_fun
            (congr_fun (matMulRect_add_right m m p (matTranspose Q') B E') i) j).symm
  · have hfE' : frobNorm E' = frobNorm E := by
      show frobNorm (matMulRect m m p Q' E) = _
      exact frobNorm_orthogonal_left_rect Q' E hQ'
    have hfÂ :
        frobNorm A_hat =
          frobNorm B := by
      rw [hÂ]
      exact frobNorm_orthogonal_left_rect (matTranspose Q) B hQ.transpose
    show frobNorm (fun a b => ΔA a b + E' a b) ≤
      frobNorm ΔA +
        c_step * frobNorm B
    calc frobNorm (fun a b => ΔA a b + E' a b)
        ≤ frobNorm ΔA + frobNorm E' :=
          norm_add_le (Matrix.of ΔA : Matrix (Fin m) (Fin p) ℝ)
            (Matrix.of E' : Matrix (Fin m) (Fin p) ℝ)
      _ = frobNorm ΔA + frobNorm E := by rw [hfE']
      _ ≤ frobNorm ΔA + c_step * frobNorm A_hat := by
          linarith [hE]
      _ = frobNorm ΔA + c_step * frobNorm B := by rw [hfÂ]

/-- Repeated residual-form orthogonal sequence theorem for rectangular panels. -/
theorem residual_orthogonal_sequence_backward_error_rect (m p r : ℕ)
    (Aseq : ℕ → Fin m → Fin p → ℝ)
    (Pseq : ℕ → Fin m → Fin m → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hP : ∀ k : ℕ, k < r → IsOrthogonal m (Pseq k))
    (hStep : ∀ k : ℕ, k < r → ∃ E : Fin m → Fin p → ℝ,
      (∀ (i : Fin m) (j : Fin p), Aseq (k + 1) i j =
        matMulRect m m p (Pseq k) (Aseq k) i j + E i j) ∧
      frobNorm E ≤ c * frobNorm (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin p → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin p), Aseq r i j =
        matMulRect m m p (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  induction r with
  | zero =>
      let Z : Fin m → Fin p → ℝ := fun _ _ => 0
      refine ⟨idMatrix m, Z, idMatrix_orthogonal m, ?_, ?_⟩
      · intro i j
        simp [Z, matTranspose_id, matMulRect_id_left]
      · have hZ : frobNorm Z = 0 := by
          rw [frobNorm_eq_zero_iff]
          intro i j
          rfl
        simp [residualAccumBound, Z, hZ]
  | succ r ih =>
      have hP_prefix : ∀ k : ℕ, k < r → IsOrthogonal m (Pseq k) := by
        intro k hk
        exact hP k (Nat.lt_trans hk (Nat.lt_succ_self r))
      have hStep_prefix : ∀ k : ℕ, k < r → ∃ E : Fin m → Fin p → ℝ,
        (∀ (i : Fin m) (j : Fin p), Aseq (k + 1) i j =
          matMulRect m m p (Pseq k) (Aseq k) i j + E i j) ∧
        frobNorm E ≤ c * frobNorm (Aseq k) := by
        intro k hk
        exact hStep k (Nat.lt_trans hk (Nat.lt_succ_self r))
      obtain ⟨Q, ΔA, hQ, hAhat, hΔA⟩ := ih hP_prefix hStep_prefix
      obtain ⟨E, hNext, hE⟩ := hStep r (Nat.lt_succ_self r)
      obtain ⟨Q', ΔA', hQ', hRep, hStepBound⟩ :=
        orthogonal_sequence_one_step_of_residual_rect m p (Aseq 0) (Aseq r)
          Q ΔA hQ hAhat (Pseq r) (hP r (Nat.lt_succ_self r))
          (Aseq (r + 1)) E hNext hE
      refine ⟨Q', ΔA', hQ', ?_, ?_⟩
      · simpa using hRep
      · let α : ℝ := residualAccumBound c r
        let N : ℝ := frobNorm (Aseq 0)
        have hΔA' : frobNorm ΔA ≤ α * N := by
          simpa [α, N] using hΔA
        have hB :
            frobNorm (fun a b => Aseq 0 a b + ΔA a b) ≤
              (1 + α) * N := by
          calc
            frobNorm (fun a b => Aseq 0 a b + ΔA a b)
                ≤ frobNorm (Aseq 0) + frobNorm ΔA :=
                  norm_add_le (Matrix.of (Aseq 0) : Matrix (Fin m) (Fin p) ℝ)
                    (Matrix.of ΔA : Matrix (Fin m) (Fin p) ℝ)
            _ ≤ N + α * N := by
                simpa [N] using add_le_add_left hΔA' (frobNorm (Aseq 0))
            _ = (1 + α) * N := by ring
        have htotal :
            frobNorm ΔA' ≤ α * N + c * ((1 + α) * N) := by
          calc
            frobNorm ΔA'
                ≤ frobNorm ΔA +
                    c * frobNorm (fun a b => Aseq 0 a b + ΔA a b) :=
                  hStepBound
            _ ≤ α * N + c * ((1 + α) * N) := by
                exact add_le_add hΔA'
                  (mul_le_mul_of_nonneg_left hB hc)
        have hrec :
            residualAccumBound c (r + 1) * N =
              α * N + c * ((1 + α) * N) := by
          simp [residualAccumBound, α]
          ring
        rw [show residualAccumBound c (r + 1) * frobNorm (Aseq 0) =
            α * N + c * ((1 + α) * N) from by
          rw [← hrec]]
        exact htotal

/-- Rectangular panel sequence theorem specialized to columnwise Householder
    panel-step contracts. -/
theorem columnwise_householder_panel_sequence_backward_error (m p r : ℕ)
    (Aseq : ℕ → Fin m → Fin p → ℝ)
    (Pseq : ℕ → Fin m → Fin m → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ k : ℕ, k < r →
      ColumnwiseHouseholderStepErrorRect m p
        (Pseq k) (Aseq k) (Aseq (k + 1)) c) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin p → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin p), Aseq r i j =
        matMulRect m m p (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤ residualAccumBound c r * frobNorm (Aseq 0) := by
  apply residual_orthogonal_sequence_backward_error_rect m p r Aseq Pseq c hc
  · intro k hk
    exact (hStep k hk).orth
  · intro k hk
    obtain ⟨E, hNext, hE⟩ := (hStep k hk).exists_residual_matrix_bound hc
    exact ⟨E, hNext, hE⟩

/-- Repeated concrete Householder construction/application on a rectangular
    panel sequence.

    This is the panel analogue of `fl_householder_sequence_backward_error`.
    It still does not choose the QR trailing-column vectors; it proves the
    reusable fact that once such vectors and concrete panel updates are supplied,
    the resulting repeated panel update is backward stable in the residual
    sequence sense. -/
theorem fl_householder_panel_sequence_backward_error (fp : FPModel)
    {m p r : ℕ}
    (hm0 : 0 < m)
    (Aseq : ℕ → Fin m → Fin p → ℝ)
    (xseq : ℕ → Fin m → ℝ)
    (hx : ∀ k : ℕ, k < r → xseq k ≠ 0)
    (hvalid : gammaValid fp (11 * m + 23))
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_householderApplyMatrixRect fp m p
          (fl_householderNormalizedVector fp hm0 (xseq k)) 1 (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin p → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin p), Aseq r i j =
        matMulRect m m p (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (householderConstructApplyBound fp m) r *
          frobNorm (Aseq 0) := by
  let Pseq : ℕ → Fin m → Fin m → ℝ := fun k =>
    householder m
      (householderNormalizedVector m
        (householderVector hm0 (xseq k)) (householderBetaFromScale hm0 (xseq k))) 1
  apply columnwise_householder_panel_sequence_backward_error m p r Aseq Pseq
    (householderConstructApplyBound fp m)
    (householderConstructApplyBound_nonneg fp m hvalid)
  intro k hk
  have hraw :=
    fl_householderConstructApply_matrix_step_error_rect fp hm0 (xseq k) (Aseq k)
      (hx k hk) hvalid
  rw [hAstep k hk]
  simpa [Pseq, householderConstructApplyBound] using hraw

/-- First column of a nonempty rectangular panel.  In a Householder QR panel
    step, this is the vector used to construct the next reflector. -/
noncomputable def panelFirstColumn {m p : ℕ} (hp0 : 0 < p)
    (A : Fin m → Fin p → ℝ) : Fin m → ℝ :=
  fun i => A i ⟨0, hp0⟩

/-- Drop the first row of a rectangular panel.  This is exact indexing
    infrastructure, not a floating-point operation. -/
noncomputable def panelDropFirstRow {m p : ℕ}
    (A : Fin (m + 1) → Fin p → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => A i.succ j

/-- Drop the first column of a rectangular panel.  This is exact indexing
    infrastructure, not a floating-point operation. -/
noncomputable def panelDropFirstCol {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => A i j.succ

/-- The trailing panel obtained by deleting the first row and first column. -/
noncomputable def trailingPanel {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => A i.succ j.succ

/-- Top-left entry of a nonempty rectangular panel. -/
noncomputable def panelTopLeft {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : ℝ :=
  A 0 0

/-- First row after the top-left entry of a nonempty panel. -/
noncomputable def panelTopRowTail {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : Fin p → ℝ :=
  fun j => A 0 j.succ

/-- First column below the top-left entry of a nonempty panel. -/
noncomputable def panelFirstColumnTail {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : Fin m → ℝ :=
  fun i => A i.succ 0

/-- The first-column tail of a panel has been zeroed. -/
def panelFirstColumnTailZero {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : Prop :=
  ∀ i : Fin m, panelFirstColumnTail A i = 0

/-- Reconstruct a nonempty panel from its top-left entry, top-row tail, and
    trailing panel, setting the first-column tail to zero.

    This is exact QR bookkeeping: after one Householder step, the algorithm
    stores the completed first column as triangular zeros and recurses on the
    trailing panel.  No floating-point operation is hidden in this definition. -/
noncomputable def panelFromTopAndTrailing {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ) :
    Fin (m + 1) → Fin (p + 1) → ℝ :=
  fun i j =>
    if hi : i = 0 then
      if hj : j = 0 then a00 else top (j.pred hj)
    else
      if hj : j = 0 then 0 else tail (i.pred hi) (j.pred hj)

/-- Embed a trailing-panel perturbation into a larger panel, with zero top row
    and zero completed first-column tail. -/
noncomputable def panelTrailingPerturbation {m p : ℕ}
    (tail : Fin m → Fin p → ℝ) : Fin (m + 1) → Fin (p + 1) → ℝ :=
  panelFromTopAndTrailing 0 (fun _ => 0) tail

/-- Embed an `m × m` matrix as the lower-right block of an `(m+1) × (m+1)`
    matrix, with a leading `1` on the diagonal and zeros in the first row and
    first column.

    This exact algebraic operation is the bridge between a Householder
    reflector acting on the active trailing panel and the same reflector viewed
    as a full-size orthogonal transformation in the QR loop. -/
noncomputable def embedTrailingOne {m : ℕ}
    (U : Fin m → Fin m → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun i j =>
    if hi : i = 0 then
      if j = 0 then 1 else 0
    else
      if hj : j = 0 then 0 else U (i.pred hi) (j.pred hj)

@[simp] theorem panelDropFirstRow_apply {m p : ℕ}
    (A : Fin (m + 1) → Fin p → ℝ) (i : Fin m) (j : Fin p) :
    panelDropFirstRow A i j = A i.succ j := rfl

@[simp] theorem panelDropFirstCol_apply {m p : ℕ}
    (A : Fin m → Fin (p + 1) → ℝ) (i : Fin m) (j : Fin p) :
    panelDropFirstCol A i j = A i j.succ := rfl

@[simp] theorem trailingPanel_apply {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (i : Fin m) (j : Fin p) :
    trailingPanel A i j = A i.succ j.succ := rfl

@[simp] theorem panelTopLeft_apply {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    panelTopLeft A = A 0 0 := rfl

@[simp] theorem panelTopRowTail_apply {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (j : Fin p) :
    panelTopRowTail A j = A 0 j.succ := rfl

@[simp] theorem panelFirstColumnTail_apply {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (i : Fin m) :
    panelFirstColumnTail A i = A i.succ 0 := rfl

@[simp] theorem panelFromTopAndTrailing_zero_zero {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ) :
    panelFromTopAndTrailing a00 top tail 0 0 = a00 := by
  simp [panelFromTopAndTrailing]

@[simp] theorem panelFromTopAndTrailing_zero_succ {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ)
    (j : Fin p) :
    panelFromTopAndTrailing a00 top tail 0 j.succ = top j := by
  simp [panelFromTopAndTrailing]

@[simp] theorem panelFromTopAndTrailing_succ_zero {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ)
    (i : Fin m) :
    panelFromTopAndTrailing a00 top tail i.succ 0 = 0 := by
  simp [panelFromTopAndTrailing]

@[simp] theorem panelFromTopAndTrailing_succ_succ {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ)
    (i : Fin m) (j : Fin p) :
    panelFromTopAndTrailing a00 top tail i.succ j.succ = tail i j := by
  simp [panelFromTopAndTrailing]

@[simp] theorem panelTopLeft_panelFromTopAndTrailing {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ) :
    panelTopLeft (panelFromTopAndTrailing a00 top tail) = a00 := by
  rfl

@[simp] theorem panelTopRowTail_panelFromTopAndTrailing {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ) :
    panelTopRowTail (panelFromTopAndTrailing a00 top tail) = top := by
  ext j
  rfl

@[simp] theorem trailingPanel_panelFromTopAndTrailing {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ) :
    trailingPanel (panelFromTopAndTrailing a00 top tail) = tail := by
  ext i j
  rfl

@[simp] theorem panelFirstColumnTailZero_panelFromTopAndTrailing {m p : ℕ}
    (a00 : ℝ) (top : Fin p → ℝ) (tail : Fin m → Fin p → ℝ) :
    panelFirstColumnTailZero (panelFromTopAndTrailing a00 top tail) := by
  intro i
  rfl

@[simp] theorem panelTrailingPerturbation_zero_zero {m p : ℕ}
    (tail : Fin m → Fin p → ℝ) :
    panelTrailingPerturbation tail 0 0 = 0 := by
  rfl

@[simp] theorem panelTrailingPerturbation_zero_succ {m p : ℕ}
    (tail : Fin m → Fin p → ℝ) (j : Fin p) :
    panelTrailingPerturbation tail 0 j.succ = 0 := by
  rfl

@[simp] theorem panelTrailingPerturbation_succ_zero {m p : ℕ}
    (tail : Fin m → Fin p → ℝ) (i : Fin m) :
    panelTrailingPerturbation tail i.succ 0 = 0 := by
  rfl

@[simp] theorem panelTrailingPerturbation_succ_succ {m p : ℕ}
    (tail : Fin m → Fin p → ℝ) (i : Fin m) (j : Fin p) :
    panelTrailingPerturbation tail i.succ j.succ = tail i j := by
  rfl

/-- A panel whose first-column tail is zero is exactly reconstructed from its
    visible top row and trailing panel. -/
theorem panelFromTopAndTrailing_of_firstColumnTailZero {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hzero : panelFirstColumnTailZero A) :
    panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
      (trailingPanel A) = A := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · rfl
    · intro j
      rfl
  · intro i
    refine Fin.cases ?_ ?_ j
    · simpa [panelFirstColumnTailZero, panelFirstColumnTail] using (hzero i).symm
    · intro j
      rfl

/-- If the whole first column of a nonempty panel is zero, then its
    first-column tail is zero.  This is the exact algebraic fact needed by the
    zero/skip branch of a Householder QR implementation: no reflector is needed
    to complete a column that is already zero in the active panel. -/
theorem panelFirstColumnTailZero_of_panelFirstColumn_eq_zero {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    panelFirstColumnTailZero A := by
  intro i
  have h := congrFun hcol i.succ
  simpa [panelFirstColumn, panelFirstColumnTail] using h

/-- Zero first-column panels are exactly reconstructed from their top row and
    trailing panel.  This is the reconstruction lemma used when the QR loop
    skips a degenerate Householder step. -/
theorem panelFromTopAndTrailing_of_panelFirstColumn_eq_zero {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
      (trailingPanel A) = A := by
  exact panelFromTopAndTrailing_of_firstColumnTailZero A
    (panelFirstColumnTailZero_of_panelFirstColumn_eq_zero A hcol)

/-- The embedded trailing-panel perturbation has exactly the same squared
    Frobenius norm as the trailing perturbation. -/
theorem frobNormSq_panelTrailingPerturbation {m p : ℕ}
    (tail : Fin m → Fin p → ℝ) :
    frobNormSq (panelTrailingPerturbation tail) = frobNormSq tail := by
  unfold frobNormSq panelTrailingPerturbation
  rw [Fin.sum_univ_succ]
  simp [panelFromTopAndTrailing, Fin.sum_univ_succ]

/-- The embedded trailing-panel perturbation has exactly the same Frobenius
    norm as the trailing perturbation. -/
theorem frobNorm_panelTrailingPerturbation {m p : ℕ}
    (tail : Fin m → Fin p → ℝ) :
    frobNorm (panelTrailingPerturbation tail) = frobNorm tail := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq,
    frobNormSq_panelTrailingPerturbation]

@[simp] theorem embedTrailingOne_zero_zero {m : ℕ}
    (U : Fin m → Fin m → ℝ) :
    embedTrailingOne U 0 0 = 1 := by
  simp [embedTrailingOne]

@[simp] theorem embedTrailingOne_zero_succ {m : ℕ}
    (U : Fin m → Fin m → ℝ) (j : Fin m) :
    embedTrailingOne U 0 j.succ = 0 := by
  simp [embedTrailingOne]

@[simp] theorem embedTrailingOne_succ_zero {m : ℕ}
    (U : Fin m → Fin m → ℝ) (i : Fin m) :
    embedTrailingOne U i.succ 0 = 0 := by
  simp [embedTrailingOne]

@[simp] theorem embedTrailingOne_succ_succ {m : ℕ}
    (U : Fin m → Fin m → ℝ) (i j : Fin m) :
    embedTrailingOne U i.succ j.succ = U i j := by
  simp [embedTrailingOne]

/-- Squared Frobenius norm of a one-step trailing-block embedding.

    The leading diagonal entry contributes `1`; all other new first-row and
    first-column entries are zero, and the trailing block contributes the
    original squared Frobenius norm. -/
theorem frobNormSq_embedTrailingOne {m : ℕ}
    (U : Fin m → Fin m → ℝ) :
    frobNormSq (embedTrailingOne U) = 1 + frobNormSq U := by
  unfold frobNormSq
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ]

/-- Frobenius norm of a one-step trailing-block embedding. -/
theorem frobNorm_embedTrailingOne {m : ℕ}
    (U : Fin m → Fin m → ℝ) :
    frobNorm (embedTrailingOne U) =
      Real.sqrt (1 + frobNormSq U) := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNormSq_embedTrailingOne]

/-- If a trailing block has an additive perturbation representation, then its
    one-step trailing-block embedding has the same representation with the
    perturbation embedded as a zero-top-row/zero-first-column tail block. -/
theorem embedTrailingOne_add_panelTrailingPerturbation {m : ℕ}
    {U V Δ : Fin m → Fin m → ℝ}
    (hV : ∀ i j, V i j = U i j + Δ i j) :
    ∀ i j : Fin (m + 1),
      embedTrailingOne V i j =
        embedTrailingOne U i j + panelTrailingPerturbation Δ i j := by
  intro i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      simp
  · intro i
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      simp [hV i j]

/-- Transpose commutes with one-step trailing-block embedding. -/
theorem matTranspose_embedTrailingOne {m : ℕ}
    (U : Fin m → Fin m → ℝ) :
    matTranspose (embedTrailingOne U) =
      embedTrailingOne (matTranspose U) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [matTranspose]
    · intro j
      simp [matTranspose]
  · intro i
    refine Fin.cases ?_ ?_ j
    · simp [matTranspose]
    · intro j
      simp [matTranspose]

/-- Matrix multiplication commutes with one-step trailing-block embedding. -/
theorem matMul_embedTrailingOne {m : ℕ}
    (U V : Fin m → Fin m → ℝ) :
    matMul (m + 1) (embedTrailingOne U) (embedTrailingOne V) =
      embedTrailingOne (matMul m U V) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · rw [show matMul (m + 1) (embedTrailingOne U) (embedTrailingOne V)
            0 0 =
          ∑ k : Fin (m + 1),
            embedTrailingOne U 0 k * embedTrailingOne V k 0 by rfl]
      rw [Fin.sum_univ_succ]
      simp
    · intro j
      rw [show matMul (m + 1) (embedTrailingOne U) (embedTrailingOne V)
            0 j.succ =
          ∑ k : Fin (m + 1),
            embedTrailingOne U 0 k * embedTrailingOne V k j.succ by rfl]
      rw [Fin.sum_univ_succ]
      simp
  · intro i
    refine Fin.cases ?_ ?_ j
    · rw [show matMul (m + 1) (embedTrailingOne U) (embedTrailingOne V)
            i.succ 0 =
          ∑ k : Fin (m + 1),
            embedTrailingOne U i.succ k * embedTrailingOne V k 0 by rfl]
      rw [Fin.sum_univ_succ]
      simp
    · intro j
      rw [show matMul (m + 1) (embedTrailingOne U) (embedTrailingOne V)
            i.succ j.succ =
          ∑ k : Fin (m + 1),
            embedTrailingOne U i.succ k * embedTrailingOne V k j.succ by rfl]
      rw [Fin.sum_univ_succ]
      simp [matMul]

/-- The identity matrix is preserved by one-step trailing-block embedding. -/
theorem embedTrailingOne_idMatrix (m : ℕ) :
    embedTrailingOne (idMatrix m) = idMatrix (m + 1) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [idMatrix]
    · intro j
      have h : (0 : Fin (m + 1)) ≠ j.succ := by
        exact Ne.symm (Fin.succ_ne_zero j)
      simp [idMatrix, h]
  · intro i
    refine Fin.cases ?_ ?_ j
    · have h : i.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero i
      simp [idMatrix, h]
    · intro j
      simp [idMatrix]

/-- Embedding a trailing-block orthogonal matrix with a leading scalar identity
    produces an orthogonal full matrix. -/
theorem embedTrailingOne_orthogonal {m : ℕ}
    (U : Fin m → Fin m → ℝ) (hU : IsOrthogonal m U) :
    IsOrthogonal (m + 1) (embedTrailingOne U) := by
  have hleft :
      matMul m (matTranspose U) U = idMatrix m := by
    ext i j
    exact hU.left_inv i j
  have hright :
      matMul m U (matTranspose U) = idMatrix m := by
    ext i j
    exact hU.right_inv i j
  constructor
  · intro i j
    show matMul (m + 1)
        (matTranspose (embedTrailingOne U)) (embedTrailingOne U) i j =
      if i = j then 1 else 0
    rw [matTranspose_embedTrailingOne, matMul_embedTrailingOne, hleft,
      embedTrailingOne_idMatrix]
    rfl
  · intro i j
    show matMul (m + 1)
        (embedTrailingOne U) (matTranspose (embedTrailingOne U)) i j =
      if i = j then 1 else 0
    rw [matTranspose_embedTrailingOne, matMul_embedTrailingOne, hright,
      embedTrailingOne_idMatrix]
    rfl

/-- Frobenius norm of an embedded exact orthogonal trailing factor. -/
theorem frobNorm_embedTrailingOne_of_orthogonal {m : ℕ}
    (U : Fin m → Fin m → ℝ) (hU : IsOrthogonal m U) :
    frobNorm (embedTrailingOne U) = Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  exact (embedTrailingOne_orthogonal U hU).frobNorm_eq_sqrt_card

/-- Left multiplication by an embedded trailing-block matrix leaves the top row
    of a rectangular panel unchanged. -/
theorem embedTrailingOne_matMulRect_top_row {m p : ℕ}
    (U : Fin m → Fin m → ℝ)
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (j : Fin (p + 1)) :
    matMulRect (m + 1) (m + 1) (p + 1) (embedTrailingOne U) A 0 j =
      A 0 j := by
  unfold matMulRect
  rw [Fin.sum_univ_succ]
  simp

/-- The trailing panel of an embedded trailing-block multiplication is the
    smaller multiplication of the trailing panel. -/
theorem trailingPanel_embedTrailingOne_matMulRect {m p : ℕ}
    (U : Fin m → Fin m → ℝ)
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    trailingPanel
      (matMulRect (m + 1) (m + 1) (p + 1) (embedTrailingOne U) A) =
        matMulRect m m p U (trailingPanel A) := by
  ext i j
  unfold trailingPanel matMulRect
  rw [Fin.sum_univ_succ]
  simp

/-- Lift a trailing-panel backward representation to the full panel by
    embedding the trailing orthogonal factor with a leading identity.

    The full perturbation has zero top row and zero completed first-column
    tail, and its trailing block is the tail perturbation. -/
theorem panelFromTopAndTrailing_lift_trailing_rep {m p : ℕ}
    (Q : Fin m → Fin m → ℝ)
    (a00 : ℝ) (top : Fin p → ℝ)
    (T Rtail ΔT : Fin m → Fin p → ℝ)
    (hTail : ∀ i j, Rtail i j =
      matMulRect m m p (matTranspose Q)
        (fun a b => T a b + ΔT a b) i j) :
    panelFromTopAndTrailing a00 top Rtail =
      matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Q))
        (fun i j =>
          panelFromTopAndTrailing a00 top T i j +
            panelTrailingPerturbation ΔT i j) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · unfold matMulRect
      rw [Fin.sum_univ_succ]
      simp
    · intro j
      unfold matMulRect
      rw [Fin.sum_univ_succ]
      simp
  · intro i
    refine Fin.cases ?_ ?_ j
    · unfold matMulRect
      rw [Fin.sum_univ_succ]
      simp
    · intro j
      simp only [panelFromTopAndTrailing_succ_succ]
      rw [hTail i j]
      unfold matMulRect
      rw [Fin.sum_univ_succ]
      simp

/-- Dropping first row and first column is the same as taking the trailing
    panel in either order. -/
theorem trailingPanel_eq_dropFirstRow_dropFirstCol {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    trailingPanel A = panelDropFirstRow (panelDropFirstCol A) := rfl

/-- Dropping first column then first row is also the trailing panel. -/
theorem trailingPanel_eq_dropFirstCol_dropFirstRow {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    trailingPanel A = panelDropFirstCol (panelDropFirstRow A) := rfl

/-- Taking a trailing panel cannot increase the squared Frobenius norm. -/
theorem frobNormSq_trailingPanel_le {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    frobNormSq (trailingPanel A) ≤ frobNormSq A := by
  unfold frobNormSq trailingPanel
  rw [Fin.sum_univ_succ
    (fun i : Fin (m + 1) => ∑ j : Fin (p + 1), A i j ^ 2)]
  rw [show
      (∑ i : Fin m, ∑ j : Fin (p + 1), A i.succ j ^ 2) =
        ∑ i : Fin m,
          (A i.succ 0 ^ 2 + ∑ j : Fin p, A i.succ j.succ ^ 2) by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succ
      (fun j : Fin (p + 1) => A i.succ j ^ 2)]]
  rw [Finset.sum_add_distrib]
  have hrow0 :
      0 ≤ ∑ j : Fin (p + 1), A 0 j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (A 0 j)
  have hcol0 :
      0 ≤ ∑ i : Fin m, A i.succ 0 ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (A i.succ 0)
  linarith

/-- Taking a trailing panel cannot increase the Frobenius norm. -/
theorem frobNorm_trailingPanel_le {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    frobNorm (trailingPanel A) ≤ frobNorm A := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq]
  exact Real.sqrt_le_sqrt (frobNormSq_trailingPanel_le A)

/-- Reconstructing a panel from the same top row and trailing panel while
    zeroing the first-column tail cannot increase the squared Frobenius norm. -/
theorem frobNormSq_panelFromTopAndTrailing_extract_le {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    frobNormSq
      (panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (trailingPanel A)) ≤
      frobNormSq A := by
  let B : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
      (trailingPanel A)
  have hrow0 :
      (∑ j : Fin (p + 1), B 0 j ^ 2) =
        ∑ j : Fin (p + 1), A 0 j ^ 2 := by
    rw [Fin.sum_univ_succ
      (fun j : Fin (p + 1) => B 0 j ^ 2)]
    rw [Fin.sum_univ_succ
      (fun j : Fin (p + 1) => A 0 j ^ 2)]
    simp [B]
  have htail :
      (∑ i : Fin m, ∑ j : Fin (p + 1), B i.succ j ^ 2) =
        ∑ i : Fin m, ∑ j : Fin p, A i.succ j.succ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succ]
    simp [B]
  unfold frobNormSq
  rw [show
      (∑ i : Fin (m + 1), ∑ j : Fin (p + 1), B i j ^ 2) =
        (∑ j : Fin (p + 1), B 0 j ^ 2) +
          ∑ i : Fin m, ∑ j : Fin (p + 1), B i.succ j ^ 2 by
    rw [Fin.sum_univ_succ]]
  rw [show
      (∑ i : Fin (m + 1), ∑ j : Fin (p + 1), A i j ^ 2) =
        (∑ j : Fin (p + 1), A 0 j ^ 2) +
          ∑ i : Fin m, ∑ j : Fin (p + 1), A i.succ j ^ 2 by
    rw [Fin.sum_univ_succ]]
  rw [hrow0, htail]
  rw [show
      (∑ i : Fin m, ∑ j : Fin (p + 1), A i.succ j ^ 2) =
        ∑ i : Fin m,
          (A i.succ 0 ^ 2 + ∑ j : Fin p, A i.succ j.succ ^ 2) by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succ]]
  rw [Finset.sum_add_distrib]
  have hcol0 :
      0 ≤ ∑ i : Fin m, A i.succ 0 ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (A i.succ 0)
  linarith

/-- Reconstructing a panel from the same top row and trailing panel while
    zeroing the first-column tail cannot increase the Frobenius norm. -/
theorem frobNorm_panelFromTopAndTrailing_extract_le {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    frobNorm
      (panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
        (trailingPanel A)) ≤
      frobNorm A := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq]
  exact Real.sqrt_le_sqrt (frobNormSq_panelFromTopAndTrailing_extract_le A)

/-- One concrete Householder QR trailing-panel update.

    Given an `(m+1) × (p+1)` panel, construct the Householder reflector from
    the panel's first column, apply the rounded reflector to the whole panel,
    then return the trailing `m × p` panel.  This is the concrete shrinking
    step needed before defining the dependent full QR loop. -/
noncomputable def fl_householderTrailingPanelStep (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    Fin m → Fin p → ℝ :=
  trailingPanel
    (fl_householderApplyMatrixRect fp (m + 1) (p + 1)
      (fl_householderNormalizedVector fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos p) A)) 1 A)

@[simp] theorem fl_householderTrailingPanelStep_apply (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (i : Fin m) (j : Fin p) :
    fl_householderTrailingPanelStep fp A i j =
      fl_householderApplyMatrixRect fp (m + 1) (p + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 A i.succ j.succ := rfl

/-- Recursive rounded Householder QR panel algorithm returning the `R` panel.

    In a nonempty panel, it computes the rounded first-column Householder
    application, stores the computed top row, sets the completed first-column
    tail to zero by construction, and recurses on the computed trailing panel.
    This is the concrete loop that the later backward-error theorem must
    connect to the residual-sequence analysis. -/
noncomputable def fl_householderQRPanel_R (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Fin m → Fin p → ℝ
  | 0, _, A => A
  | Nat.succ _, 0, A => A
  | m + 1, p + 1, A =>
      let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A
      panelFromTopAndTrailing
        (panelTopLeft Astep)
        (panelTopRowTail Astep)
        (fl_householderQRPanel_R fp m p (trailingPanel Astep))

@[simp] theorem fl_householderQRPanel_R_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    fl_householderQRPanel_R fp 0 p A = A := rfl

@[simp] theorem fl_householderQRPanel_R_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    fl_householderQRPanel_R fp (m + 1) 0 A = A := rfl

@[simp] theorem fl_householderQRPanel_R_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    fl_householderQRPanel_R fp (m + 1) (p + 1) A =
      let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A
      panelFromTopAndTrailing
        (panelTopLeft Astep)
        (panelTopRowTail Astep)
        (fl_householderQRPanel_R fp m p (trailingPanel Astep)) := rfl

/-- The recursive QR `R` algorithm stores the computed top-left entry from the
    current rounded Householder panel step. -/
theorem panelTopLeft_fl_householderQRPanel_R_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    panelTopLeft (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      panelTopLeft
        (fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A) := by
  simp [fl_householderQRPanel_R]

/-- The recursive QR `R` algorithm stores the computed top-row tail from the
    current rounded Householder panel step. -/
theorem panelTopRowTail_fl_householderQRPanel_R_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    panelTopRowTail (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      panelTopRowTail
        (fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A) := by
  simp [fl_householderQRPanel_R]

/-- The recursive QR `R` algorithm makes the completed first-column tail
    structurally zero. -/
theorem panelFirstColumnTailZero_fl_householderQRPanel_R_succ_succ
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    panelFirstColumnTailZero
      (fl_householderQRPanel_R fp (m + 1) (p + 1) A) := by
  simp [fl_householderQRPanel_R]

/-- The recursive QR `R` algorithm recurses exactly on the concrete rounded
    trailing-panel step. -/
theorem trailingPanel_fl_householderQRPanel_R_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    trailingPanel (fl_householderQRPanel_R fp (m + 1) (p + 1) A) =
      fl_householderQRPanel_R fp m p (fl_householderTrailingPanelStep fp A) := by
  simp [fl_householderQRPanel_R, fl_householderTrailingPanelStep]

/-- Zero-aware trailing-panel step for Householder QR.

    If the active first column is zero, the reflector is skipped and the next
    active panel is the exact trailing panel.  Otherwise this is the concrete
    rounded Householder trailing-panel step. -/
noncomputable def fl_householderTrailingPanelStepSafe (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    Fin m → Fin p → ℝ :=
  if panelFirstColumn (Nat.succ_pos p) A = 0 then
    trailingPanel A
  else
    fl_householderTrailingPanelStep fp A

/-- Zero-aware recursive rounded Householder QR panel algorithm returning the
    `R` panel.

    This variant closes the main degeneracy gap in the older implementation:
    nonzero active columns use the concrete rounded Householder step, while
    zero active columns skip the reflector and recurse on the trailing panel.
    The original `fl_householderQRPanel_R` is preserved for compatibility with
    the nonzero-panel theorem. -/
noncomputable def fl_householderQRPanel_R_safe (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Fin m → Fin p → ℝ
  | 0, _, A => A
  | Nat.succ _, 0, A => A
  | m + 1, p + 1, A =>
      if _hcol : panelFirstColumn (Nat.succ_pos p) A = 0 then
        panelFromTopAndTrailing
          (panelTopLeft A)
          (panelTopRowTail A)
          (fl_householderQRPanel_R_safe fp m p (trailingPanel A))
      else
        let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
          fl_householderApplyMatrixRect fp (m + 1) (p + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A)) 1 A
        panelFromTopAndTrailing
          (panelTopLeft Astep)
          (panelTopRowTail Astep)
          (fl_householderQRPanel_R_safe fp m p (trailingPanel Astep))

@[simp] theorem fl_householderQRPanel_R_safe_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    fl_householderQRPanel_R_safe fp 0 p A = A := rfl

@[simp] theorem fl_householderQRPanel_R_safe_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    fl_householderQRPanel_R_safe fp (m + 1) 0 A = A := rfl

@[simp] theorem fl_householderQRPanel_R_safe_succ_succ_zero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    fl_householderQRPanel_R_safe fp (m + 1) (p + 1) A =
      panelFromTopAndTrailing
        (panelTopLeft A)
        (panelTopRowTail A)
        (fl_householderQRPanel_R_safe fp m p (trailingPanel A)) := by
  simp [fl_householderQRPanel_R_safe, hcol]

@[simp] theorem fl_householderQRPanel_R_safe_succ_succ_nonzero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    fl_householderQRPanel_R_safe fp (m + 1) (p + 1) A =
      let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A
      panelFromTopAndTrailing
        (panelTopLeft Astep)
        (panelTopRowTail Astep)
        (fl_householderQRPanel_R_safe fp m p (trailingPanel Astep)) := by
  simp [fl_householderQRPanel_R_safe, hcol]

/-- The zero-aware recursive QR `R` algorithm makes the completed
    first-column tail structurally zero in every nonempty panel. -/
theorem panelFirstColumnTailZero_fl_householderQRPanel_R_safe_succ_succ
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    panelFirstColumnTailZero
      (fl_householderQRPanel_R_safe fp (m + 1) (p + 1) A) := by
  by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
  · simp [fl_householderQRPanel_R_safe, hcol]
  · simp [fl_householderQRPanel_R_safe, hcol]

/-- Square specialization of the recursive rounded Householder QR `R`
    algorithm. -/
noncomputable def fl_householderQR_R (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fl_householderQRPanel_R fp n n A

/-- Square specialization of the zero-aware recursive rounded Householder QR
    `R` algorithm. -/
noncomputable def fl_householderQR_R_safe (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fl_householderQRPanel_R_safe fp n n A

/-- Exact orthogonal-factor witness associated with the zero-aware rounded
    Householder QR panel algorithm.

    This is not a separately rounded accumulated `Q_hat`.  It records the exact
    product of ideal Householder reflectors used in the backward-error
    representation for the same branch choices and rounded trailing panels as
    `fl_householderQRPanel_R_safe`.  It is the first explicit `Q`-side object
    needed before adding a public `(Q, R)` factorization API. -/
noncomputable def fl_householderQRPanel_Q_safe (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Fin m → Fin m → ℝ
  | 0, _, _A => idMatrix 0
  | m + 1, 0, _A => idMatrix (m + 1)
  | m + 1, p + 1, A =>
      if _hcol : panelFirstColumn (Nat.succ_pos p) A = 0 then
        embedTrailingOne
          (fl_householderQRPanel_Q_safe fp m p (trailingPanel A))
      else
        let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
          householder (m + 1)
            (householderNormalizedVector (m + 1)
              (householderVector (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) A))
              (householderBetaFromScale (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) A))) 1
        let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
          fl_householderApplyMatrixRect fp (m + 1) (p + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A)) 1 A
        let Qt : Fin m → Fin m → ℝ :=
          fl_householderQRPanel_Q_safe fp m p (trailingPanel Astep)
        matTranspose
          (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P)

@[simp] theorem fl_householderQRPanel_Q_safe_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    fl_householderQRPanel_Q_safe fp 0 p A = idMatrix 0 := rfl

@[simp] theorem fl_householderQRPanel_Q_safe_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    fl_householderQRPanel_Q_safe fp (m + 1) 0 A = idMatrix (m + 1) := rfl

@[simp] theorem fl_householderQRPanel_Q_safe_succ_succ_zero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    fl_householderQRPanel_Q_safe fp (m + 1) (p + 1) A =
      embedTrailingOne
        (fl_householderQRPanel_Q_safe fp m p (trailingPanel A)) := by
  simp [fl_householderQRPanel_Q_safe, hcol]

@[simp] theorem fl_householderQRPanel_Q_safe_succ_succ_nonzero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    fl_householderQRPanel_Q_safe fp (m + 1) (p + 1) A =
      let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
        householder (m + 1)
          (householderNormalizedVector (m + 1)
            (householderVector (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))
            (householderBetaFromScale (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))) 1
      let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A
      let Qt : Fin m → Fin m → ℝ :=
        fl_householderQRPanel_Q_safe fp m p (trailingPanel Astep)
      matTranspose
        (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P) := by
  simp [fl_householderQRPanel_Q_safe, hcol]

/-- Square specialization of the explicit exact `Q` witness associated with
    `fl_householderQR_R_safe`. -/
noncomputable def fl_householderQR_Q_safe (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fl_householderQRPanel_Q_safe fp n n A

/-- Public paired object for the current Householder QR layer.

    `Q` is the explicit exact orthogonal witness associated with the
    backward-error representation, and `R` is the concrete rounded
    zero-aware `R` output.  This is intentionally not named as a rounded
    `(Q_hat, R_hat)` implementation: forming a separately rounded accumulated
    `Q_hat` is a later algorithmic layer. -/
structure HouseholderQRWitness (n : ℕ) where
  /-- Exact orthogonal witness generated from the safe QR branch choices. -/
  Q : Fin n → Fin n → ℝ
  /-- Concrete rounded zero-aware `R` output. -/
  R : Fin n → Fin n → ℝ

/-- Paired exact-`Q` witness and rounded `R_safe` output for Householder QR. -/
noncomputable def fl_householderQR_safe_witness (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : HouseholderQRWitness n :=
  { Q := fl_householderQR_Q_safe fp n A
    R := fl_householderQR_R_safe fp n A }

/-- Rounded accumulated `Q_hat` for the zero-aware Householder QR panel loop.

    This is a concrete `fl_*` algorithmic object, unlike
    `fl_householderQRPanel_Q_safe`, which is the exact orthogonal witness used
    in the backward-error proof.  In the nonzero branch, the same rounded
    Householder reflector that updates the active panel is applied columnwise
    to the embedded trailing `Q_hat` accumulator.

    No stability or orthogonality theorem is claimed here yet.  The next proof
    milestone is a separate bridge showing that this rounded accumulation
    satisfies an appropriate perturbation contract. -/
noncomputable def fl_householderQRPanel_Qhat_safe (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Fin m → Fin m → ℝ
  | 0, _, _A => idMatrix 0
  | m + 1, 0, _A => idMatrix (m + 1)
  | m + 1, p + 1, A =>
      if _hcol : panelFirstColumn (Nat.succ_pos p) A = 0 then
        embedTrailingOne
          (fl_householderQRPanel_Qhat_safe fp m p (trailingPanel A))
      else
        let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
          fl_householderApplyMatrixRect fp (m + 1) (p + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A)) 1 A
        let Qtail_hat : Fin m → Fin m → ℝ :=
          fl_householderQRPanel_Qhat_safe fp m p (trailingPanel Astep)
        fl_householderApplyMatrixRect fp (m + 1) (m + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1
          (embedTrailingOne Qtail_hat)

@[simp] theorem fl_householderQRPanel_Qhat_safe_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    fl_householderQRPanel_Qhat_safe fp 0 p A = idMatrix 0 := rfl

@[simp] theorem fl_householderQRPanel_Qhat_safe_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    fl_householderQRPanel_Qhat_safe fp (m + 1) 0 A = idMatrix (m + 1) := rfl

@[simp] theorem fl_householderQRPanel_Qhat_safe_succ_succ_zero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A =
      embedTrailingOne
        (fl_householderQRPanel_Qhat_safe fp m p (trailingPanel A)) := by
  simp [fl_householderQRPanel_Qhat_safe, hcol]

/-- Residual form of one zero-column rounded `Q_hat` accumulator update.

    When the active first column is zero, the safe QR loop skips the reflector.
    The `Q_hat` accumulator is therefore just the embedded trailing accumulator,
    equivalently an identity transformation plus zero residual. -/
theorem fl_householderQRPanel_Qhat_safe_succ_succ_zero_residual_bound
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    let Qtail_hat : Fin m → Fin m → ℝ :=
      fl_householderQRPanel_Qhat_safe fp m p (trailingPanel A)
    ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A i j =
          matMulRect (m + 1) (m + 1) (m + 1)
            (idMatrix (m + 1)) (embedTrailingOne Qtail_hat) i j +
              E i j) ∧
      frobNorm E ≤ 0 * frobNorm (embedTrailingOne Qtail_hat) := by
  dsimp only
  let Qtail_hat : Fin m → Fin m → ℝ :=
    fl_householderQRPanel_Qhat_safe fp m p (trailingPanel A)
  let Z : Fin (m + 1) → Fin (m + 1) → ℝ := fun _ _ => 0
  refine ⟨Z, ?_, ?_⟩
  · intro i j
    have hid :
        matMulRect (m + 1) (m + 1) (m + 1)
          (idMatrix (m + 1)) (embedTrailingOne Qtail_hat) =
            embedTrailingOne Qtail_hat :=
      matMulRect_id_left (m + 1) (m + 1) (embedTrailingOne Qtail_hat)
    rw [fl_householderQRPanel_Qhat_safe_succ_succ_zero fp A hcol,
      congr_fun (congr_fun hid i) j]
    simp [Qtail_hat, Z]
  · have hZ : frobNorm Z = 0 := by
      rw [frobNorm_eq_zero_iff]
      intro i j
      rfl
    rw [hZ]
    simp

@[simp] theorem fl_householderQRPanel_Qhat_safe_succ_succ_nonzero
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A =
      let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A
      let Qtail_hat : Fin m → Fin m → ℝ :=
        fl_householderQRPanel_Qhat_safe fp m p (trailingPanel Astep)
      fl_householderApplyMatrixRect fp (m + 1) (m + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1
        (embedTrailingOne Qtail_hat) := by
  simp [fl_householderQRPanel_Qhat_safe, hcol]

/-- One nonzero branch of the rounded `Q_hat` accumulator has the same
    concrete columnwise Householder matrix-step error as any rounded
    Householder application.

    This is the first local bridge for the computed `Q_hat` API: the full
    accumulated `Q_hat` theorem still needs a separate recursive composition
    proof, but each nonzero update is already connected to the lower-level
    implementation-backed Householder application theorem. -/
theorem fl_householderQRPanel_Qhat_safe_succ_succ_nonzero_step_error
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
      fl_householderApplyMatrixRect fp (m + 1) (p + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 A
    let Qtail_hat : Fin m → Fin m → ℝ :=
      fl_householderQRPanel_Qhat_safe fp m p (trailingPanel Astep)
    ColumnwiseHouseholderStepErrorRect (m + 1) (m + 1)
      (householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1)
      (embedTrailingOne Qtail_hat)
      (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
      (householderConstructApplyBound fp (m + 1)) := by
  dsimp only
  let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
    fl_householderApplyMatrixRect fp (m + 1) (p + 1)
      (fl_householderNormalizedVector fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos p) A)) 1 A
  let Qtail_hat : Fin m → Fin m → ℝ :=
    fl_householderQRPanel_Qhat_safe fp m p (trailingPanel Astep)
  have hstep :=
    fl_householderConstructApply_matrix_step_error_rect fp
      (Nat.succ_pos m) (panelFirstColumn (Nat.succ_pos p) A)
      (embedTrailingOne Qtail_hat) hcol hvalid
  simpa [fl_householderQRPanel_Qhat_safe, hcol, Astep, Qtail_hat,
    householderConstructApplyBound] using hstep

/-- Residual form of one nonzero rounded `Q_hat` accumulator update.

    This is the exact form needed for the future recursive `Q_hat`
    accumulation analysis: the computed accumulator update is an exact
    Householder application to the embedded trailing accumulator plus a single
    residual matrix whose Frobenius norm is bounded by the lower-level
    implementation-backed Householder coefficient. -/
theorem fl_householderQRPanel_Qhat_safe_succ_succ_nonzero_residual_bound
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
      fl_householderApplyMatrixRect fp (m + 1) (p + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 A
    let Qtail_hat : Fin m → Fin m → ℝ :=
      fl_householderQRPanel_Qhat_safe fp m p (trailingPanel Astep)
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A i j =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) i j + E i j) ∧
      frobNorm E ≤
        householderConstructApplyBound fp (m + 1) *
          frobNorm (embedTrailingOne Qtail_hat) := by
  dsimp only
  let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
    fl_householderApplyMatrixRect fp (m + 1) (p + 1)
      (fl_householderNormalizedVector fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos p) A)) 1 A
  let Qtail_hat : Fin m → Fin m → ℝ :=
    fl_householderQRPanel_Qhat_safe fp m p (trailingPanel Astep)
  let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
    householder (m + 1)
      (householderNormalizedVector (m + 1)
        (householderVector (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A))
        (householderBetaFromScale (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A))) 1
  have hstep :
      ColumnwiseHouseholderStepErrorRect (m + 1) (m + 1) P
        (embedTrailingOne Qtail_hat)
        (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
        (householderConstructApplyBound fp (m + 1)) := by
    simpa [P, Astep, Qtail_hat] using
      fl_householderQRPanel_Qhat_safe_succ_succ_nonzero_step_error
        fp A hcol hvalid
  exact hstep.exists_residual_matrix_bound
    (householderConstructApplyBound_nonneg fp (m + 1) hvalid)

/-- Exact transformation used by one safe `Q_hat` accumulator step.

    The zero-column branch skips the reflector and uses the identity.  The
    nonzero branch uses the exact Householder reflector corresponding to the
    same active first column used by the rounded panel update. -/
noncomputable def householderQRPanel_Qhat_stepP_safe {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    Fin (m + 1) → Fin (m + 1) → ℝ :=
  if panelFirstColumn (Nat.succ_pos p) A = 0 then
    idMatrix (m + 1)
  else
    householder (m + 1)
      (householderNormalizedVector (m + 1)
        (householderVector (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A))
        (householderBetaFromScale (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A))) 1

/-- Recursive tail accumulator used by one safe `Q_hat` step. -/
noncomputable def fl_householderQRPanel_Qhat_tail_safe (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    Fin m → Fin m → ℝ :=
  fl_householderQRPanel_Qhat_safe fp m p
    (fl_householderTrailingPanelStepSafe fp A)

/-- Local residual coefficient for one safe `Q_hat` accumulator step. -/
noncomputable def householderQRPanel_Qhat_stepCoeff_safe (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) : ℝ :=
  if panelFirstColumn (Nat.succ_pos p) A = 0 then
    0
  else
    householderConstructApplyBound fp (m + 1)

/-- The local residual coefficient for one safe `Q_hat` step is nonnegative
    under the same gamma-validity condition used by the nonzero branch. -/
theorem householderQRPanel_Qhat_stepCoeff_safe_nonneg (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    0 ≤ householderQRPanel_Qhat_stepCoeff_safe fp A := by
  by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
  · simp [householderQRPanel_Qhat_stepCoeff_safe, hcol]
  · simpa [householderQRPanel_Qhat_stepCoeff_safe, hcol] using
      householderConstructApplyBound_nonneg fp (m + 1) hvalid

/-- The exact transformation used by one safe `Q_hat` step is orthogonal. -/
theorem householderQRPanel_Qhat_stepP_safe_orthogonal (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    IsOrthogonal (m + 1) (householderQRPanel_Qhat_stepP_safe A) := by
  by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
  · simpa [householderQRPanel_Qhat_stepP_safe, hcol] using
      idMatrix_orthogonal (m + 1)
  · have hstep :=
      fl_householderQRPanel_Qhat_safe_succ_succ_nonzero_step_error
        fp A hcol hvalid
    simpa [householderQRPanel_Qhat_stepP_safe, hcol] using hstep.orth

/-- Unified residual form for one safe rounded `Q_hat` accumulator step.

    This combines the zero-column skip branch and the nonzero rounded
    Householder branch into one theorem.  It is the interface intended for the
    future recursive accumulated-`Q_hat` analysis. -/
theorem fl_householderQRPanel_Qhat_safe_succ_succ_residual_bound
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A i j =
          matMulRect (m + 1) (m + 1) (m + 1)
            (householderQRPanel_Qhat_stepP_safe A)
            (embedTrailingOne
              (fl_householderQRPanel_Qhat_tail_safe fp A)) i j +
              E i j) ∧
      frobNorm E ≤
        householderQRPanel_Qhat_stepCoeff_safe fp A *
          frobNorm
            (embedTrailingOne
              (fl_householderQRPanel_Qhat_tail_safe fp A)) := by
  by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
  · have hzero :=
      fl_householderQRPanel_Qhat_safe_succ_succ_zero_residual_bound fp A hcol
    simpa [householderQRPanel_Qhat_stepP_safe,
      householderQRPanel_Qhat_stepCoeff_safe,
      fl_householderQRPanel_Qhat_tail_safe,
      fl_householderTrailingPanelStepSafe, hcol] using hzero
  · have hnonzero :=
      fl_householderQRPanel_Qhat_safe_succ_succ_nonzero_residual_bound
        fp A hcol hvalid
    simpa [householderQRPanel_Qhat_stepP_safe,
      householderQRPanel_Qhat_stepCoeff_safe,
      fl_householderQRPanel_Qhat_tail_safe,
      fl_householderTrailingPanelStepSafe, fl_householderTrailingPanelStep,
      hcol] using hnonzero

/-- Complete local interface for one safe rounded `Q_hat` accumulator step:
    the exact step matrix is orthogonal, the local coefficient is
    nonnegative, and the rounded step has a bounded residual form. -/
theorem fl_householderQRPanel_Qhat_safe_succ_succ_step_interface
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    IsOrthogonal (m + 1) (householderQRPanel_Qhat_stepP_safe A) ∧
    0 ≤ householderQRPanel_Qhat_stepCoeff_safe fp A ∧
    ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A i j =
          matMulRect (m + 1) (m + 1) (m + 1)
            (householderQRPanel_Qhat_stepP_safe A)
            (embedTrailingOne
              (fl_householderQRPanel_Qhat_tail_safe fp A)) i j +
              E i j) ∧
      frobNorm E ≤
        householderQRPanel_Qhat_stepCoeff_safe fp A *
          frobNorm
            (embedTrailingOne
              (fl_householderQRPanel_Qhat_tail_safe fp A)) := by
  exact ⟨householderQRPanel_Qhat_stepP_safe_orthogonal fp A hvalid,
    householderQRPanel_Qhat_stepCoeff_safe_nonneg fp A hvalid,
    fl_householderQRPanel_Qhat_safe_succ_succ_residual_bound fp A hvalid⟩

/-- The exact `Q_safe` witness follows the same one-step orientation as the
    rounded `Q_hat` accumulator residual recurrence.

    In the nonzero branch this uses symmetry of the exact Householder
    reflector: `transpose (embed(Qtailᵀ) * P) = P * embed(Qtail)`. -/
theorem fl_householderQRPanel_Q_safe_succ_succ_as_stepP_safe
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    fl_householderQRPanel_Q_safe fp (m + 1) (p + 1) A =
      matMul (m + 1) (householderQRPanel_Qhat_stepP_safe A)
        (embedTrailingOne
          (fl_householderQRPanel_Q_safe fp m p
            (fl_householderTrailingPanelStepSafe fp A))) := by
  by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
  · simp [fl_householderQRPanel_Q_safe, householderQRPanel_Qhat_stepP_safe,
      fl_householderTrailingPanelStepSafe, hcol, matMul_id_left]
  · let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
      fl_householderApplyMatrixRect fp (m + 1) (p + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 A
    let Qt : Fin m → Fin m → ℝ :=
      fl_householderQRPanel_Q_safe fp m p (trailingPanel Astep)
    have hP : matTranspose P = P := by
      simpa [P] using
        householder_symmetric (m + 1)
          (householderNormalizedVector (m + 1)
            (householderVector (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))
            (householderBetaFromScale (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))) 1
    calc
      fl_householderQRPanel_Q_safe fp (m + 1) (p + 1) A
          = matTranspose
              (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P) := by
              simp [fl_householderQRPanel_Q_safe, hcol, P, Astep, Qt]
      _ = matMul (m + 1) P (embedTrailingOne Qt) := by
              rw [matTranspose_matMul, hP, matTranspose_embedTrailingOne,
                matTranspose_involutive]
      _ =
          matMul (m + 1) (householderQRPanel_Qhat_stepP_safe A)
            (embedTrailingOne
              (fl_householderQRPanel_Q_safe fp m p
                (fl_householderTrailingPanelStepSafe fp A))) := by
              simp [householderQRPanel_Qhat_stepP_safe,
                fl_householderTrailingPanelStepSafe,
                fl_householderTrailingPanelStep, hcol, P, Astep, Qt]

/-- Raw recursive accumulated perturbation bound for the rounded `Q_hat`
    panel algorithm.

    This is intentionally branch-sensitive and not yet simplified to a compact
    closed form.  Each safe step contributes its local residual coefficient
    times the actual Frobenius norm of the embedded tail accumulator. -/
noncomputable def householderQRPanel_QhatAccumBound (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → ℝ
  | 0, _, _A => 0
  | Nat.succ _, 0, _A => 0
  | m + 1, p + 1, A =>
      householderQRPanel_QhatAccumBound fp m p
        (fl_householderTrailingPanelStepSafe fp A) +
      householderQRPanel_Qhat_stepCoeff_safe fp A *
        frobNorm
          (embedTrailingOne
            (fl_householderQRPanel_Qhat_tail_safe fp A))

@[simp] theorem householderQRPanel_QhatAccumBound_zero_rows
    (fp : FPModel) {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    householderQRPanel_QhatAccumBound fp 0 p A = 0 := rfl

@[simp] theorem householderQRPanel_QhatAccumBound_zero_cols
    (fp : FPModel) {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    householderQRPanel_QhatAccumBound fp (m + 1) 0 A = 0 := rfl

/-- Recursive accumulated `Q_hat` bound with the embedded tail norm eliminated.

    At each step, the raw factor `‖embedTrailingOne Qtail_hat‖_F` is bounded by
    the Frobenius norm of an exact embedded orthogonal block,
    `sqrt (m + 1)`, plus the already accumulated tail perturbation.  This is
    still recursive and branch-sensitive, but it no longer depends on the
    concrete accumulated `Q_hat` value. -/
noncomputable def householderQRPanel_QhatClosedBound (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → ℝ
  | 0, _, _A => 0
  | Nat.succ _, 0, _A => 0
  | m + 1, p + 1, A =>
      let ηtail :=
        householderQRPanel_QhatClosedBound fp m p
          (fl_householderTrailingPanelStepSafe fp A)
      ηtail +
        householderQRPanel_Qhat_stepCoeff_safe fp A *
          (Real.sqrt ((m + 1 : ℕ) : ℝ) + ηtail)

@[simp] theorem householderQRPanel_QhatClosedBound_zero_rows
    (fp : FPModel) {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    householderQRPanel_QhatClosedBound fp 0 p A = 0 := rfl

@[simp] theorem householderQRPanel_QhatClosedBound_zero_cols
    (fp : FPModel) {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    householderQRPanel_QhatClosedBound fp (m + 1) 0 A = 0 := rfl

/-- Dimension-only recursive upper bound for accumulated rounded `Q_hat`
    perturbations.

    This replaces all branch-dependent step coefficients by the uniform
    coefficient `householderConstructApplyBound fp N` and all embedded
    orthogonal block norms by `sqrt N`. -/
noncomputable def householderQR_QhatUniformClosedBound
    (fp : FPModel) (N : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      let η := householderQR_QhatUniformClosedBound fp N k
      η + householderConstructApplyBound fp N *
        (Real.sqrt (N : ℝ) + η)

@[simp] theorem householderQR_QhatUniformClosedBound_zero
    (fp : FPModel) (N : ℕ) :
    householderQR_QhatUniformClosedBound fp N 0 = 0 := rfl

/-- The uniform accumulated `Q_hat` bound is nonnegative. -/
lemma householderQR_QhatUniformClosedBound_nonneg
    (fp : FPModel) (N : ℕ)
    (hvalid : gammaValid fp (11 * N + 23)) :
    ∀ k : ℕ, 0 ≤ householderQR_QhatUniformClosedBound fp N k := by
  intro k
  induction k with
  | zero =>
      simp [householderQR_QhatUniformClosedBound]
  | succ k ih =>
      have hc : 0 ≤ householderConstructApplyBound fp N :=
        householderConstructApplyBound_nonneg fp N hvalid
      have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      simp [householderQR_QhatUniformClosedBound]
      exact add_nonneg ih (mul_nonneg hc (add_nonneg hs ih))

/-- The one-step Householder construction/application coefficient is monotone
    in the active dimension under a gamma-validity hypothesis for the larger
    dimension. -/
lemma householderConstructApplyBound_mono (fp : FPModel)
    {k N : ℕ} (hkN : k ≤ N)
    (hvalid : gammaValid fp (11 * N + 23)) :
    householderConstructApplyBound fp k ≤
      householderConstructApplyBound fp N := by
  unfold householderConstructApplyBound
  have hkN_real : (k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hkN
  have hu2 : 0 ≤ fp.u ^ 2 := sq_nonneg fp.u
  have hs_arg : (k : ℝ) * fp.u ^ 2 ≤ (N : ℝ) * fp.u ^ 2 :=
    mul_le_mul_of_nonneg_right hkN_real hu2
  have hsqrt :
      Real.sqrt ((k : ℝ) * fp.u ^ 2) ≤
        Real.sqrt ((N : ℝ) * fp.u ^ 2) :=
    Real.sqrt_le_sqrt hs_arg
  have hgamma :
      gamma fp (11 * k + 23) ≤ gamma fp (11 * N + 23) :=
    gamma_mono fp (by omega) hvalid
  linarith

/-- A safe `Q_hat` step coefficient is bounded by a uniform larger-dimension
    Householder coefficient. -/
lemma householderQRPanel_Qhat_stepCoeff_safe_le_global
    (fp : FPModel) {m p N : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hmN : m + 1 ≤ N)
    (hvalid : gammaValid fp (11 * N + 23)) :
    householderQRPanel_Qhat_stepCoeff_safe fp A ≤
      householderConstructApplyBound fp N := by
  by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
  · have hnonneg :
        0 ≤ householderConstructApplyBound fp N :=
      householderConstructApplyBound_nonneg fp N hvalid
    simpa [householderQRPanel_Qhat_stepCoeff_safe, hcol] using hnonneg
  · simpa [householderQRPanel_Qhat_stepCoeff_safe, hcol] using
      householderConstructApplyBound_mono fp hmN hvalid

/-- The branch-sensitive closed accumulated `Q_hat` bound is nonnegative under
    a single global gamma-validity hypothesis. -/
theorem householderQRPanel_QhatClosedBound_nonneg_of_global_gammaValid
    (fp : FPModel) :
    ∀ (m p N : ℕ) (A : Fin m → Fin p → ℝ),
      m ≤ N →
      gammaValid fp (11 * N + 23) →
      0 ≤ householderQRPanel_QhatClosedBound fp m p A := by
  intro m
  induction m with
  | zero =>
      intro p N A _hmN _hvalid
      simp [householderQRPanel_QhatClosedBound]
  | succ m ih =>
      intro p N A hmN hvalid
      cases p with
      | zero =>
          simp [householderQRPanel_QhatClosedBound]
      | succ p =>
          have htail :
              0 ≤ householderQRPanel_QhatClosedBound fp m p
                (fl_householderTrailingPanelStepSafe fp A) :=
            ih p N (fl_householderTrailingPanelStepSafe fp A) (by omega) hvalid
          have hstepValid : gammaValid fp (11 * (m + 1) + 23) :=
            gammaValid_mono fp (by omega) hvalid
          have hc :
              0 ≤ householderQRPanel_Qhat_stepCoeff_safe fp A :=
            householderQRPanel_Qhat_stepCoeff_safe_nonneg fp A hstepValid
          have hs : 0 ≤ Real.sqrt ((m : ℝ) + 1) :=
            Real.sqrt_nonneg _
          simp [householderQRPanel_QhatClosedBound]
          exact add_nonneg htail
            (mul_nonneg hc (add_nonneg hs htail))

/-- The branch-sensitive closed accumulated `Q_hat` bound is controlled by the
    dimension-only uniform recursive bound. -/
theorem householderQRPanel_QhatClosedBound_le_uniform
    (fp : FPModel) :
    ∀ (m p N : ℕ) (A : Fin m → Fin p → ℝ),
      m ≤ N →
      gammaValid fp (11 * N + 23) →
      householderQRPanel_QhatClosedBound fp m p A ≤
        householderQR_QhatUniformClosedBound fp N m := by
  intro m
  induction m with
  | zero =>
      intro p N A _hmN _hvalid
      simp [householderQRPanel_QhatClosedBound,
        householderQR_QhatUniformClosedBound]
  | succ m ih =>
      intro p N A hmN hvalid
      cases p with
      | zero =>
          exact householderQR_QhatUniformClosedBound_nonneg fp N hvalid (m + 1)
      | succ p =>
          let η : ℝ :=
            householderQRPanel_QhatClosedBound fp m p
              (fl_householderTrailingPanelStepSafe fp A)
          let U : ℝ := householderQR_QhatUniformClosedBound fp N m
          let a : ℝ := householderQRPanel_Qhat_stepCoeff_safe fp A
          let c : ℝ := householderConstructApplyBound fp N
          let s : ℝ := Real.sqrt ((m + 1 : ℕ) : ℝ)
          let B : ℝ := Real.sqrt (N : ℝ)
          have hηU : η ≤ U :=
            ih p N (fl_householderTrailingPanelStepSafe fp A) (by omega) hvalid
          have hη_nonneg : 0 ≤ η :=
            householderQRPanel_QhatClosedBound_nonneg_of_global_gammaValid
              fp m p N (fl_householderTrailingPanelStepSafe fp A)
              (by omega) hvalid
          have ha_nonneg : 0 ≤ a := by
            have hstepValid : gammaValid fp (11 * (m + 1) + 23) :=
              gammaValid_mono fp (by omega) hvalid
            simpa [a] using
              householderQRPanel_Qhat_stepCoeff_safe_nonneg fp A hstepValid
          have ha_le_c : a ≤ c := by
            simpa [a, c] using
              householderQRPanel_Qhat_stepCoeff_safe_le_global fp A hmN hvalid
          have hc_nonneg : 0 ≤ c := by
            simpa [c] using householderConstructApplyBound_nonneg fp N hvalid
          have hs_le_B : s ≤ B := by
            have hcast : ((m + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast hmN
            simpa [s, B] using Real.sqrt_le_sqrt hcast
          have hterm : s + η ≤ B + U :=
            add_le_add hs_le_B hηU
          have hterm_nonneg : 0 ≤ s + η := by
            have hs_nonneg : 0 ≤ s := by
              simp [s]
            exact add_nonneg hs_nonneg hη_nonneg
          have hmul :
              a * (s + η) ≤ c * (B + U) := by
            have h1 : a * (s + η) ≤ c * (s + η) :=
              mul_le_mul_of_nonneg_right ha_le_c hterm_nonneg
            have h2 : c * (s + η) ≤ c * (B + U) :=
              mul_le_mul_of_nonneg_left hterm hc_nonneg
            exact le_trans h1 h2
          simpa [householderQRPanel_QhatClosedBound,
            householderQR_QhatUniformClosedBound, η, U, a, c, s, B] using
            add_le_add hηU hmul

/-- Accumulated perturbation statement for a rounded `Q_hat`: it is an exact
    orthogonal matrix plus a Frobenius-norm-bounded perturbation. -/
structure HouseholderQRPanelQhatAccumError (m : ℕ)
    (Q_hat : Fin m → Fin m → ℝ) (η : ℝ) : Prop where
  /-- Existence of an exact orthogonal factor and perturbation explaining the
      rounded accumulated `Q_hat`. -/
  result : ∃ (Q : Fin m → Fin m → ℝ) (ΔQ : Fin m → Fin m → ℝ),
    IsOrthogonal m Q ∧
    (∀ i j, Q_hat i j = Q i j + ΔQ i j) ∧
    frobNorm ΔQ ≤ η

/-- Accumulated `Q_hat` perturbation bounds are monotone in the bound value. -/
theorem HouseholderQRPanelQhatAccumError.mono {m : ℕ}
    {Q_hat : Fin m → Fin m → ℝ} {η η' : ℝ}
    (h : HouseholderQRPanelQhatAccumError m Q_hat η)
    (hη : η ≤ η') :
    HouseholderQRPanelQhatAccumError m Q_hat η' := by
  obtain ⟨Q, ΔQ, hQ, hrep, hΔQ⟩ := h.result
  exact ⟨⟨Q, ΔQ, hQ, hrep, le_trans hΔQ hη⟩⟩

/-- The embedded tail accumulator norm is controlled by the exact orthogonal
    block size plus the accumulated tail perturbation. -/
theorem HouseholderQRPanelQhatAccumError.embedTrailingOne_norm_le {m : ℕ}
    {Qtail_hat : Fin m → Fin m → ℝ} {ηtail : ℝ}
    (hTail : HouseholderQRPanelQhatAccumError m Qtail_hat ηtail) :
    frobNorm (embedTrailingOne Qtail_hat) ≤
      Real.sqrt ((m + 1 : ℕ) : ℝ) + ηtail := by
  obtain ⟨Qt, ΔT, hQt, hTailRep, hΔT⟩ := hTail.result
  let Δemb : Fin (m + 1) → Fin (m + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  have hemb :
      embedTrailingOne Qtail_hat =
        fun i j => embedTrailingOne Qt i j + Δemb i j := by
    ext i j
    exact embedTrailingOne_add_panelTrailingPerturbation hTailRep i j
  calc
    frobNorm (embedTrailingOne Qtail_hat)
        = frobNorm (fun i j => embedTrailingOne Qt i j + Δemb i j) := by
          rw [hemb]
    _ ≤ frobNorm (embedTrailingOne Qt) + frobNorm Δemb := by
          exact norm_add_le
            (Matrix.of (embedTrailingOne Qt) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
            (Matrix.of Δemb :
              Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    _ = Real.sqrt ((m + 1 : ℕ) : ℝ) + frobNorm ΔT := by
          rw [frobNorm_embedTrailingOne_of_orthogonal Qt hQt,
            frobNorm_panelTrailingPerturbation]
    _ ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) + ηtail :=
          add_le_add_right hΔT _

/-- Fixed-reference accumulated perturbation statement for rounded `Q_hat`.

    Unlike `HouseholderQRPanelQhatAccumError`, this does not hide the exact
    orthogonal factor existentially.  It states that a specific exact reference
    factor, later `fl_householderQRPanel_Q_safe`, explains the computed
    `Q_hat` up to a bounded perturbation. -/
structure HouseholderQRPanelQhatFixedAccumError (m : ℕ)
    (Q_ref Q_hat : Fin m → Fin m → ℝ) (η : ℝ) : Prop where
  /-- The fixed exact reference factor is orthogonal. -/
  orth : IsOrthogonal m Q_ref
  /-- The rounded accumulated factor differs from `Q_ref` by a bounded
      Frobenius-norm perturbation. -/
  result : ∃ ΔQ : Fin m → Fin m → ℝ,
    (∀ i j, Q_hat i j = Q_ref i j + ΔQ i j) ∧
    frobNorm ΔQ ≤ η

/-- Forget the fixed reference factor and recover the existential accumulated
    `Q_hat` perturbation statement. -/
theorem HouseholderQRPanelQhatFixedAccumError.toAccum {m : ℕ}
    {Q_ref Q_hat : Fin m → Fin m → ℝ} {η : ℝ}
    (h : HouseholderQRPanelQhatFixedAccumError m Q_ref Q_hat η) :
    HouseholderQRPanelQhatAccumError m Q_hat η := by
  obtain ⟨ΔQ, hrep, hΔQ⟩ := h.result
  exact ⟨⟨Q_ref, ΔQ, h.orth, hrep, hΔQ⟩⟩

/-- Fixed-reference accumulated `Q_hat` perturbation bounds are monotone in
    the bound value. -/
theorem HouseholderQRPanelQhatFixedAccumError.mono {m : ℕ}
    {Q_ref Q_hat : Fin m → Fin m → ℝ} {η η' : ℝ}
    (h : HouseholderQRPanelQhatFixedAccumError m Q_ref Q_hat η)
    (hη : η ≤ η') :
    HouseholderQRPanelQhatFixedAccumError m Q_ref Q_hat η' := by
  obtain ⟨ΔQ, hrep, hΔQ⟩ := h.result
  exact ⟨h.orth, ⟨ΔQ, hrep, le_trans hΔQ hη⟩⟩

/-- Algebraic one-step extension for accumulated rounded `Q_hat` errors. -/
theorem HouseholderQRPanelQhatAccumError.cons {m : ℕ}
    {Qtail_hat : Fin m → Fin m → ℝ} {ηtail : ℝ}
    (hTail : HouseholderQRPanelQhatAccumError m Qtail_hat ηtail)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q_hat : Fin (m + 1) → Fin (m + 1) → ℝ) (c : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hStep : ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        Q_hat i j =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) i j + E i j) ∧
      frobNorm E ≤ c * frobNorm (embedTrailingOne Qtail_hat)) :
    HouseholderQRPanelQhatAccumError (m + 1) Q_hat
      (ηtail + c * frobNorm (embedTrailingOne Qtail_hat)) := by
  obtain ⟨Qt, ΔT, hQt, hTailRep, hΔT⟩ := hTail.result
  obtain ⟨E, hQhat, hE⟩ := hStep
  let Δemb : Fin (m + 1) → Fin (m + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ :=
    matMul (m + 1) P (embedTrailingOne Qt)
  let ΔQ : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i j =>
      matMulRect (m + 1) (m + 1) (m + 1) P Δemb i j + E i j
  refine ⟨⟨Q, ΔQ, ?_, ?_, ?_⟩⟩
  · exact hP.mul (embedTrailingOne_orthogonal Qt hQt)
  · intro i j
    have hemb :
        embedTrailingOne Qtail_hat =
          fun i j => embedTrailingOne Qt i j + Δemb i j := by
      ext a b
      exact embedTrailingOne_add_panelTrailingPerturbation hTailRep a b
    have hmul :
        matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (fun a b => embedTrailingOne Qt a b + Δemb a b) := by
      rw [hemb]
    calc
      Q_hat i j =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) i j + E i j := hQhat i j
      _ =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (fun a b => embedTrailingOne Qt a b + Δemb a b) i j + E i j := by
            rw [hmul]
      _ =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qt) i j +
            matMulRect (m + 1) (m + 1) (m + 1) P Δemb i j +
            E i j := by
            rw [← congr_fun
              (congr_fun
                (matMulRect_add_right (m + 1) (m + 1) (m + 1)
                  P (embedTrailingOne Qt) Δemb) i) j]
      _ = Q i j + ΔQ i j := by
            simp [Q, ΔQ, matMul, matMulRect]
            ring_nf
  · have hΔQ_triangle :
        frobNorm ΔQ ≤
          frobNorm (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) +
            frobNorm E := by
      show frobNorm
          (fun i j =>
            matMulRect (m + 1) (m + 1) (m + 1) P Δemb i j + E i j) ≤ _
      exact norm_add_le
        (Matrix.of (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (Matrix.of E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    have hPΔ :
        frobNorm (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) =
          frobNorm Δemb :=
      frobNorm_orthogonal_left_rect P Δemb hP
    have hΔemb : frobNorm Δemb = frobNorm ΔT :=
      frobNorm_panelTrailingPerturbation ΔT
    calc
      frobNorm ΔQ
          ≤ frobNorm (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) +
              frobNorm E := hΔQ_triangle
      _ = frobNorm ΔT + frobNorm E := by rw [hPΔ, hΔemb]
      _ ≤ ηtail + c * frobNorm (embedTrailingOne Qtail_hat) :=
          add_le_add hΔT hE

/-- One-step extension using the closed recursive `Q_hat` bound. -/
theorem HouseholderQRPanelQhatAccumError.cons_closed {m : ℕ}
    {Qtail_hat : Fin m → Fin m → ℝ} {ηtail : ℝ}
    (hTail : HouseholderQRPanelQhatAccumError m Qtail_hat ηtail)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Q_hat : Fin (m + 1) → Fin (m + 1) → ℝ) (c : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hc : 0 ≤ c)
    (hStep : ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        Q_hat i j =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) i j + E i j) ∧
      frobNorm E ≤ c * frobNorm (embedTrailingOne Qtail_hat)) :
    HouseholderQRPanelQhatAccumError (m + 1) Q_hat
      (ηtail + c * (Real.sqrt ((m + 1 : ℕ) : ℝ) + ηtail)) := by
  have hRaw :=
    HouseholderQRPanelQhatAccumError.cons hTail P Q_hat c hP hStep
  have htailNorm :=
    HouseholderQRPanelQhatAccumError.embedTrailingOne_norm_le hTail
  refine hRaw.mono ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left htailNorm hc) ηtail

/-- Algebraic one-step extension for fixed-reference accumulated rounded
    `Q_hat` errors. -/
theorem HouseholderQRPanelQhatFixedAccumError.cons {m : ℕ}
    {Qtail Qtail_hat : Fin m → Fin m → ℝ} {ηtail : ℝ}
    (hTail :
      HouseholderQRPanelQhatFixedAccumError m Qtail Qtail_hat ηtail)
    (P Q_ref Q_hat : Fin (m + 1) → Fin (m + 1) → ℝ) (c : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hQ_ref :
      Q_ref = matMul (m + 1) P (embedTrailingOne Qtail))
    (hStep : ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        Q_hat i j =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) i j + E i j) ∧
      frobNorm E ≤ c * frobNorm (embedTrailingOne Qtail_hat)) :
    HouseholderQRPanelQhatFixedAccumError (m + 1) Q_ref Q_hat
      (ηtail + c * frobNorm (embedTrailingOne Qtail_hat)) := by
  obtain ⟨ΔT, hTailRep, hΔT⟩ := hTail.result
  obtain ⟨E, hQhat, hE⟩ := hStep
  let Δemb : Fin (m + 1) → Fin (m + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  let ΔQ : Fin (m + 1) → Fin (m + 1) → ℝ :=
    fun i j =>
      matMulRect (m + 1) (m + 1) (m + 1) P Δemb i j + E i j
  refine ⟨?_, ⟨ΔQ, ?_, ?_⟩⟩
  · rw [hQ_ref]
    exact hP.mul (embedTrailingOne_orthogonal Qtail hTail.orth)
  · intro i j
    have hemb :
        embedTrailingOne Qtail_hat =
          fun i j => embedTrailingOne Qtail i j + Δemb i j := by
      ext a b
      exact embedTrailingOne_add_panelTrailingPerturbation hTailRep a b
    have hmul :
        matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (fun a b => embedTrailingOne Qtail a b + Δemb a b) := by
      rw [hemb]
    calc
      Q_hat i j =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) i j + E i j := hQhat i j
      _ =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (fun a b => embedTrailingOne Qtail a b + Δemb a b) i j + E i j := by
            rw [hmul]
      _ =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail) i j +
            matMulRect (m + 1) (m + 1) (m + 1) P Δemb i j +
            E i j := by
            rw [← congr_fun
              (congr_fun
                (matMulRect_add_right (m + 1) (m + 1) (m + 1)
                  P (embedTrailingOne Qtail) Δemb) i) j]
      _ = Q_ref i j + ΔQ i j := by
            rw [hQ_ref]
            simp [ΔQ, matMul, matMulRect]
            ring_nf
  · have hΔQ_triangle :
        frobNorm ΔQ ≤
          frobNorm (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) +
            frobNorm E := by
      show frobNorm
          (fun i j =>
            matMulRect (m + 1) (m + 1) (m + 1) P Δemb i j + E i j) ≤ _
      exact norm_add_le
        (Matrix.of (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
        (Matrix.of E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    have hPΔ :
        frobNorm (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) =
          frobNorm Δemb :=
      frobNorm_orthogonal_left_rect P Δemb hP
    have hΔemb : frobNorm Δemb = frobNorm ΔT :=
      frobNorm_panelTrailingPerturbation ΔT
    calc
      frobNorm ΔQ
          ≤ frobNorm (matMulRect (m + 1) (m + 1) (m + 1) P Δemb) +
              frobNorm E := hΔQ_triangle
      _ = frobNorm ΔT + frobNorm E := by rw [hPΔ, hΔemb]
      _ ≤ ηtail + c * frobNorm (embedTrailingOne Qtail_hat) :=
          add_le_add hΔT hE

/-- One-step extension for fixed-reference accumulated `Q_hat` errors using
    the closed recursive bound. -/
theorem HouseholderQRPanelQhatFixedAccumError.cons_closed {m : ℕ}
    {Qtail Qtail_hat : Fin m → Fin m → ℝ} {ηtail : ℝ}
    (hTail :
      HouseholderQRPanelQhatFixedAccumError m Qtail Qtail_hat ηtail)
    (P Q_ref Q_hat : Fin (m + 1) → Fin (m + 1) → ℝ) (c : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hc : 0 ≤ c)
    (hQ_ref :
      Q_ref = matMul (m + 1) P (embedTrailingOne Qtail))
    (hStep : ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j : Fin (m + 1),
        Q_hat i j =
          matMulRect (m + 1) (m + 1) (m + 1) P
            (embedTrailingOne Qtail_hat) i j + E i j) ∧
      frobNorm E ≤ c * frobNorm (embedTrailingOne Qtail_hat)) :
    HouseholderQRPanelQhatFixedAccumError (m + 1) Q_ref Q_hat
      (ηtail + c * (Real.sqrt ((m + 1 : ℕ) : ℝ) + ηtail)) := by
  have hRaw :=
    HouseholderQRPanelQhatFixedAccumError.cons hTail P Q_ref Q_hat c hP
      hQ_ref hStep
  have htailNorm :=
    HouseholderQRPanelQhatAccumError.embedTrailingOne_norm_le hTail.toAccum
  refine hRaw.mono ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left htailNorm hc) ηtail

/-- Square specialization of the rounded accumulated Householder QR `Q_hat`
    algorithm. -/
noncomputable def fl_householderQR_Qhat_safe (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fl_householderQRPanel_Qhat_safe fp n n A

/-- Public concrete computed-factor object for the current Householder QR
    implementation.

    `Q_hat` is the rounded accumulated factor produced by applying the rounded
    reflector sequence to an identity-style accumulator.  `R_hat` is the
    zero-aware rounded `R` output.  The current proved backward-error theorem is
    still attached to the exact witness API `HouseholderQRWitness`; this object
    records the concrete `(Q_hat, R_hat)` API that the next proof layer should
    analyze. -/
structure HouseholderQRComputedFactors (n : ℕ) where
  /-- Rounded accumulated Householder `Q_hat`. -/
  Q_hat : Fin n → Fin n → ℝ
  /-- Concrete rounded zero-aware `R_hat`. -/
  R_hat : Fin n → Fin n → ℝ

/-- Concrete rounded `(Q_hat, R_hat)` pair for the zero-aware Householder QR
    implementation. -/
noncomputable def fl_householderQR_computed_safe (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : HouseholderQRComputedFactors n :=
  { Q_hat := fl_householderQR_Qhat_safe fp n A
    R_hat := fl_householderQR_R_safe fp n A }

@[simp] theorem fl_householderQR_computed_safe_Q_hat (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    (fl_householderQR_computed_safe fp n A).Q_hat =
      fl_householderQR_Qhat_safe fp n A := rfl

@[simp] theorem fl_householderQR_computed_safe_R_hat (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    (fl_householderQR_computed_safe fp n A).R_hat =
      fl_householderQR_R_safe fp n A := rfl

/-- Recursive readiness predicate for the concrete Householder QR `R` panel
    algorithm.

    Each nonempty active panel needs a nonzero first column and the gamma
    validity condition required by the concrete first-column Householder
    construction/application bridge.  The predicate then recurses on the
    computed trailing panel used by `fl_householderQRPanel_R`. -/
def HouseholderQRPanelReady (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Prop
  | 0, _, _ => True
  | Nat.succ _, 0, _ => True
  | m + 1, p + 1, A =>
      panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
      gammaValid fp (11 * (m + 1) + 23) ∧
      HouseholderQRPanelReady fp m p (fl_householderTrailingPanelStep fp A)

@[simp] theorem HouseholderQRPanelReady_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    HouseholderQRPanelReady fp 0 p A := by
  trivial

@[simp] theorem HouseholderQRPanelReady_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    HouseholderQRPanelReady fp (m + 1) 0 A := by
  trivial

@[simp] theorem HouseholderQRPanelReady_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    HouseholderQRPanelReady fp (m + 1) (p + 1) A ↔
      panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
      gammaValid fp (11 * (m + 1) + 23) ∧
      HouseholderQRPanelReady fp m p (fl_householderTrailingPanelStep fp A) := by
  rfl

/-- Readiness predicate for the zero-aware Householder QR panel algorithm.

    Unlike `HouseholderQRPanelReady`, this predicate does not require every
    active first column to be nonzero.  A zero active column is handled by an
    exact skip branch; only the nonzero branch needs the gamma-validity
    hypothesis required by the rounded Householder construction/application
    theorem. -/
def HouseholderQRPanelSafeReady (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → Prop
  | 0, _, _ => True
  | Nat.succ _, 0, _ => True
  | m + 1, p + 1, A =>
      if panelFirstColumn (Nat.succ_pos p) A = 0 then
        HouseholderQRPanelSafeReady fp m p (trailingPanel A)
      else
        gammaValid fp (11 * (m + 1) + 23) ∧
        HouseholderQRPanelSafeReady fp m p (fl_householderTrailingPanelStep fp A)

@[simp] theorem HouseholderQRPanelSafeReady_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) :
    HouseholderQRPanelSafeReady fp 0 p A := by
  trivial

@[simp] theorem HouseholderQRPanelSafeReady_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) :
    HouseholderQRPanelSafeReady fp (m + 1) 0 A := by
  trivial

@[simp] theorem HouseholderQRPanelSafeReady_succ_succ_zero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    HouseholderQRPanelSafeReady fp (m + 1) (p + 1) A ↔
      HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
  simp [HouseholderQRPanelSafeReady, hcol]

@[simp] theorem HouseholderQRPanelSafeReady_succ_succ_nonzero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    HouseholderQRPanelSafeReady fp (m + 1) (p + 1) A ↔
      gammaValid fp (11 * (m + 1) + 23) ∧
      HouseholderQRPanelSafeReady fp m p (fl_householderTrailingPanelStep fp A) := by
  simp [HouseholderQRPanelSafeReady, hcol]

/-- Recursive accumulated perturbation theorem for the rounded `Q_hat` panel
    algorithm.

    Under the same zero-aware readiness predicate used by `R_safe`, the
    concrete rounded accumulator `fl_householderQRPanel_Qhat_safe` is an exact
    orthogonal matrix plus a perturbation bounded by the raw recursive
    accumulator `householderQRPanel_QhatAccumBound`. -/
theorem fl_householderQRPanel_Qhat_safe_accum_error (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelSafeReady fp m p A →
      HouseholderQRPanelQhatAccumError m
        (fl_householderQRPanel_Qhat_safe fp m p A)
        (householderQRPanel_QhatAccumBound fp m p A) := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      let Z : Fin 0 → Fin 0 → ℝ := fun i _ => Fin.elim0 i
      refine ⟨⟨idMatrix 0, Z, idMatrix_orthogonal 0, ?_, ?_⟩⟩
      · intro i
        exact Fin.elim0 i
      · have hZ : frobNorm Z = 0 := by
          rw [frobNorm_eq_zero_iff]
          intro i
          exact Fin.elim0 i
        simp [Z, hZ]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          let Z : Fin (m + 1) → Fin (m + 1) → ℝ := fun _ _ => 0
          refine ⟨⟨idMatrix (m + 1), Z, idMatrix_orthogonal (m + 1), ?_, ?_⟩⟩
          · intro i j
            simp [fl_householderQRPanel_Qhat_safe, Z]
          · have hZ : frobNorm Z = 0 := by
              rw [frobNorm_eq_zero_iff]
              intro i j
              rfl
            simp [householderQRPanel_QhatAccumBound, Z, hZ]
      | succ p =>
          intro A hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailBase :=
              ih p (trailingPanel A) htailReady
            have hTail :
                HouseholderQRPanelQhatAccumError m
                  (fl_householderQRPanel_Qhat_tail_safe fp A)
                  (householderQRPanel_QhatAccumBound fp m p
                    (fl_householderTrailingPanelStepSafe fp A)) := by
              simpa [fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using hTailBase
            have hStep :
                ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
                  (∀ i j : Fin (m + 1),
                    fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A i j =
                      matMulRect (m + 1) (m + 1) (m + 1)
                        (householderQRPanel_Qhat_stepP_safe A)
                        (embedTrailingOne
                          (fl_householderQRPanel_Qhat_tail_safe fp A)) i j +
                        E i j) ∧
                  frobNorm E ≤
                    householderQRPanel_Qhat_stepCoeff_safe fp A *
                      frobNorm
                        (embedTrailingOne
                          (fl_householderQRPanel_Qhat_tail_safe fp A)) := by
              simpa [householderQRPanel_Qhat_stepP_safe,
                householderQRPanel_Qhat_stepCoeff_safe,
                fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using
                fl_householderQRPanel_Qhat_safe_succ_succ_zero_residual_bound
                  fp A hcol
            have hP :
                IsOrthogonal (m + 1) (householderQRPanel_Qhat_stepP_safe A) := by
              simpa [householderQRPanel_Qhat_stepP_safe, hcol] using
                idMatrix_orthogonal (m + 1)
            have hCons :=
              HouseholderQRPanelQhatAccumError.cons hTail
                (householderQRPanel_Qhat_stepP_safe A)
                (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
                (householderQRPanel_Qhat_stepCoeff_safe fp A) hP hStep
            simpa [householderQRPanel_QhatAccumBound] using hCons
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailBase :=
              ih p (fl_householderTrailingPanelStep fp A) hready'.2
            have hTail :
                HouseholderQRPanelQhatAccumError m
                  (fl_householderQRPanel_Qhat_tail_safe fp A)
                  (householderQRPanel_QhatAccumBound fp m p
                    (fl_householderTrailingPanelStepSafe fp A)) := by
              simpa [fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using hTailBase
            have hStep :=
              fl_householderQRPanel_Qhat_safe_succ_succ_residual_bound
                fp A hready'.1
            have hP :=
              householderQRPanel_Qhat_stepP_safe_orthogonal fp A hready'.1
            have hCons :=
              HouseholderQRPanelQhatAccumError.cons hTail
                (householderQRPanel_Qhat_stepP_safe A)
                (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
                (householderQRPanel_Qhat_stepCoeff_safe fp A) hP hStep
            simpa [householderQRPanel_QhatAccumBound] using hCons

/-- Recursive accumulated perturbation theorem for the rounded `Q_hat` panel
    algorithm using the closed recursive bound.

    Compared with `fl_householderQRPanel_Qhat_safe_accum_error`, this statement
    removes the explicit dependence on the actual embedded tail accumulator norm
    from the bound.  Each step instead uses
    `sqrt (m + 1) + ηtail`, where `ηtail` is the already accumulated tail
    perturbation bound. -/
theorem fl_householderQRPanel_Qhat_safe_closed_accum_error (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelSafeReady fp m p A →
      HouseholderQRPanelQhatAccumError m
        (fl_householderQRPanel_Qhat_safe fp m p A)
        (householderQRPanel_QhatClosedBound fp m p A) := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      let Z : Fin 0 → Fin 0 → ℝ := fun i _ => Fin.elim0 i
      refine ⟨⟨idMatrix 0, Z, idMatrix_orthogonal 0, ?_, ?_⟩⟩
      · intro i
        exact Fin.elim0 i
      · have hZ : frobNorm Z = 0 := by
          rw [frobNorm_eq_zero_iff]
          intro i
          exact Fin.elim0 i
        simp [Z, hZ]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          let Z : Fin (m + 1) → Fin (m + 1) → ℝ := fun _ _ => 0
          refine ⟨⟨idMatrix (m + 1), Z, idMatrix_orthogonal (m + 1), ?_, ?_⟩⟩
          · intro i j
            simp [fl_householderQRPanel_Qhat_safe, Z]
          · have hZ : frobNorm Z = 0 := by
              rw [frobNorm_eq_zero_iff]
              intro i j
              rfl
            simp [householderQRPanel_QhatClosedBound, Z, hZ]
      | succ p =>
          intro A hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailBase :=
              ih p (trailingPanel A) htailReady
            have hTail :
                HouseholderQRPanelQhatAccumError m
                  (fl_householderQRPanel_Qhat_tail_safe fp A)
                  (householderQRPanel_QhatClosedBound fp m p
                    (fl_householderTrailingPanelStepSafe fp A)) := by
              simpa [fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using hTailBase
            have hStep :
                ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
                  (∀ i j : Fin (m + 1),
                    fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A i j =
                      matMulRect (m + 1) (m + 1) (m + 1)
                        (householderQRPanel_Qhat_stepP_safe A)
                        (embedTrailingOne
                          (fl_householderQRPanel_Qhat_tail_safe fp A)) i j +
                        E i j) ∧
                  frobNorm E ≤
                    householderQRPanel_Qhat_stepCoeff_safe fp A *
                      frobNorm
                        (embedTrailingOne
                          (fl_householderQRPanel_Qhat_tail_safe fp A)) := by
              simpa [householderQRPanel_Qhat_stepP_safe,
                householderQRPanel_Qhat_stepCoeff_safe,
                fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using
                fl_householderQRPanel_Qhat_safe_succ_succ_zero_residual_bound
                  fp A hcol
            have hP :
                IsOrthogonal (m + 1) (householderQRPanel_Qhat_stepP_safe A) := by
              simpa [householderQRPanel_Qhat_stepP_safe, hcol] using
                idMatrix_orthogonal (m + 1)
            have hc : 0 ≤ householderQRPanel_Qhat_stepCoeff_safe fp A := by
              simp [householderQRPanel_Qhat_stepCoeff_safe, hcol]
            have hCons :=
              HouseholderQRPanelQhatAccumError.cons_closed hTail
                (householderQRPanel_Qhat_stepP_safe A)
                (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
                (householderQRPanel_Qhat_stepCoeff_safe fp A) hP hc hStep
            simpa [householderQRPanel_QhatClosedBound] using hCons
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailBase :=
              ih p (fl_householderTrailingPanelStep fp A) hready'.2
            have hTail :
                HouseholderQRPanelQhatAccumError m
                  (fl_householderQRPanel_Qhat_tail_safe fp A)
                  (householderQRPanel_QhatClosedBound fp m p
                    (fl_householderTrailingPanelStepSafe fp A)) := by
              simpa [fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using hTailBase
            have hStep :=
              fl_householderQRPanel_Qhat_safe_succ_succ_residual_bound
                fp A hready'.1
            have hP :=
              householderQRPanel_Qhat_stepP_safe_orthogonal fp A hready'.1
            have hc :=
              householderQRPanel_Qhat_stepCoeff_safe_nonneg fp A hready'.1
            have hCons :=
              HouseholderQRPanelQhatAccumError.cons_closed hTail
                (householderQRPanel_Qhat_stepP_safe A)
                (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
                (householderQRPanel_Qhat_stepCoeff_safe fp A) hP hc hStep
            simpa [householderQRPanel_QhatClosedBound] using hCons

/-- Recursive accumulated perturbation theorem for the rounded `Q_hat` panel
    algorithm with the exact reference factor fixed to `Q_safe`.

    This strengthens the existential accumulated theorem: the exact orthogonal
    matrix explaining the rounded `Q_hat` perturbation can be chosen to be the
    same recursive `fl_householderQRPanel_Q_safe` witness used by the
    Householder QR backward-error proof. -/
theorem fl_householderQRPanel_Qhat_safe_fixed_Q_safe_closed_accum_error
    (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelSafeReady fp m p A →
      HouseholderQRPanelQhatFixedAccumError m
        (fl_householderQRPanel_Q_safe fp m p A)
        (fl_householderQRPanel_Qhat_safe fp m p A)
        (householderQRPanel_QhatClosedBound fp m p A) := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      let Z : Fin 0 → Fin 0 → ℝ := fun i _ => Fin.elim0 i
      refine ⟨?_, ⟨Z, ?_, ?_⟩⟩
      · simpa [fl_householderQRPanel_Q_safe] using idMatrix_orthogonal 0
      · intro i
        exact Fin.elim0 i
      · have hZ : frobNorm Z = 0 := by
          rw [frobNorm_eq_zero_iff]
          intro i
          exact Fin.elim0 i
        simp [Z, hZ]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          let Z : Fin (m + 1) → Fin (m + 1) → ℝ := fun _ _ => 0
          refine ⟨?_, ⟨Z, ?_, ?_⟩⟩
          · simpa [fl_householderQRPanel_Q_safe] using
              idMatrix_orthogonal (m + 1)
          · intro i j
            simp [fl_householderQRPanel_Q_safe,
              fl_householderQRPanel_Qhat_safe, Z]
          · have hZ : frobNorm Z = 0 := by
              rw [frobNorm_eq_zero_iff]
              intro i j
              rfl
            simp [householderQRPanel_QhatClosedBound, Z, hZ]
      | succ p =>
          intro A hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailBase :=
              ih p (trailingPanel A) htailReady
            have hTail :
                HouseholderQRPanelQhatFixedAccumError m
                  (fl_householderQRPanel_Q_safe fp m p
                    (fl_householderTrailingPanelStepSafe fp A))
                  (fl_householderQRPanel_Qhat_tail_safe fp A)
                  (householderQRPanel_QhatClosedBound fp m p
                    (fl_householderTrailingPanelStepSafe fp A)) := by
              simpa [fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using hTailBase
            have hStep :
                ∃ E : Fin (m + 1) → Fin (m + 1) → ℝ,
                  (∀ i j : Fin (m + 1),
                    fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A i j =
                      matMulRect (m + 1) (m + 1) (m + 1)
                        (householderQRPanel_Qhat_stepP_safe A)
                        (embedTrailingOne
                          (fl_householderQRPanel_Qhat_tail_safe fp A)) i j +
                        E i j) ∧
                  frobNorm E ≤
                    householderQRPanel_Qhat_stepCoeff_safe fp A *
                      frobNorm
                        (embedTrailingOne
                          (fl_householderQRPanel_Qhat_tail_safe fp A)) := by
              simpa [householderQRPanel_Qhat_stepP_safe,
                householderQRPanel_Qhat_stepCoeff_safe,
                fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using
                fl_householderQRPanel_Qhat_safe_succ_succ_zero_residual_bound
                  fp A hcol
            have hP :
                IsOrthogonal (m + 1) (householderQRPanel_Qhat_stepP_safe A) := by
              simpa [householderQRPanel_Qhat_stepP_safe, hcol] using
                idMatrix_orthogonal (m + 1)
            have hc : 0 ≤ householderQRPanel_Qhat_stepCoeff_safe fp A := by
              simp [householderQRPanel_Qhat_stepCoeff_safe, hcol]
            have hQref :=
              fl_householderQRPanel_Q_safe_succ_succ_as_stepP_safe fp A
            have hCons :=
              HouseholderQRPanelQhatFixedAccumError.cons_closed hTail
                (householderQRPanel_Qhat_stepP_safe A)
                (fl_householderQRPanel_Q_safe fp (m + 1) (p + 1) A)
                (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
                (householderQRPanel_Qhat_stepCoeff_safe fp A) hP hc hQref hStep
            simpa [householderQRPanel_QhatClosedBound] using hCons
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailBase :=
              ih p (fl_householderTrailingPanelStep fp A) hready'.2
            have hTail :
                HouseholderQRPanelQhatFixedAccumError m
                  (fl_householderQRPanel_Q_safe fp m p
                    (fl_householderTrailingPanelStepSafe fp A))
                  (fl_householderQRPanel_Qhat_tail_safe fp A)
                  (householderQRPanel_QhatClosedBound fp m p
                    (fl_householderTrailingPanelStepSafe fp A)) := by
              simpa [fl_householderQRPanel_Qhat_tail_safe,
                fl_householderTrailingPanelStepSafe, hcol] using hTailBase
            have hStep :=
              fl_householderQRPanel_Qhat_safe_succ_succ_residual_bound
                fp A hready'.1
            have hP :=
              householderQRPanel_Qhat_stepP_safe_orthogonal fp A hready'.1
            have hc :=
              householderQRPanel_Qhat_stepCoeff_safe_nonneg fp A hready'.1
            have hQref :=
              fl_householderQRPanel_Q_safe_succ_succ_as_stepP_safe fp A
            have hCons :=
              HouseholderQRPanelQhatFixedAccumError.cons_closed hTail
                (householderQRPanel_Qhat_stepP_safe A)
                (fl_householderQRPanel_Q_safe fp (m + 1) (p + 1) A)
                (fl_householderQRPanel_Qhat_safe fp (m + 1) (p + 1) A)
                (householderQRPanel_Qhat_stepCoeff_safe fp A) hP hc hQref hStep
            simpa [householderQRPanel_QhatClosedBound] using hCons

/-- A single global gamma-validity hypothesis supplies all branch-local
    gamma-validity assumptions needed by the zero-aware Householder QR panel
    algorithm.

    Zero active columns require no rounded reflector theorem.  Nonzero active
    columns use `gammaValid fp (11 * rows + 23)`, which follows by monotonicity
    from the global row bound. -/
theorem HouseholderQRPanelSafeReady_of_global_gammaValid (fp : FPModel) :
    ∀ (m p N : ℕ) (A : Fin m → Fin p → ℝ),
      m ≤ N →
      gammaValid fp (11 * N + 23) →
      HouseholderQRPanelSafeReady fp m p A := by
  intro m
  induction m with
  | zero =>
      intro p N A _hrows _hvalid
      trivial
  | succ m ih =>
      intro p N A hrows hvalid
      cases p with
      | zero =>
          trivial
      | succ p =>
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htail :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) :=
              ih p N (trailingPanel A) (by omega) hvalid
            simpa [HouseholderQRPanelSafeReady, hcol] using htail
          · have hstep : gammaValid fp (11 * (m + 1) + 23) :=
              gammaValid_mono fp (by omega) hvalid
            have htail :
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) :=
              ih p N (fl_householderTrailingPanelStep fp A) (by omega) hvalid
            simpa [HouseholderQRPanelSafeReady, hcol] using ⟨hstep, htail⟩

/-- Square specialization of
    `HouseholderQRPanelSafeReady_of_global_gammaValid`. -/
theorem HouseholderQRPanelSafeReady_square_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelSafeReady fp n n A :=
  HouseholderQRPanelSafeReady_of_global_gammaValid fp n n n A
    (le_refl n) hvalid

/-- Square specialization of the accumulated perturbation theorem for the
    rounded `Q_hat` algorithm. -/
theorem fl_householderQR_Qhat_safe_accum_error
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelSafeReady fp n n A) :
    HouseholderQRPanelQhatAccumError n
      (fl_householderQR_Qhat_safe fp n A)
      (householderQRPanel_QhatAccumBound fp n n A) := by
  simpa [fl_householderQR_Qhat_safe] using
    fl_householderQRPanel_Qhat_safe_accum_error fp n n A hready

/-- Global-gamma wrapper for the accumulated perturbation theorem for the
    rounded `Q_hat` algorithm. -/
theorem fl_householderQR_Qhat_safe_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatAccumError n
      (fl_householderQR_Qhat_safe fp n A)
      (householderQRPanel_QhatAccumBound fp n n A) := by
  exact fl_householderQR_Qhat_safe_accum_error fp n A
    (HouseholderQRPanelSafeReady_square_of_global_gammaValid fp n A hvalid)

/-- The `Q_hat` field of the concrete computed-factor API is an exact
    orthogonal matrix plus a bounded accumulated perturbation. -/
theorem fl_householderQR_computed_safe_Q_hat_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatAccumError n
      (fl_householderQR_computed_safe fp n A).Q_hat
      (householderQRPanel_QhatAccumBound fp n n A) := by
  simpa [fl_householderQR_computed_safe] using
    fl_householderQR_Qhat_safe_accum_error_of_global_gammaValid fp n A hvalid

/-- Square specialization of the closed accumulated perturbation theorem for
    the rounded `Q_hat` algorithm. -/
theorem fl_householderQR_Qhat_safe_closed_accum_error
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelSafeReady fp n n A) :
    HouseholderQRPanelQhatAccumError n
      (fl_householderQR_Qhat_safe fp n A)
      (householderQRPanel_QhatClosedBound fp n n A) := by
  simpa [fl_householderQR_Qhat_safe] using
    fl_householderQRPanel_Qhat_safe_closed_accum_error fp n n A hready

/-- Global-gamma wrapper for the closed accumulated perturbation theorem for
    the rounded `Q_hat` algorithm. -/
theorem fl_householderQR_Qhat_safe_closed_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatAccumError n
      (fl_householderQR_Qhat_safe fp n A)
      (householderQRPanel_QhatClosedBound fp n n A) := by
  exact fl_householderQR_Qhat_safe_closed_accum_error fp n A
    (HouseholderQRPanelSafeReady_square_of_global_gammaValid fp n A hvalid)

/-- The `Q_hat` field of the concrete computed-factor API is an exact
    orthogonal matrix plus a perturbation bounded by the closed recursive
    accumulated `Q_hat` bound. -/
theorem fl_householderQR_computed_safe_Q_hat_closed_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatAccumError n
      (fl_householderQR_computed_safe fp n A).Q_hat
      (householderQRPanel_QhatClosedBound fp n n A) := by
  simpa [fl_householderQR_computed_safe] using
    fl_householderQR_Qhat_safe_closed_accum_error_of_global_gammaValid
      fp n A hvalid

/-- Square specialization of the fixed-`Q_safe` closed accumulated
    perturbation theorem for the rounded `Q_hat` algorithm. -/
theorem fl_householderQR_Qhat_safe_fixed_Q_safe_closed_accum_error
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelSafeReady fp n n A) :
    HouseholderQRPanelQhatFixedAccumError n
      (fl_householderQR_Q_safe fp n A)
      (fl_householderQR_Qhat_safe fp n A)
      (householderQRPanel_QhatClosedBound fp n n A) := by
  simpa [fl_householderQR_Q_safe, fl_householderQR_Qhat_safe] using
    fl_householderQRPanel_Qhat_safe_fixed_Q_safe_closed_accum_error
      fp n n A hready

/-- Global-gamma wrapper for the fixed-`Q_safe` closed accumulated
    perturbation theorem for the rounded `Q_hat` algorithm. -/
theorem fl_householderQR_Qhat_safe_fixed_Q_safe_closed_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatFixedAccumError n
      (fl_householderQR_Q_safe fp n A)
      (fl_householderQR_Qhat_safe fp n A)
      (householderQRPanel_QhatClosedBound fp n n A) := by
  exact fl_householderQR_Qhat_safe_fixed_Q_safe_closed_accum_error fp n A
    (HouseholderQRPanelSafeReady_square_of_global_gammaValid fp n A hvalid)

/-- The `Q_hat` field of the concrete computed-factor API differs from the
    exact `Q` field of the safe witness by a perturbation bounded by the closed
    recursive accumulated `Q_hat` bound. -/
theorem fl_householderQR_computed_safe_Q_hat_fixed_Q_safe_closed_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatFixedAccumError n
      (fl_householderQR_safe_witness fp n A).Q
      (fl_householderQR_computed_safe fp n A).Q_hat
      (householderQRPanel_QhatClosedBound fp n n A) := by
  simpa [fl_householderQR_safe_witness, fl_householderQR_computed_safe] using
    fl_householderQR_Qhat_safe_fixed_Q_safe_closed_accum_error_of_global_gammaValid
      fp n A hvalid

/-- Panel theorem bounding the fixed-`Q_safe` accumulated `Q_hat` perturbation
    by the dimension-only uniform recursive bound. -/
theorem fl_householderQRPanel_Qhat_safe_fixed_Q_safe_uniform_accum_error
    (fp : FPModel) (m p N : ℕ) (A : Fin m → Fin p → ℝ)
    (hmN : m ≤ N)
    (hvalid : gammaValid fp (11 * N + 23)) :
    HouseholderQRPanelQhatFixedAccumError m
      (fl_householderQRPanel_Q_safe fp m p A)
      (fl_householderQRPanel_Qhat_safe fp m p A)
      (householderQR_QhatUniformClosedBound fp N m) := by
  have hready :
      HouseholderQRPanelSafeReady fp m p A :=
    HouseholderQRPanelSafeReady_of_global_gammaValid fp m p N A hmN hvalid
  have hFixed :=
    fl_householderQRPanel_Qhat_safe_fixed_Q_safe_closed_accum_error
      fp m p A hready
  have hBound :=
    householderQRPanel_QhatClosedBound_le_uniform fp m p N A hmN hvalid
  exact hFixed.mono hBound

/-- Square/global wrapper for the dimension-only uniform accumulated `Q_hat`
    perturbation bound with fixed `Q_safe` reference. -/
theorem fl_householderQR_Qhat_safe_fixed_Q_safe_uniform_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatFixedAccumError n
      (fl_householderQR_Q_safe fp n A)
      (fl_householderQR_Qhat_safe fp n A)
      (householderQR_QhatUniformClosedBound fp n n) := by
  simpa [fl_householderQR_Q_safe, fl_householderQR_Qhat_safe] using
    fl_householderQRPanel_Qhat_safe_fixed_Q_safe_uniform_accum_error
      fp n n n A (le_refl n) hvalid

/-- The computed-factor `Q_hat` field differs from the safe witness `Q` field
    by a perturbation bounded by the dimension-only uniform recursive bound. -/
theorem fl_householderQR_computed_safe_Q_hat_fixed_Q_safe_uniform_accum_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelQhatFixedAccumError n
      (fl_householderQR_safe_witness fp n A).Q
      (fl_householderQR_computed_safe fp n A).Q_hat
      (householderQR_QhatUniformClosedBound fp n n) := by
  simpa [fl_householderQR_safe_witness, fl_householderQR_computed_safe] using
    fl_householderQR_Qhat_safe_fixed_Q_safe_uniform_accum_error_of_global_gammaValid
      fp n A hvalid

/-- Active trailing-panel state for a Householder QR loop.

    This state tracks only the active panel dimensions and entries.  It is a
    legacy loop scaffold for local step reasoning; the final implementation-
    backed `R` theorems below use the direct recursive panel algorithms
    `fl_householderQRPanel_R` and `fl_householderQRPanel_R_safe`. -/
structure HouseholderPanelState where
  /-- Number of active panel rows. -/
  rows : ℕ
  /-- Number of active panel columns. -/
  cols : ℕ
  /-- Active panel entries. -/
  panel : Fin rows → Fin cols → ℝ

/-- One concrete active-panel step in the shrinking Householder QR loop.

    If both dimensions are nonzero, apply the concrete first-column Householder
    update and keep the trailing panel.  If either dimension is zero, leave the
    state unchanged. -/
noncomputable def householderPanelStateStep (fp : FPModel)
    (S : HouseholderPanelState) : HouseholderPanelState :=
  match S with
  | ⟨m + 1, p + 1, A⟩ =>
      ⟨m, p, fl_householderTrailingPanelStep fp A⟩
  | S => S

/-- Iterate the concrete active-panel shrinking step. -/
noncomputable def householderPanelStateIterate (fp : FPModel) :
    ℕ → HouseholderPanelState → HouseholderPanelState
  | 0, S => S
  | k + 1, S => householderPanelStateIterate fp k
      (householderPanelStateStep fp S)

/-- Per-step hypotheses needed to apply the implementation-backed Householder
    panel bridge to an active panel state.

    Empty-row or empty-column states require no further QR panel step.  A
    nonempty active panel needs a nonzero first column and the gamma-validity
    condition for the current row dimension. -/
def HouseholderPanelStepReady (fp : FPModel)
    (S : HouseholderPanelState) : Prop :=
  match S with
  | ⟨m + 1, p + 1, A⟩ =>
      panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
      gammaValid fp (11 * (m + 1) + 23)
  | _ => True

/-- Every step in a finite active-panel run has the hypotheses needed by the
    one-step implementation-backed bridge. -/
def HouseholderPanelRunReady (fp : FPModel)
    (r : ℕ) (S : HouseholderPanelState) : Prop :=
  ∀ k : ℕ, k < r →
    HouseholderPanelStepReady fp (householderPanelStateIterate fp k S)

@[simp] theorem householderPanelStateStep_nonempty (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    householderPanelStateStep fp ⟨m + 1, p + 1, A⟩ =
      ⟨m, p, fl_householderTrailingPanelStep fp A⟩ := rfl

@[simp] theorem householderPanelStateIterate_zero (fp : FPModel)
    (S : HouseholderPanelState) :
    householderPanelStateIterate fp 0 S = S := rfl

@[simp] theorem householderPanelStateIterate_succ (fp : FPModel)
    (k : ℕ) (S : HouseholderPanelState) :
    householderPanelStateIterate fp (k + 1) S =
      householderPanelStateIterate fp k (householderPanelStateStep fp S) := rfl

@[simp] theorem householderPanelStepReady_nonempty (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    HouseholderPanelStepReady fp ⟨m + 1, p + 1, A⟩ ↔
      panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
      gammaValid fp (11 * (m + 1) + 23) := by
  rfl

/-- A global gamma-validity assumption for a larger row dimension supplies the
    per-step gamma-validity needed by a smaller active panel. -/
theorem householderPanelStepReady_nonempty_of_global_gammaValid
    (fp : FPModel) {m p N : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hrows : m + 1 ≤ N)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * N + 23)) :
    HouseholderPanelStepReady fp ⟨m + 1, p + 1, A⟩ := by
  refine ⟨hx, ?_⟩
  exact gammaValid_mono fp (by omega) hvalid

theorem householderPanelRunReady_zero (fp : FPModel)
    (S : HouseholderPanelState) :
    HouseholderPanelRunReady fp 0 S := by
  intro k hk
  exact False.elim ((Nat.not_lt_zero k) hk)

/-- The first step of a nonempty ready run is ready. -/
theorem householderPanelRunReady_head (fp : FPModel)
    {r : ℕ} {S : HouseholderPanelState}
    (h : HouseholderPanelRunReady fp (r + 1) S) :
    HouseholderPanelStepReady fp S := by
  exact h 0 (Nat.succ_pos r)

/-- The tail of a ready run is ready after performing the first step. -/
theorem householderPanelRunReady_tail (fp : FPModel)
    {r : ℕ} {S : HouseholderPanelState}
    (h : HouseholderPanelRunReady fp (r + 1) S) :
    HouseholderPanelRunReady fp r (householderPanelStateStep fp S) := by
  intro k hk
  simpa [HouseholderPanelRunReady] using h (k + 1) (Nat.succ_lt_succ hk)

/-- Split a nonempty ready run into the current ready step and the ready tail.
    This is the induction shape needed by repeated-panel proofs. -/
theorem householderPanelRunReady_succ_iff (fp : FPModel)
    {r : ℕ} {S : HouseholderPanelState} :
    HouseholderPanelRunReady fp (r + 1) S ↔
      HouseholderPanelStepReady fp S ∧
      HouseholderPanelRunReady fp r (householderPanelStateStep fp S) := by
  constructor
  · intro h
    exact ⟨householderPanelRunReady_head fp h,
      householderPanelRunReady_tail fp h⟩
  · intro h k hk
    cases k with
    | zero =>
        simpa using h.1
    | succ k =>
        have hk_tail : k < r := Nat.succ_lt_succ_iff.mp hk
        simpa [HouseholderPanelRunReady] using h.2 k hk_tail

/-- If a full nonempty panel is updated by the concrete first-column
    Householder step, then the next trailing panel is exactly
    `fl_householderTrailingPanelStep`. -/
theorem trailingPanel_first_column_panel_step_eq
    (fp : FPModel) {m p : ℕ}
    (A A_next : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hAstep :
      A_next =
        fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A) :
    trailingPanel A_next = fl_householderTrailingPanelStep fp A := by
  rw [hAstep]
  rfl

/-- One concrete Householder panel step where the reflector is constructed from
    the first column of the current panel.

    This is still only the first-column panel bridge, not the full QR loop:
    later QR code must show that successive trailing panels are formed from the
    previous update and that the first-column choice matches the mathematical
    QR iteration. -/
theorem fl_householder_first_column_panel_step_error (fp : FPModel)
    {m p : ℕ}
    (hm0 : 0 < m) (hp0 : 0 < p) (A : Fin m → Fin p → ℝ)
    (hx : panelFirstColumn hp0 A ≠ 0)
    (hvalid : gammaValid fp (11 * m + 23)) :
    ColumnwiseHouseholderStepErrorRect m p
      (householder m
        (householderNormalizedVector m
          (householderVector hm0 (panelFirstColumn hp0 A))
          (householderBetaFromScale hm0 (panelFirstColumn hp0 A))) 1)
      A
      (fl_householderApplyMatrixRect fp m p
        (fl_householderNormalizedVector fp hm0 (panelFirstColumn hp0 A)) 1 A)
      (householderConstructApplyBound fp m) := by
  simpa [householderConstructApplyBound] using
    fl_householderConstructApply_matrix_step_error_rect fp hm0
      (panelFirstColumn hp0 A) A hx hvalid

/-- The explicit exact `Q` witness associated with the zero-aware rounded
    Householder QR panel algorithm is orthogonal.

    This proves the first `Q`-side bridge: the recursive object
    `fl_householderQRPanel_Q_safe` is a genuine exact orthogonal matrix for the
    same safe branch choices used by `fl_householderQRPanel_R_safe`. -/
theorem fl_householderQRPanel_Q_safe_orthogonal (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelSafeReady fp m p A →
      IsOrthogonal m (fl_householderQRPanel_Q_safe fp m p A) := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      simpa [fl_householderQRPanel_Q_safe] using idMatrix_orthogonal 0
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          simpa [fl_householderQRPanel_Q_safe] using idMatrix_orthogonal (m + 1)
      | succ p =>
          intro A hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hQt :
                IsOrthogonal m
                  (fl_householderQRPanel_Q_safe fp m p (trailingPanel A)) :=
              ih p (trailingPanel A) htailReady
            simpa [fl_householderQRPanel_Q_safe, hcol] using
              embedTrailingOne_orthogonal
                (fl_householderQRPanel_Q_safe fp m p (trailingPanel A)) hQt
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
              householder (m + 1)
                (householderNormalizedVector (m + 1)
                  (householderVector (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))
                  (householderBetaFromScale (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))) 1
            let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
              fl_householderApplyMatrixRect fp (m + 1) (p + 1)
                (fl_householderNormalizedVector fp (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A)) 1 A
            let Qt : Fin m → Fin m → ℝ :=
              fl_householderQRPanel_Q_safe fp m p (trailingPanel Astep)
            have htailReady' :
                HouseholderQRPanelSafeReady fp m p (trailingPanel Astep) := by
              simpa [Astep, fl_householderTrailingPanelStep] using hready'.2
            have hQt : IsOrthogonal m Qt := by
              simpa [Qt] using ih p (trailingPanel Astep) htailReady'
            have hEmb :
                IsOrthogonal (m + 1)
                  (embedTrailingOne (matTranspose Qt)) :=
              embedTrailingOne_orthogonal (matTranspose Qt) hQt.transpose
            have hP : IsOrthogonal (m + 1) P := by
              have hstep :=
                fl_householder_first_column_panel_step_error fp
                  (Nat.succ_pos m) (Nat.succ_pos p) A hcol hready'.1
              simpa [P, householderConstructApplyBound] using hstep.orth
            have hM :
                IsOrthogonal (m + 1)
                  (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P) :=
              hEmb.mul hP
            simpa [fl_householderQRPanel_Q_safe, hcol, P, Astep, Qt] using
              hM.transpose

/-- Square specialization: the explicit exact `Q` witness associated with
    `fl_householderQR_R_safe` is orthogonal. -/
theorem fl_householderQR_Q_safe_orthogonal (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelSafeReady fp n n A) :
    IsOrthogonal n (fl_householderQR_Q_safe fp n A) := by
  simpa [fl_householderQR_Q_safe] using
    fl_householderQRPanel_Q_safe_orthogonal fp n n A hready

/-- Global-gamma wrapper for orthogonality of the explicit exact `Q` witness
    associated with the zero-aware Householder QR `R` algorithm. -/
theorem fl_householderQR_Q_safe_orthogonal_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    IsOrthogonal n (fl_householderQR_Q_safe fp n A) := by
  exact fl_householderQR_Q_safe_orthogonal fp n A
    (HouseholderQRPanelSafeReady_square_of_global_gammaValid fp n A hvalid)

/-- Exact first-column value after applying the constructed Householder
    reflector to a panel. -/
theorem householder_first_column_panel_exact_first
    {m p : ℕ} (hm0 : 0 < m) (hp0 : 0 < p)
    (A : Fin m → Fin p → ℝ) (hx : panelFirstColumn hp0 A ≠ 0) :
    matMulRect m m p
      (householder m
        (householderNormalizedVector m
          (householderVector hm0 (panelFirstColumn hp0 A))
          (householderBetaFromScale hm0 (panelFirstColumn hp0 A))) 1)
      A ⟨0, hm0⟩ ⟨0, hp0⟩ =
        -householderScale hm0 (panelFirstColumn hp0 A) := by
  simpa [matMulRect, matMulVec, panelFirstColumn] using
    householder_constructed_matMulVec_first hm0 (panelFirstColumn hp0 A) hx

/-- Exact first-column tail zeroing after applying the constructed Householder
    reflector to a panel.  This is the exact triangularization fact for one
    Householder panel step. -/
theorem householder_first_column_panel_exact_tail_zero
    {m p : ℕ} (hm0 : 0 < m) (hp0 : 0 < p)
    (A : Fin m → Fin p → ℝ) (hx : panelFirstColumn hp0 A ≠ 0)
    (i : Fin m) (hi : i ≠ ⟨0, hm0⟩) :
    matMulRect m m p
      (householder m
        (householderNormalizedVector m
          (householderVector hm0 (panelFirstColumn hp0 A))
          (householderBetaFromScale hm0 (panelFirstColumn hp0 A))) 1)
      A i ⟨0, hp0⟩ = 0 := by
  simpa [matMulRect, matMulVec, panelFirstColumn] using
    householder_constructed_matMulVec_tail_zero hm0
      (panelFirstColumn hp0 A) hx i hi

/-- Exact top-left entry after a constructed Householder panel step. -/
theorem householder_panel_exact_topLeft
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    panelTopLeft
      (matMulRect (m + 1) (m + 1) (p + 1)
        (householder (m + 1)
          (householderNormalizedVector (m + 1)
            (householderVector (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))
            (householderBetaFromScale (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))) 1)
        A) =
      -householderScale (Nat.succ_pos m) (panelFirstColumn (Nat.succ_pos p) A) := by
  simpa [panelTopLeft] using
    householder_first_column_panel_exact_first
      (Nat.succ_pos m) (Nat.succ_pos p) A hx

/-- Exact first-column tail zeroing after a constructed Householder panel
    step, stated with the panel-decomposition predicate. -/
theorem householder_panel_exact_firstColumnTailZero
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    panelFirstColumnTailZero
      (matMulRect (m + 1) (m + 1) (p + 1)
        (householder (m + 1)
          (householderNormalizedVector (m + 1)
            (householderVector (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))
            (householderBetaFromScale (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A))) 1)
        A) := by
  intro i
  have hi :
      i.succ ≠ (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) :=
    Fin.succ_ne_zero i
  simpa [panelFirstColumnTailZero, panelFirstColumnTail] using
    householder_first_column_panel_exact_tail_zero
      (Nat.succ_pos m) (Nat.succ_pos p) A hx i.succ hi

/-- Concrete rounded first-column Householder panel step, packaged with both
    its residual bound and the exact triangularization shape of the underlying
    exact reflector step. -/
theorem fl_householder_first_column_panel_step_residual_and_shape
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    ∃ E : Fin (m + 1) → Fin (p + 1) → ℝ,
      (∀ i j,
        fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A i j =
          matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) ∧
      frobNorm E ≤ householderConstructApplyBound fp (m + 1) * frobNorm A ∧
      panelTopLeft (matMulRect (m + 1) (m + 1) (p + 1) P A) =
        -householderScale (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A) ∧
      panelFirstColumnTailZero
        (matMulRect (m + 1) (m + 1) (p + 1) P A) := by
  intro P
  have hstep :
      ColumnwiseHouseholderStepErrorRect (m + 1) (p + 1) P A
        (fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A)
        (householderConstructApplyBound fp (m + 1)) := by
    simpa [P] using
      fl_householder_first_column_panel_step_error fp
        (Nat.succ_pos m) (Nat.succ_pos p) A hx hvalid
  obtain ⟨E, hNext, hE⟩ :=
    hstep.exists_residual_matrix_bound
      (householderConstructApplyBound_nonneg fp (m + 1) hvalid)
  refine ⟨E, hNext, hE, ?_, ?_⟩
  · simpa [P] using householder_panel_exact_topLeft A hx
  · simpa [P] using householder_panel_exact_firstColumnTailZero A hx

/-- Stored first-column Householder panel step.

    The rounded panel application may contain rounded values below the diagonal
    in the completed first column.  The QR `R` algorithm stores those entries as
    structural zeros.  Because the corresponding exact Householder application
    has zero first-column tail, this only removes part of the residual and
    preserves the same normwise residual bound. -/
theorem fl_householder_first_column_panel_stored_residual_and_shape
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    let Ahat : Fin (m + 1) → Fin (p + 1) → ℝ :=
      fl_householderApplyMatrixRect fp (m + 1) (p + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 A
    let Rstep : Fin (m + 1) → Fin (p + 1) → ℝ :=
      panelFromTopAndTrailing (panelTopLeft Ahat) (panelTopRowTail Ahat)
        (trailingPanel Ahat)
    ∃ E : Fin (m + 1) → Fin (p + 1) → ℝ,
      (∀ i j,
        Rstep i j =
          matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) ∧
      frobNorm E ≤ householderConstructApplyBound fp (m + 1) * frobNorm A ∧
      panelFirstColumnTailZero Rstep := by
  intro P Ahat Rstep
  obtain ⟨Efull, hrep, hEfull, _htop, hzero⟩ :=
    fl_householder_first_column_panel_step_residual_and_shape fp A hx hvalid
  let Estore : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelFromTopAndTrailing (panelTopLeft Efull) (panelTopRowTail Efull)
      (trailingPanel Efull)
  refine ⟨Estore, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simpa [Rstep, Ahat, P, Estore, panelTopLeft] using hrep 0 0
      · intro j
        simpa [Rstep, Ahat, P, Estore, panelTopRowTail] using hrep 0 j.succ
    · intro i
      refine Fin.cases ?_ ?_ j
      · have hPzero : matMulRect (m + 1) (m + 1) (p + 1) P A i.succ 0 = 0 := by
          simpa [P, panelFirstColumnTailZero, panelFirstColumnTail] using hzero i
        simp [Rstep, Estore, hPzero]
      · intro j
        simpa [Rstep, Ahat, P, Estore, trailingPanel] using hrep i.succ j.succ
  · exact le_trans (frobNorm_panelFromTopAndTrailing_extract_le Efull) hEfull
  · simp [Rstep]

/-- Residual form of the concrete shrinking Householder QR panel step.

    The full first-column panel step already has a residual matrix bound.
    Restricting that residual to the trailing block gives a residual
    representation for `fl_householderTrailingPanelStep`.  This is the
    one-step bridge needed before an induction over shrinking QR panels. -/
theorem fl_householderTrailingPanelStep_residual
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    ∃ E : Fin m → Fin p → ℝ,
      (∀ i j, fl_householderTrailingPanelStep fp A i j =
        trailingPanel (matMulRect (m + 1) (m + 1) (p + 1) P A) i j +
          E i j) ∧
      frobNorm E ≤
        householderConstructApplyBound fp (m + 1) * frobNorm A := by
  intro P
  have hstep :
      ColumnwiseHouseholderStepErrorRect (m + 1) (p + 1) P A
        (fl_householderApplyMatrixRect fp (m + 1) (p + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 A)
        (householderConstructApplyBound fp (m + 1)) := by
    simpa [P] using
      fl_householder_first_column_panel_step_error fp
        (Nat.succ_pos m) (Nat.succ_pos p) A hx hvalid
  obtain ⟨Efull, hNext, hEfull⟩ :=
    hstep.exists_residual_matrix_bound
      (householderConstructApplyBound_nonneg fp (m + 1) hvalid)
  refine ⟨trailingPanel Efull, ?_, ?_⟩
  · intro i j
    have h := hNext i.succ j.succ
    simpa [fl_householderTrailingPanelStep, trailingPanel, P] using h
  · exact le_trans (frobNorm_trailingPanel_le Efull) hEfull

/-- One nonempty active-panel state step, packaged with the residual bound for
    the next active panel and the exact shape facts for the full reflector
    application.

    This is the state-level version of
    `fl_householderTrailingPanelStep_residual` plus the exact first-column
    triangularization lemmas.  It is still a one-step result; the full QR loop
    requires induction over this theorem. -/
theorem householderPanelStateStep_nonempty_residual_and_shape
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    ∃ E : Fin m → Fin p → ℝ,
      (∀ i j,
        (householderPanelStateStep fp ⟨m + 1, p + 1, A⟩).panel i j =
          trailingPanel (matMulRect (m + 1) (m + 1) (p + 1) P A) i j +
            E i j) ∧
      frobNorm E ≤
        householderConstructApplyBound fp (m + 1) * frobNorm A ∧
      panelTopLeft (matMulRect (m + 1) (m + 1) (p + 1) P A) =
        -householderScale (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A) ∧
      panelFirstColumnTailZero
        (matMulRect (m + 1) (m + 1) (p + 1) P A) := by
  intro P
  obtain ⟨E, hErep, hEbound⟩ :=
    fl_householderTrailingPanelStep_residual fp A hx hvalid
  refine ⟨E, ?_, hEbound, ?_, ?_⟩
  · intro i j
    simpa [householderPanelStateStep, P] using hErep i j
  · simpa [P] using householder_panel_exact_topLeft A hx
  · simpa [P] using householder_panel_exact_firstColumnTailZero A hx

/-- State-level one-step bridge using the packaged readiness predicate. -/
theorem householderPanelStateStep_nonempty_residual_and_shape_of_ready
    (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hready : HouseholderPanelStepReady fp ⟨m + 1, p + 1, A⟩) :
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    ∃ E : Fin m → Fin p → ℝ,
      (∀ i j,
        (householderPanelStateStep fp ⟨m + 1, p + 1, A⟩).panel i j =
          trailingPanel (matMulRect (m + 1) (m + 1) (p + 1) P A) i j +
            E i j) ∧
      frobNorm E ≤
        householderConstructApplyBound fp (m + 1) * frobNorm A ∧
      panelTopLeft (matMulRect (m + 1) (m + 1) (p + 1) P A) =
        -householderScale (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A) ∧
      panelFirstColumnTailZero
        (matMulRect (m + 1) (m + 1) (p + 1) P A) := by
  have hready' :
      panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
      gammaValid fp (11 * (m + 1) + 23) := by
    simpa using hready
  exact householderPanelStateStep_nonempty_residual_and_shape fp A
    hready'.1 hready'.2

/-- Repeated rectangular panel sequence where each reflector is constructed
    from the current panel's first column.

    This is closer to a QR panel loop than
    `fl_householder_panel_sequence_backward_error`, but it still keeps a fixed
    panel shape.  The full QR loop must additionally shrink the trailing panel
    after each step and prove triangularization. -/
theorem fl_householder_first_column_panel_sequence_backward_error
    (fp : FPModel) {m p r : ℕ}
    (hm0 : 0 < m) (hp0 : 0 < p)
    (Aseq : ℕ → Fin m → Fin p → ℝ)
    (hx : ∀ k : ℕ, k < r → panelFirstColumn hp0 (Aseq k) ≠ 0)
    (hvalid : gammaValid fp (11 * m + 23))
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_householderApplyMatrixRect fp m p
          (fl_householderNormalizedVector fp hm0 (panelFirstColumn hp0 (Aseq k)))
          1 (Aseq k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin p → ℝ),
      IsOrthogonal m Q ∧
      (∀ (i : Fin m) (j : Fin p), Aseq r i j =
        matMulRect m m p (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (householderConstructApplyBound fp m) r *
          frobNorm (Aseq 0) := by
  let xseq : ℕ → Fin m → ℝ := fun k => panelFirstColumn hp0 (Aseq k)
  exact fl_householder_panel_sequence_backward_error fp hm0 Aseq xseq hx hvalid hAstep

-- ============================================================
-- §18.3  Theorem 18.4: Householder QR backward error
-- ============================================================

/-- Upper-triangular shape predicate for square QR `R` factors. -/
def IsUpperTriangular (n : ℕ) (R : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, j.val < i.val → R i j = 0

/-- Reconstructing a square panel with a zero first-column tail preserves
    upper-triangularity exactly when the trailing panel is upper triangular. -/
theorem IsUpperTriangular_panelFromTopAndTrailing {n : ℕ}
    (a00 : ℝ) (top : Fin n → ℝ) (tail : Fin n → Fin n → ℝ)
    (htail : IsUpperTriangular n tail) :
    IsUpperTriangular (n + 1) (panelFromTopAndTrailing a00 top tail) := by
  intro i j hji
  revert hji
  refine Fin.cases ?_ ?_ i
  · intro hji
    exact False.elim ((Nat.not_lt_zero j.val) hji)
  · intro i hji
    revert hji
    refine Fin.cases ?_ ?_ j
    · intro _hji
      simp
    · intro j hji
      have hjlt : j.val < i.val := Nat.succ_lt_succ_iff.mp hji
      simpa [IsUpperTriangular] using htail i j hjlt

/-- The recursive rounded Householder QR `R` algorithm returns an
    upper-triangular matrix by construction. -/
theorem fl_householderQR_R_upper (fp : FPModel) :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      IsUpperTriangular n (fl_householderQR_R fp n A) := by
  intro n
  induction n with
  | zero =>
      intro A i
      exact Fin.elim0 i
  | succ n ih =>
      intro A
      let Astep : Fin (n + 1) → Fin (n + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (n + 1) (n + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos n)
            (panelFirstColumn (Nat.succ_pos n) A)) 1 A
      change IsUpperTriangular (n + 1)
        (panelFromTopAndTrailing (panelTopLeft Astep) (panelTopRowTail Astep)
          (fl_householderQRPanel_R fp n n (trailingPanel Astep)))
      exact IsUpperTriangular_panelFromTopAndTrailing
        (panelTopLeft Astep) (panelTopRowTail Astep)
        (fl_householderQRPanel_R fp n n (trailingPanel Astep))
        (by simpa [fl_householderQR_R] using ih (trailingPanel Astep))

/-- The zero-aware recursive rounded Householder QR `R` algorithm returns an
    upper-triangular matrix by construction. -/
theorem fl_householderQR_R_safe_upper (fp : FPModel) :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      IsUpperTriangular n (fl_householderQR_R_safe fp n A) := by
  intro n
  induction n with
  | zero =>
      intro A i
      exact Fin.elim0 i
  | succ n ih =>
      intro A
      by_cases hcol : panelFirstColumn (Nat.succ_pos n) A = 0
      · have htail :
            IsUpperTriangular n
              (fl_householderQRPanel_R_safe fp n n (trailingPanel A)) := by
          simpa [fl_householderQR_R_safe] using ih (trailingPanel A)
        have hmain :=
          IsUpperTriangular_panelFromTopAndTrailing
            (panelTopLeft A) (panelTopRowTail A)
            (fl_householderQRPanel_R_safe fp n n (trailingPanel A)) htail
        simpa [fl_householderQR_R_safe, fl_householderQRPanel_R_safe, hcol]
          using hmain
      · let Astep : Fin (n + 1) → Fin (n + 1) → ℝ :=
          fl_householderApplyMatrixRect fp (n + 1) (n + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos n)
              (panelFirstColumn (Nat.succ_pos n) A)) 1 A
        have htail :
            IsUpperTriangular n
              (fl_householderQRPanel_R_safe fp n n (trailingPanel Astep)) := by
          simpa [fl_householderQR_R_safe] using ih (trailingPanel Astep)
        have hmain :=
          IsUpperTriangular_panelFromTopAndTrailing
            (panelTopLeft Astep) (panelTopRowTail Astep)
            (fl_householderQRPanel_R_safe fp n n (trailingPanel Astep)) htail
        simpa [fl_householderQR_R_safe, fl_householderQRPanel_R_safe, hcol, Astep]
          using hmain

/-- Recursive coefficient for the implementation-backed nonzero-panel
    Householder QR panel backward-error theorem.

    For a nonempty panel, the first concrete Householder panel step contributes
    `c = householderConstructApplyBound fp (m+1)`.  The recursive tail bound is
    then applied to a trailing panel whose norm is bounded by `(1+c)` times the
    current panel norm. -/
noncomputable def householderQRPanelBackwardCoeff (fp : FPModel) :
    ℕ → ℕ → ℝ
  | 0, _ => 0
  | Nat.succ _, 0 => 0
  | m + 1, p + 1 =>
      let c := householderConstructApplyBound fp (m + 1)
      c + householderQRPanelBackwardCoeff fp m p * (1 + c)

/-- Square specialization of the recursive QR panel backward-error
    coefficient. -/
noncomputable def householderQRBackwardCoeff (fp : FPModel) (n : ℕ) : ℝ :=
  householderQRPanelBackwardCoeff fp n n

/-- Branch-dependent backward-error coefficient for the zero-aware Householder
    QR panel algorithm.

    A zero active first column contributes no rounded reflector-application
    error and recurses directly on the exact trailing panel.  A nonzero active
    column uses the same concrete Householder construction/application bound as
    `householderQRPanelBackwardCoeff`. -/
noncomputable def householderQRPanelBackwardCoeffSafe (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → ℝ
  | 0, _, _ => 0
  | Nat.succ _, 0, _ => 0
  | m + 1, p + 1, A =>
      if panelFirstColumn (Nat.succ_pos p) A = 0 then
        householderQRPanelBackwardCoeffSafe fp m p (trailingPanel A)
      else
        let c := householderConstructApplyBound fp (m + 1)
        c + householderQRPanelBackwardCoeffSafe fp m p
              (fl_householderTrailingPanelStep fp A) * (1 + c)

/-- Square specialization of the zero-aware Householder QR backward-error
    coefficient. -/
noncomputable def householderQRBackwardCoeffSafe (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  householderQRPanelBackwardCoeffSafe fp n n A

/-- The zero-aware QR panel coefficient is nonnegative whenever the safe run
    has the gamma hypotheses needed for every nonzero rounded reflector
    branch. -/
theorem householderQRPanelBackwardCoeffSafe_nonneg (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelSafeReady fp m p A →
      0 ≤ householderQRPanelBackwardCoeffSafe fp m p A := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      simp [householderQRPanelBackwardCoeffSafe]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          simp [householderQRPanelBackwardCoeffSafe]
      | succ p =>
          intro A hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htail :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            simpa [householderQRPanelBackwardCoeffSafe, hcol] using
              ih p (trailingPanel A) htail
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            let c := householderConstructApplyBound fp (m + 1)
            let α := householderQRPanelBackwardCoeffSafe fp m p
              (fl_householderTrailingPanelStep fp A)
            have hc : 0 ≤ c := by
              simpa [c] using
                householderConstructApplyBound_nonneg fp (m + 1) hready'.1
            have hα : 0 ≤ α := by
              simpa [α] using
                ih p (fl_householderTrailingPanelStep fp A) hready'.2
            simp [householderQRPanelBackwardCoeffSafe, hcol]
            nlinarith

/-- The recursive QR panel backward-error coefficient is nonnegative whenever
    the concrete QR panel run is ready. -/
theorem householderQRPanelBackwardCoeff_nonneg (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelReady fp m p A →
      0 ≤ householderQRPanelBackwardCoeff fp m p := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      simp [householderQRPanelBackwardCoeff]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          simp [householderQRPanelBackwardCoeff]
      | succ p =>
          intro A hready
          have hxvalid :
              panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
              gammaValid fp (11 * (m + 1) + 23) ∧
              HouseholderQRPanelReady fp m p (fl_householderTrailingPanelStep fp A) := by
            simpa using hready
          let c := householderConstructApplyBound fp (m + 1)
          let α := householderQRPanelBackwardCoeff fp m p
          have hc : 0 ≤ c := by
            simpa [c] using
              householderConstructApplyBound_nonneg fp (m + 1) hxvalid.2.1
          have hα : 0 ≤ α := by
            simpa [α] using ih p (fl_householderTrailingPanelStep fp A) hxvalid.2.2
          simp [householderQRPanelBackwardCoeff]
          nlinarith

/-- **Theorem 18.4**: Householder QR factorization backward error (normwise).

    The computed R̂ from Householder QR satisfies A + ΔA = Q·R̂
    where Q is orthogonal and ‖ΔA‖_F ≤ c_bound.

    This is the final QR backward-error contract.  Some wrapper theorems below
    derive it from a supplied `OrthogonalSequenceBackwardError`, while
    `fl_householderQR_R_backward_error` and
    `fl_householderQR_R_safe_backward_error` prove it from concrete rounded
    Householder QR `R` algorithms. -/
structure HouseholderQRBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (c_bound : ℝ) : Prop where
  /-- There exists an orthogonal Q such that A + ΔA = Q·R̂ with bounded ΔA. -/
  result : ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
    IsOrthogonal n Q ∧
    (∀ i j, matMul n Q R_hat i j = A i j + ΔA i j) ∧
    frobNorm ΔA ≤ c_bound

/-- Rectangular panel form of the QR backward-error target.

    This is the natural induction target for the recursive implementation:
    the active panel may be rectangular even when the original problem is
    square.  It records the equivalent representation
    `R_hat = Qᵀ(A + ΔA)`; the square wrapper later converts this to
    `A + ΔA = Q R_hat`. -/
structure HouseholderQRPanelBackwardError (m p : ℕ)
    (A R_hat : Fin m → Fin p → ℝ) (c_bound : ℝ) : Prop where
  /-- There exist an orthogonal `Q` and bounded panel perturbation `ΔA`. -/
  result : ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin p → ℝ),
    IsOrthogonal m Q ∧
    (∀ i j, R_hat i j =
      matMulRect m m p (matTranspose Q)
        (fun a b => A a b + ΔA a b) i j) ∧
    frobNorm ΔA ≤ c_bound

/-- Rectangular panel QR backward-error target with the orthogonal factor made
    explicit.

    This strengthens `HouseholderQRPanelBackwardError` by fixing the `Q`
    witness.  It is useful for public APIs that expose the exact orthogonal
    witness associated with a concrete rounded `R` algorithm. -/
structure HouseholderQRPanelExplicitBackwardError (m p : ℕ)
    (A : Fin m → Fin p → ℝ) (Q : Fin m → Fin m → ℝ)
    (R_hat : Fin m → Fin p → ℝ) (c_bound : ℝ) : Prop where
  /-- The supplied `Q` is orthogonal. -/
  orth : IsOrthogonal m Q
  /-- The supplied `Q` realizes the panel perturbation equation. -/
  result : ∃ ΔA : Fin m → Fin p → ℝ,
    (∀ i j, R_hat i j =
      matMulRect m m p (matTranspose Q)
        (fun a b => A a b + ΔA a b) i j) ∧
    frobNorm ΔA ≤ c_bound

/-- Forget the explicit `Q` witness and recover the existing existential panel
    contract. -/
theorem HouseholderQRPanelExplicitBackwardError.to_backward_error {m p : ℕ}
    {A R_hat : Fin m → Fin p → ℝ} {Q : Fin m → Fin m → ℝ} {c_bound : ℝ}
    (h : HouseholderQRPanelExplicitBackwardError m p A Q R_hat c_bound) :
    HouseholderQRPanelBackwardError m p A R_hat c_bound := by
  obtain ⟨ΔA, hrep, hΔA⟩ := h.result
  exact ⟨⟨Q, ΔA, h.orth, hrep, hΔA⟩⟩

/-- Square Householder QR backward-error contract with the orthogonal factor
    made explicit.

    This is the public contract for APIs that expose a concrete exact `Q`
    witness together with a rounded `R` output. -/
structure HouseholderQRExplicitBackwardError
    (n : ℕ) (A : Fin n → Fin n → ℝ)
    (Q R_hat : Fin n → Fin n → ℝ) (c_bound : ℝ) : Prop where
  /-- The supplied `Q` is orthogonal. -/
  orth : IsOrthogonal n Q
  /-- The supplied `R_hat` has the expected upper-triangular shape. -/
  upper : IsUpperTriangular n R_hat
  /-- There is a bounded backward perturbation for this supplied `Q`. -/
  result : ∃ ΔA : Fin n → Fin n → ℝ,
    (∀ i j, matMul n Q R_hat i j = A i j + ΔA i j) ∧
    frobNorm ΔA ≤ c_bound

/-- Empty-row panels satisfy the rectangular QR backward-error target
    trivially. -/
theorem householder_qr_panel_backward_zero_rows (p : ℕ)
    (A : Fin 0 → Fin p → ℝ) :
    HouseholderQRPanelBackwardError 0 p A A 0 := by
  let Z : Fin 0 → Fin p → ℝ := fun _ _ => 0
  refine ⟨⟨idMatrix 0, Z, idMatrix_orthogonal 0, ?_, ?_⟩⟩
  · intro i
    exact Fin.elim0 i
  · have hZ : frobNorm Z = 0 := by
      rw [frobNorm_eq_zero_iff]
      intro i
      exact Fin.elim0 i
    simp [Z, hZ]

/-- Empty-column panels satisfy the rectangular QR backward-error target
    trivially. -/
theorem householder_qr_panel_backward_zero_cols (m : ℕ)
    (A : Fin (m + 1) → Fin 0 → ℝ) :
    HouseholderQRPanelBackwardError (m + 1) 0 A A 0 := by
  let Z : Fin (m + 1) → Fin 0 → ℝ := fun _ _ => 0
  refine ⟨⟨idMatrix (m + 1), Z, idMatrix_orthogonal (m + 1), ?_, ?_⟩⟩
  · intro i j
    exact Fin.elim0 j
  · have hZ : frobNorm Z = 0 := by
      rw [frobNorm_eq_zero_iff]
      intro i j
      exact Fin.elim0 j
    simp [Z, hZ]

/-- Algebraic skip step for a degenerate active Householder QR panel.

    If the current first column is already zero, no reflector is needed for the
    active column.  A backward-error proof for the trailing panel can be lifted
    to the full panel by embedding the trailing orthogonal factor with a
    leading identity and by embedding the trailing perturbation.  This theorem
    is exact QR bookkeeping; it introduces no new floating-point assumption. -/
theorem householder_qr_panel_backward_skip_zero_column {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Rtail : Fin m → Fin p → ℝ)
    (α : ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0)
    (hTail :
      HouseholderQRPanelBackwardError m p (trailingPanel A) Rtail
        (α * frobNorm (trailingPanel A)))
    (hα : 0 ≤ α) :
    HouseholderQRPanelBackwardError (m + 1) (p + 1) A
      (panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A) Rtail)
      (α * frobNorm A) := by
  obtain ⟨Qt, ΔT, hQt, hTailRep, hΔT⟩ := hTail.result
  let ΔA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ :=
    embedTrailingOne Qt
  refine ⟨⟨Q, ΔA, ?_, ?_, ?_⟩⟩
  · exact embedTrailingOne_orthogonal Qt hQt
  · have hLift :=
      panelFromTopAndTrailing_lift_trailing_rep Qt
        (panelTopLeft A) (panelTopRowTail A)
        (trailingPanel A) Rtail ΔT hTailRep
    have hAblocks :
        panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
          (trailingPanel A) = A :=
      panelFromTopAndTrailing_of_panelFirstColumn_eq_zero A hcol
    have hInside :
        (fun i j =>
          panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
              (trailingPanel A) i j +
            panelTrailingPerturbation ΔT i j) =
          fun i j => A i j + ΔA i j := by
      ext i j
      rw [hAblocks]
    have hQtrans :
        matTranspose Q = embedTrailingOne (matTranspose Qt) := by
      simp [Q, matTranspose_embedTrailingOne]
    intro i j
    calc
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A) Rtail i j
          =
        matMulRect (m + 1) (m + 1) (p + 1)
          (embedTrailingOne (matTranspose Qt))
          (fun i j =>
            panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
                (trailingPanel A) i j +
              panelTrailingPerturbation ΔT i j) i j := by
            exact congrFun (congrFun hLift i) j
      _ =
        matMulRect (m + 1) (m + 1) (p + 1) (matTranspose Q)
          (fun i j => A i j + ΔA i j) i j := by
            rw [hQtrans, hInside]
  · have hΔnorm : frobNorm ΔA = frobNorm ΔT := by
      exact frobNorm_panelTrailingPerturbation ΔT
    calc
      frobNorm ΔA = frobNorm ΔT := hΔnorm
      _ ≤ α * frobNorm (trailingPanel A) := hΔT
      _ ≤ α * frobNorm A :=
          mul_le_mul_of_nonneg_left (frobNorm_trailingPanel_le A) hα

/-- Explicit-`Q` version of
    `householder_qr_panel_backward_skip_zero_column`. -/
theorem householder_qr_panel_explicit_backward_skip_zero_column {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Qt : Fin m → Fin m → ℝ)
    (Rtail : Fin m → Fin p → ℝ)
    (α : ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0)
    (hTail :
      HouseholderQRPanelExplicitBackwardError m p (trailingPanel A) Qt Rtail
        (α * frobNorm (trailingPanel A)))
    (hα : 0 ≤ α) :
    HouseholderQRPanelExplicitBackwardError (m + 1) (p + 1) A
      (embedTrailingOne Qt)
      (panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A) Rtail)
      (α * frobNorm A) := by
  obtain ⟨ΔT, hTailRep, hΔT⟩ := hTail.result
  let ΔA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  refine ⟨embedTrailingOne_orthogonal Qt hTail.orth, ⟨ΔA, ?_, ?_⟩⟩
  · have hLift :=
      panelFromTopAndTrailing_lift_trailing_rep Qt
        (panelTopLeft A) (panelTopRowTail A)
        (trailingPanel A) Rtail ΔT hTailRep
    have hAblocks :
        panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
          (trailingPanel A) = A :=
      panelFromTopAndTrailing_of_panelFirstColumn_eq_zero A hcol
    have hInside :
        (fun i j =>
          panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
              (trailingPanel A) i j +
            panelTrailingPerturbation ΔT i j) =
          fun i j => A i j + ΔA i j := by
      ext i j
      rw [hAblocks]
    intro i j
    calc
      panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A) Rtail i j
          =
        matMulRect (m + 1) (m + 1) (p + 1)
          (embedTrailingOne (matTranspose Qt))
          (fun i j =>
            panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
                (trailingPanel A) i j +
              panelTrailingPerturbation ΔT i j) i j := by
            exact congrFun (congrFun hLift i) j
      _ =
        matMulRect (m + 1) (m + 1) (p + 1)
          (matTranspose (embedTrailingOne Qt))
          (fun i j => A i j + ΔA i j) i j := by
            rw [matTranspose_embedTrailingOne, hInside]
  · have hΔnorm : frobNorm ΔA = frobNorm ΔT := by
      exact frobNorm_panelTrailingPerturbation ΔT
    calc
      frobNorm ΔA = frobNorm ΔT := hΔnorm
      _ ≤ α * frobNorm (trailingPanel A) := hΔT
      _ ≤ α * frobNorm A :=
          mul_le_mul_of_nonneg_left (frobNorm_trailingPanel_le A) hα

/-- Algebraic cons step for the recursive rectangular QR panel backward-error
    proof.

    If the current stored panel `S` is one residual away from applying an
    orthogonal first-step reflector `P` to `A`, and the trailing panel of `S`
    already has a QR panel backward-error proof, then replacing the trailing
    panel by that recursive `Rtail` gives a full-panel backward-error proof. -/
theorem householder_qr_panel_backward_cons {m p : ℕ}
    (A S : Fin (m + 1) → Fin (p + 1) → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (E : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Rtail : Fin m → Fin p → ℝ)
    (c α : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hSrep : ∀ i j,
      S i j = matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j)
    (hE : frobNorm E ≤ c * frobNorm A)
    (hSzero : panelFirstColumnTailZero S)
    (hTail :
      HouseholderQRPanelBackwardError m p (trailingPanel S) Rtail
        (α * frobNorm (trailingPanel S)))
    (hα : 0 ≤ α) :
    HouseholderQRPanelBackwardError (m + 1) (p + 1) A
      (panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S) Rtail)
      ((c + α * (1 + c)) * frobNorm A) := by
  obtain ⟨Qt, ΔT, hQt, hTailRep, hΔT⟩ := hTail.result
  let Δtail : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  let Eta : Fin (m + 1) → Fin (p + 1) → ℝ :=
    fun i j => E i j + Δtail i j
  let ΔA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta
  let M : Fin (m + 1) → Fin (m + 1) → ℝ :=
    matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ := matTranspose M
  refine ⟨⟨Q, ΔA, ?_, ?_, ?_⟩⟩
  · have hEmb : IsOrthogonal (m + 1) (embedTrailingOne (matTranspose Qt)) :=
      embedTrailingOne_orthogonal (matTranspose Qt) hQt.transpose
    have hM : IsOrthogonal (m + 1) M := hEmb.mul hP
    exact hM.transpose
  · have hLift :=
      panelFromTopAndTrailing_lift_trailing_rep Qt
        (panelTopLeft S) (panelTopRowTail S)
        (trailingPanel S) Rtail ΔT hTailRep
    have hSblocks :
        panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
          (trailingPanel S) = S :=
      panelFromTopAndTrailing_of_firstColumnTailZero S hSzero
    have hInside :
        (fun i j =>
          panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
              (trailingPanel S) i j +
            panelTrailingPerturbation ΔT i j) =
          fun i j => S i j + Δtail i j := by
      ext i j
      rw [hSblocks]
    have hPA_Eta :
        (fun i j => S i j + Δtail i j) =
          matMulRect (m + 1) (m + 1) (p + 1) P
            (fun a b => A a b + ΔA a b) := by
      ext i j
      have hPPt :
          matMul (m + 1) P (matTranspose P) = idMatrix (m + 1) := by
        ext a b
        exact hP.right_inv a b
      have hPΔ :
          matMulRect (m + 1) (m + 1) (p + 1) P ΔA = Eta := by
        show matMulRect (m + 1) (m + 1) (p + 1) P
            (matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta) = Eta
        rw [← matMulRect_assoc_square_left, hPPt, matMulRect_id_left]
      calc
        S i j + Δtail i j
            = (matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) +
                Δtail i j := by rw [hSrep i j]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j +
              Eta i j := by
            simp [Eta]
            ring
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j +
              matMulRect (m + 1) (m + 1) (p + 1) P ΔA i j := by
            rw [hPΔ]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P
              (fun a b => A a b + ΔA a b) i j := by
            rw [← congr_fun
              (congr_fun
                (matMulRect_add_right (m + 1) (m + 1) (p + 1) P A ΔA) i) j]
    intro i j
    have hLift' :
        panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S) Rtail =
          matMulRect (m + 1) (m + 1) (p + 1)
            (embedTrailingOne (matTranspose Qt))
            (fun i j => S i j + Δtail i j) := by
      rw [hLift]
      congr
    rw [hLift']
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt))
        (fun i j => S i j + Δtail i j) i j =
      matMulRect (m + 1) (m + 1) (p + 1) (matTranspose Q)
        (fun a b => A a b + ΔA a b) i j
    rw [hPA_Eta]
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt))
        (matMulRect (m + 1) (m + 1) (p + 1) P
          (fun a b => A a b + ΔA a b)) i j =
      matMulRect (m + 1) (m + 1) (p + 1) (matTranspose Q)
        (fun a b => A a b + ΔA a b) i j
    rw [← matMulRect_assoc_square_left]
    simp [Q, M, matTranspose_involutive]
  · have hΔnorm :
        frobNorm ΔA = frobNorm Eta := by
      show frobNorm
          (matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta) =
        frobNorm Eta
      exact frobNorm_orthogonal_left_rect (matTranspose P) Eta hP.transpose
    have hΔtailnorm : frobNorm Δtail = frobNorm ΔT := by
      exact frobNorm_panelTrailingPerturbation ΔT
    have hEta :
        frobNorm Eta ≤ frobNorm E + frobNorm Δtail := by
      show frobNorm (fun i j => E i j + Δtail i j) ≤
        frobNorm E + frobNorm Δtail
      exact norm_add_le
        (Matrix.of E : Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
        (Matrix.of Δtail : Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
    have hSnorm :
        frobNorm S ≤ (1 + c) * frobNorm A := by
      have hSfun :
          S = fun i j =>
            matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j :=
        funext fun i => funext fun j => hSrep i j
      calc
        frobNorm S
            = frobNorm
                (fun i j =>
                  matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) := by
              rw [hSfun]
        _ ≤ frobNorm (matMulRect (m + 1) (m + 1) (p + 1) P A) +
              frobNorm E := by
            exact norm_add_le
              (Matrix.of
                (matMulRect (m + 1) (m + 1) (p + 1) P A) :
                  Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
              (Matrix.of E : Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
        _ = frobNorm A + frobNorm E := by
            rw [frobNorm_orthogonal_left_rect P A hP]
        _ ≤ frobNorm A + c * frobNorm A := by
            exact add_le_add (le_refl (frobNorm A)) hE
        _ = (1 + c) * frobNorm A := by ring
    have hTnorm :
        frobNorm (trailingPanel S) ≤ (1 + c) * frobNorm A :=
      le_trans (frobNorm_trailingPanel_le S) hSnorm
    have hΔTbound :
        frobNorm ΔT ≤ α * ((1 + c) * frobNorm A) :=
      le_trans hΔT (mul_le_mul_of_nonneg_left hTnorm hα)
    calc
      frobNorm ΔA
          = frobNorm Eta := hΔnorm
      _ ≤ frobNorm E + frobNorm Δtail := hEta
      _ = frobNorm E + frobNorm ΔT := by rw [hΔtailnorm]
      _ ≤ c * frobNorm A + α * ((1 + c) * frobNorm A) := by
          exact add_le_add hE hΔTbound
      _ = (c + α * (1 + c)) * frobNorm A := by ring

/-- Explicit-`Q` version of `householder_qr_panel_backward_cons`. -/
theorem householder_qr_panel_explicit_backward_cons {m p : ℕ}
    (A S : Fin (m + 1) → Fin (p + 1) → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (E : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Qt : Fin m → Fin m → ℝ)
    (Rtail : Fin m → Fin p → ℝ)
    (c α : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hSrep : ∀ i j,
      S i j = matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j)
    (hE : frobNorm E ≤ c * frobNorm A)
    (hSzero : panelFirstColumnTailZero S)
    (hTail :
      HouseholderQRPanelExplicitBackwardError m p (trailingPanel S) Qt Rtail
        (α * frobNorm (trailingPanel S)))
    (hα : 0 ≤ α) :
    HouseholderQRPanelExplicitBackwardError (m + 1) (p + 1) A
      (matTranspose (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P))
      (panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S) Rtail)
      ((c + α * (1 + c)) * frobNorm A) := by
  obtain ⟨ΔT, hTailRep, hΔT⟩ := hTail.result
  let Δtail : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  let Eta : Fin (m + 1) → Fin (p + 1) → ℝ :=
    fun i j => E i j + Δtail i j
  let ΔA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta
  refine ⟨?_, ⟨ΔA, ?_, ?_⟩⟩
  · have hEmb : IsOrthogonal (m + 1) (embedTrailingOne (matTranspose Qt)) :=
      embedTrailingOne_orthogonal (matTranspose Qt) hTail.orth.transpose
    have hM :
        IsOrthogonal (m + 1)
          (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P) :=
      hEmb.mul hP
    exact hM.transpose
  · have hLift :=
      panelFromTopAndTrailing_lift_trailing_rep Qt
        (panelTopLeft S) (panelTopRowTail S)
        (trailingPanel S) Rtail ΔT hTailRep
    have hSblocks :
        panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
          (trailingPanel S) = S :=
      panelFromTopAndTrailing_of_firstColumnTailZero S hSzero
    have hInside :
        (fun i j =>
          panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
              (trailingPanel S) i j +
            panelTrailingPerturbation ΔT i j) =
          fun i j => S i j + Δtail i j := by
      ext i j
      rw [hSblocks]
    have hPA_Eta :
        (fun i j => S i j + Δtail i j) =
          matMulRect (m + 1) (m + 1) (p + 1) P
            (fun a b => A a b + ΔA a b) := by
      ext i j
      have hPPt :
          matMul (m + 1) P (matTranspose P) = idMatrix (m + 1) := by
        ext a b
        exact hP.right_inv a b
      have hPΔ :
          matMulRect (m + 1) (m + 1) (p + 1) P ΔA = Eta := by
        show matMulRect (m + 1) (m + 1) (p + 1) P
            (matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta) = Eta
        rw [← matMulRect_assoc_square_left, hPPt, matMulRect_id_left]
      calc
        S i j + Δtail i j
            = (matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) +
                Δtail i j := by rw [hSrep i j]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j +
              Eta i j := by
            simp [Eta]
            ring
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j +
              matMulRect (m + 1) (m + 1) (p + 1) P ΔA i j := by
            rw [hPΔ]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P
              (fun a b => A a b + ΔA a b) i j := by
            rw [← congr_fun
              (congr_fun
                (matMulRect_add_right (m + 1) (m + 1) (p + 1) P A ΔA) i) j]
    intro i j
    have hLift' :
        panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S) Rtail =
          matMulRect (m + 1) (m + 1) (p + 1)
            (embedTrailingOne (matTranspose Qt))
            (fun i j => S i j + Δtail i j) := by
      rw [hLift]
      congr
    rw [hLift']
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt))
        (fun i j => S i j + Δtail i j) i j =
      matMulRect (m + 1) (m + 1) (p + 1)
        (matTranspose
          (matTranspose
            (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P)))
        (fun a b => A a b + ΔA a b) i j
    rw [hPA_Eta]
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt))
        (matMulRect (m + 1) (m + 1) (p + 1) P
          (fun a b => A a b + ΔA a b)) i j =
      matMulRect (m + 1) (m + 1) (p + 1)
        (matTranspose
          (matTranspose
            (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P)))
        (fun a b => A a b + ΔA a b) i j
    rw [← matMulRect_assoc_square_left]
    simp [matTranspose_involutive]
  · have hΔnorm :
        frobNorm ΔA = frobNorm Eta := by
      show frobNorm
          (matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) Eta) =
        frobNorm Eta
      exact frobNorm_orthogonal_left_rect (matTranspose P) Eta hP.transpose
    have hΔtailnorm : frobNorm Δtail = frobNorm ΔT := by
      exact frobNorm_panelTrailingPerturbation ΔT
    have hEta :
        frobNorm Eta ≤ frobNorm E + frobNorm Δtail := by
      show frobNorm (fun i j => E i j + Δtail i j) ≤
        frobNorm E + frobNorm Δtail
      exact norm_add_le
        (Matrix.of E : Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
        (Matrix.of Δtail : Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
    have hSnorm :
        frobNorm S ≤ (1 + c) * frobNorm A := by
      have hSfun :
          S = fun i j =>
            matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j :=
        funext fun i => funext fun j => hSrep i j
      calc
        frobNorm S
            = frobNorm
                (fun i j =>
                  matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) := by
              rw [hSfun]
        _ ≤ frobNorm (matMulRect (m + 1) (m + 1) (p + 1) P A) +
              frobNorm E := by
            exact norm_add_le
              (Matrix.of
                (matMulRect (m + 1) (m + 1) (p + 1) P A) :
                  Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
              (Matrix.of E : Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)
        _ = frobNorm A + frobNorm E := by
            rw [frobNorm_orthogonal_left_rect P A hP]
        _ ≤ frobNorm A + c * frobNorm A := by
            exact add_le_add (le_refl (frobNorm A)) hE
        _ = (1 + c) * frobNorm A := by ring
    have hTnorm :
        frobNorm (trailingPanel S) ≤ (1 + c) * frobNorm A :=
      le_trans (frobNorm_trailingPanel_le S) hSnorm
    have hΔTbound :
        frobNorm ΔT ≤ α * ((1 + c) * frobNorm A) :=
      le_trans hΔT (mul_le_mul_of_nonneg_left hTnorm hα)
    calc
      frobNorm ΔA
          = frobNorm Eta := hΔnorm
      _ ≤ frobNorm E + frobNorm Δtail := hEta
      _ = frobNorm E + frobNorm ΔT := by rw [hΔtailnorm]
      _ ≤ c * frobNorm A + α * ((1 + c) * frobNorm A) := by
          exact add_le_add hE hΔTbound
      _ = (c + α * (1 + c)) * frobNorm A := by ring

/-- Implementation-backed recursive backward error theorem for the rounded
    Householder QR `R` panel algorithm.

    This is the main rectangular induction bridge for the concrete recursive
    loop `fl_householderQRPanel_R`.  The square wrapper
    `fl_householderQR_R_backward_error` converts it to the existing
    `HouseholderQRBackwardError` contract. -/
theorem fl_householderQRPanel_R_backward_error (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelReady fp m p A →
      HouseholderQRPanelBackwardError m p A
        (fl_householderQRPanel_R fp m p A)
        (householderQRPanelBackwardCoeff fp m p * frobNorm A) := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      simpa [householderQRPanelBackwardCoeff] using
        householder_qr_panel_backward_zero_rows p A
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          simpa [householderQRPanelBackwardCoeff] using
            householder_qr_panel_backward_zero_cols m A
      | succ p =>
          intro A hready
          have hready' :
              panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
              gammaValid fp (11 * (m + 1) + 23) ∧
              HouseholderQRPanelReady fp m p (fl_householderTrailingPanelStep fp A) := by
            simpa using hready
          let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
            householder (m + 1)
              (householderNormalizedVector (m + 1)
                (householderVector (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A))
                (householderBetaFromScale (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A))) 1
          let Ahat : Fin (m + 1) → Fin (p + 1) → ℝ :=
            fl_householderApplyMatrixRect fp (m + 1) (p + 1)
              (fl_householderNormalizedVector fp (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) A)) 1 A
          let S : Fin (m + 1) → Fin (p + 1) → ℝ :=
            panelFromTopAndTrailing (panelTopLeft Ahat) (panelTopRowTail Ahat)
              (trailingPanel Ahat)
          obtain ⟨E, hSrep, hE, hSzero⟩ :=
            fl_householder_first_column_panel_stored_residual_and_shape fp A
              hready'.1 hready'.2.1
          have hPorth : IsOrthogonal (m + 1) P := by
            have hstep :=
              fl_householder_first_column_panel_step_error fp
                (Nat.succ_pos m) (Nat.succ_pos p) A hready'.1 hready'.2.1
            simpa [P, householderConstructApplyBound] using hstep.orth
          have hStrailing :
              trailingPanel S = fl_householderTrailingPanelStep fp A := by
            simp [S, Ahat, fl_householderTrailingPanelStep]
          have hTailRaw :=
            ih p (fl_householderTrailingPanelStep fp A) hready'.2.2
          have hTail :
              HouseholderQRPanelBackwardError m p (trailingPanel S)
                (fl_householderQRPanel_R fp m p (fl_householderTrailingPanelStep fp A))
                (householderQRPanelBackwardCoeff fp m p *
                  frobNorm (trailingPanel S)) := by
            rw [hStrailing]
            exact hTailRaw
          have hα :
              0 ≤ householderQRPanelBackwardCoeff fp m p :=
            householderQRPanelBackwardCoeff_nonneg fp m p
              (fl_householderTrailingPanelStep fp A) hready'.2.2
          have hCons :=
            householder_qr_panel_backward_cons A S P E
              (fl_householderQRPanel_R fp m p (fl_householderTrailingPanelStep fp A))
              (householderConstructApplyBound fp (m + 1))
              (householderQRPanelBackwardCoeff fp m p)
              hPorth hSrep hE hSzero hTail hα
          simpa [fl_householderQRPanel_R, householderQRPanelBackwardCoeff,
            S, Ahat, P, fl_householderTrailingPanelStep] using hCons

/-- Implementation-backed recursive backward-error theorem for the
    zero-aware rounded Householder QR `R` panel algorithm.

    This theorem removes the nonzero-active-column assumption from
    `fl_householderQRPanel_R_backward_error`.  When the active first column is
    zero, the algorithm skips the reflector and lifts the recursive trailing
    proof exactly.  When the active first column is nonzero, it uses the
    implementation-backed Householder construction/application bridge. -/
theorem fl_householderQRPanel_R_safe_backward_error (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelSafeReady fp m p A →
      HouseholderQRPanelBackwardError m p A
        (fl_householderQRPanel_R_safe fp m p A)
        (householderQRPanelBackwardCoeffSafe fp m p A * frobNorm A) := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      simpa [householderQRPanelBackwardCoeffSafe] using
        householder_qr_panel_backward_zero_rows p A
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          simpa [householderQRPanelBackwardCoeffSafe] using
            householder_qr_panel_backward_zero_cols m A
      | succ p =>
          intro A hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailRaw :=
              ih p (trailingPanel A) htailReady
            have hα :
                0 ≤ householderQRPanelBackwardCoeffSafe fp m p
                  (trailingPanel A) :=
              householderQRPanelBackwardCoeffSafe_nonneg fp m p
                (trailingPanel A) htailReady
            have hSkip :=
              householder_qr_panel_backward_skip_zero_column A
                (fl_householderQRPanel_R_safe fp m p (trailingPanel A))
                (householderQRPanelBackwardCoeffSafe fp m p
                  (trailingPanel A))
                hcol hTailRaw hα
            simpa [fl_householderQRPanel_R_safe,
              householderQRPanelBackwardCoeffSafe, hcol] using hSkip
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
              householder (m + 1)
                (householderNormalizedVector (m + 1)
                  (householderVector (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))
                  (householderBetaFromScale (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))) 1
            let Ahat : Fin (m + 1) → Fin (p + 1) → ℝ :=
              fl_householderApplyMatrixRect fp (m + 1) (p + 1)
                (fl_householderNormalizedVector fp (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A)) 1 A
            let S : Fin (m + 1) → Fin (p + 1) → ℝ :=
              panelFromTopAndTrailing (panelTopLeft Ahat) (panelTopRowTail Ahat)
                (trailingPanel Ahat)
            obtain ⟨E, hSrep, hE, hSzero⟩ :=
              fl_householder_first_column_panel_stored_residual_and_shape fp A
                hcol hready'.1
            have hPorth : IsOrthogonal (m + 1) P := by
              have hstep :=
                fl_householder_first_column_panel_step_error fp
                  (Nat.succ_pos m) (Nat.succ_pos p) A hcol hready'.1
              simpa [P, householderConstructApplyBound] using hstep.orth
            have hStrailing :
                trailingPanel S = fl_householderTrailingPanelStep fp A := by
              simp [S, Ahat, fl_householderTrailingPanelStep]
            have hTailRaw :=
              ih p (fl_householderTrailingPanelStep fp A) hready'.2
            have hTail :
                HouseholderQRPanelBackwardError m p (trailingPanel S)
                  (fl_householderQRPanel_R_safe fp m p
                    (fl_householderTrailingPanelStep fp A))
                  (householderQRPanelBackwardCoeffSafe fp m p
                    (fl_householderTrailingPanelStep fp A) *
                    frobNorm (trailingPanel S)) := by
              rw [hStrailing]
              exact hTailRaw
            have hα :
                0 ≤ householderQRPanelBackwardCoeffSafe fp m p
                  (fl_householderTrailingPanelStep fp A) :=
              householderQRPanelBackwardCoeffSafe_nonneg fp m p
                (fl_householderTrailingPanelStep fp A) hready'.2
            have hCons :=
              householder_qr_panel_backward_cons A S P E
                (fl_householderQRPanel_R_safe fp m p
                  (fl_householderTrailingPanelStep fp A))
                (householderConstructApplyBound fp (m + 1))
                (householderQRPanelBackwardCoeffSafe fp m p
                  (fl_householderTrailingPanelStep fp A))
                hPorth hSrep hE hSzero hTail hα
            simpa [fl_householderQRPanel_R_safe,
              householderQRPanelBackwardCoeffSafe, hcol,
              S, Ahat, P, fl_householderTrailingPanelStep] using hCons

/-- Implementation-backed recursive backward-error theorem for the zero-aware
    rounded Householder QR `R` panel algorithm with the explicit exact `Q`
    witness fixed.

    This is the explicit-`Q` strengthening of
    `fl_householderQRPanel_R_safe_backward_error`: the perturbation equation is
    proved for `fl_householderQRPanel_Q_safe`, not for an unnamed existential
    orthogonal matrix. -/
theorem fl_householderQRPanel_R_safe_explicit_backward_error (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ),
      HouseholderQRPanelSafeReady fp m p A →
      HouseholderQRPanelExplicitBackwardError m p A
        (fl_householderQRPanel_Q_safe fp m p A)
        (fl_householderQRPanel_R_safe fp m p A)
        (householderQRPanelBackwardCoeffSafe fp m p A * frobNorm A) := by
  intro m
  induction m with
  | zero =>
      intro p A _hready
      let Z : Fin 0 → Fin p → ℝ := fun _ _ => 0
      refine ⟨?_, ⟨Z, ?_, ?_⟩⟩
      · simpa [fl_householderQRPanel_Q_safe] using idMatrix_orthogonal 0
      · intro i
        exact Fin.elim0 i
      · have hZ : frobNorm Z = 0 := by
          rw [frobNorm_eq_zero_iff]
          intro i
          exact Fin.elim0 i
        simp [Z, hZ, householderQRPanelBackwardCoeffSafe]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A _hready
          let Z : Fin (m + 1) → Fin 0 → ℝ := fun _ _ => 0
          refine ⟨?_, ⟨Z, ?_, ?_⟩⟩
          · simpa [fl_householderQRPanel_Q_safe] using idMatrix_orthogonal (m + 1)
          · intro i j
            exact Fin.elim0 j
          · have hZ : frobNorm Z = 0 := by
              rw [frobNorm_eq_zero_iff]
              intro i j
              exact Fin.elim0 j
            simp [Z, hZ, householderQRPanelBackwardCoeffSafe]
      | succ p =>
          intro A hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelSafeReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            have hTailRaw :=
              ih p (trailingPanel A) htailReady
            have hα :
                0 ≤ householderQRPanelBackwardCoeffSafe fp m p
                  (trailingPanel A) :=
              householderQRPanelBackwardCoeffSafe_nonneg fp m p
                (trailingPanel A) htailReady
            have hSkip :=
              householder_qr_panel_explicit_backward_skip_zero_column A
                (fl_householderQRPanel_Q_safe fp m p (trailingPanel A))
                (fl_householderQRPanel_R_safe fp m p (trailingPanel A))
                (householderQRPanelBackwardCoeffSafe fp m p
                  (trailingPanel A))
                hcol hTailRaw hα
            simpa [fl_householderQRPanel_R_safe, fl_householderQRPanel_Q_safe,
              householderQRPanelBackwardCoeffSafe, hcol] using hSkip
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelSafeReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelSafeReady, hcol] using hready
            let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
              householder (m + 1)
                (householderNormalizedVector (m + 1)
                  (householderVector (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))
                  (householderBetaFromScale (Nat.succ_pos m)
                    (panelFirstColumn (Nat.succ_pos p) A))) 1
            let Ahat : Fin (m + 1) → Fin (p + 1) → ℝ :=
              fl_householderApplyMatrixRect fp (m + 1) (p + 1)
                (fl_householderNormalizedVector fp (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A)) 1 A
            let S : Fin (m + 1) → Fin (p + 1) → ℝ :=
              panelFromTopAndTrailing (panelTopLeft Ahat) (panelTopRowTail Ahat)
                (trailingPanel Ahat)
            obtain ⟨E, hSrep, hE, hSzero⟩ :=
              fl_householder_first_column_panel_stored_residual_and_shape fp A
                hcol hready'.1
            have hPorth : IsOrthogonal (m + 1) P := by
              have hstep :=
                fl_householder_first_column_panel_step_error fp
                  (Nat.succ_pos m) (Nat.succ_pos p) A hcol hready'.1
              simpa [P, householderConstructApplyBound] using hstep.orth
            have hStrailing :
                trailingPanel S = fl_householderTrailingPanelStep fp A := by
              simp [S, Ahat, fl_householderTrailingPanelStep]
            have hTailRaw :=
              ih p (fl_householderTrailingPanelStep fp A) hready'.2
            have hTail :
                HouseholderQRPanelExplicitBackwardError m p (trailingPanel S)
                  (fl_householderQRPanel_Q_safe fp m p
                    (fl_householderTrailingPanelStep fp A))
                  (fl_householderQRPanel_R_safe fp m p
                    (fl_householderTrailingPanelStep fp A))
                  (householderQRPanelBackwardCoeffSafe fp m p
                    (fl_householderTrailingPanelStep fp A) *
                    frobNorm (trailingPanel S)) := by
              rw [hStrailing]
              exact hTailRaw
            have hα :
                0 ≤ householderQRPanelBackwardCoeffSafe fp m p
                  (fl_householderTrailingPanelStep fp A) :=
              householderQRPanelBackwardCoeffSafe_nonneg fp m p
                (fl_householderTrailingPanelStep fp A) hready'.2
            have hCons :=
              householder_qr_panel_explicit_backward_cons A S P E
                (fl_householderQRPanel_Q_safe fp m p
                  (fl_householderTrailingPanelStep fp A))
                (fl_householderQRPanel_R_safe fp m p
                  (fl_householderTrailingPanelStep fp A))
                (householderConstructApplyBound fp (m + 1))
                (householderQRPanelBackwardCoeffSafe fp m p
                  (fl_householderTrailingPanelStep fp A))
                hPorth hSrep hE hSzero hTail hα
            simpa [fl_householderQRPanel_R_safe, fl_householderQRPanel_Q_safe,
              householderQRPanelBackwardCoeffSafe, hcol,
              S, Ahat, P, fl_householderTrailingPanelStep] using hCons

/-- Convert the square rectangular-panel QR representation
    `R = Qᵀ(A + ΔA)` to the existing square QR backward-error contract
    `Q R = A + ΔA`. -/
theorem householder_qr_panel_backward_to_square {n : ℕ}
    (A R_hat : Fin n → Fin n → ℝ) (c_bound : ℝ)
    (hPanel : HouseholderQRPanelBackwardError n n A R_hat c_bound) :
    HouseholderQRBackwardError n A R_hat c_bound := by
  obtain ⟨Q, ΔA, hQ, hR, hΔ⟩ := hPanel.result
  refine ⟨⟨Q, ΔA, hQ, ?_, hΔ⟩⟩
  intro i j
  have hRmat :
      R_hat = matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) := by
    ext a b
    simpa [matMul, matMulRect] using hR a b
  have hQQT : matMul n Q (matTranspose Q) = idMatrix n := by
    ext a b
    exact hQ.right_inv a b
  rw [hRmat, ← matMul_assoc, hQQT, matMul_id_left]

/-- Convert the square explicit panel representation
    `R = Qᵀ(A + ΔA)` to the fixed-`Q` square equation
    `Q R = A + ΔA`. -/
theorem householder_qr_panel_explicit_backward_to_square {n : ℕ}
    (A Q R_hat : Fin n → Fin n → ℝ) (c_bound : ℝ)
    (hPanel :
      HouseholderQRPanelExplicitBackwardError n n A Q R_hat c_bound)
    (hUpper : IsUpperTriangular n R_hat) :
    HouseholderQRExplicitBackwardError n A Q R_hat c_bound := by
  obtain ⟨ΔA, hR, hΔ⟩ := hPanel.result
  refine ⟨hPanel.orth, hUpper, ⟨ΔA, ?_, hΔ⟩⟩
  intro i j
  have hRmat :
      R_hat = matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) := by
    ext a b
    simpa [matMul, matMulRect] using hR a b
  have hQQT : matMul n Q (matTranspose Q) = idMatrix n := by
    ext a b
    exact hPanel.orth.right_inv a b
  rw [hRmat, ← matMul_assoc, hQQT, matMul_id_left]

/-- Implementation-backed square backward-error theorem for the concrete
    recursive rounded Householder QR `R` algorithm. -/
theorem fl_householderQR_R_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp n n A) :
    HouseholderQRBackwardError n A (fl_householderQR_R fp n A)
      (householderQRBackwardCoeff fp n * frobNorm A) := by
  apply householder_qr_panel_backward_to_square
  simpa [fl_householderQR_R, householderQRBackwardCoeff] using
    fl_householderQRPanel_R_backward_error fp n n A hready

/-- Implementation-backed square backward-error theorem for the zero-aware
    concrete recursive rounded Householder QR `R` algorithm.

    This is the preferred end-to-end `R` theorem: zero active columns are
    handled by exact skip branches, while nonzero active columns are analyzed
    through the concrete rounded Householder construction/application kernels. -/
theorem fl_householderQR_R_safe_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelSafeReady fp n n A) :
    HouseholderQRBackwardError n A (fl_householderQR_R_safe fp n A)
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  apply householder_qr_panel_backward_to_square
  simpa [fl_householderQR_R_safe, householderQRBackwardCoeffSafe] using
    fl_householderQRPanel_R_safe_backward_error fp n n A hready

/-- Global-gamma wrapper for the implementation-backed zero-aware Householder
    QR `R` backward-error theorem. -/
theorem fl_householderQR_R_safe_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRBackwardError n A (fl_householderQR_R_safe fp n A)
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  exact fl_householderQR_R_safe_backward_error fp n A
    (HouseholderQRPanelSafeReady_square_of_global_gammaValid fp n A hvalid)

/-- QR backward-error contract including the structural fact that the computed
    `R_hat` is upper triangular.

    The older `HouseholderQRBackwardError` is the normwise backward-error part
    only.  The concrete rounded QR loop proves this stronger packaged contract
    in `fl_householderQR_R_structured_backward_error` and the zero-aware
    `fl_householderQR_R_safe_structured_backward_error`. -/
structure StructuredHouseholderQRBackwardError
    (n : ℕ) (A R_hat : Fin n → Fin n → ℝ) (c_bound : ℝ) : Prop where
  /-- Normwise Householder QR backward error. -/
  backward : HouseholderQRBackwardError n A R_hat c_bound
  /-- The returned `R_hat` has the expected upper-triangular shape. -/
  upper : IsUpperTriangular n R_hat

/-- Theorem 18.4 instantiation: n Householder steps with per-step error ≤ c
    yield total backward error ≤ n · c · ‖A‖_F. -/
theorem householder_qr_backward (n : ℕ) (_hn : 0 < n)
    (A R_hat : Fin n → Fin n → ℝ) (c : ℝ) (_hc : 0 ≤ c)
    (hSeq : OrthogonalSequenceBackwardError n A R_hat n c) :
    HouseholderQRBackwardError n A R_hat
      (↑n * c * frobNorm A) := by
  obtain ⟨Q, ΔA, hQ, hAhat, hbound⟩ := hSeq.result
  exact ⟨⟨Q, ΔA, hQ, by
    intro i j
    -- Q · R̂ = Q · Qᵀ(A + ΔA) = (QQᵀ)(A + ΔA) = I(A + ΔA) = A + ΔA
    have hR : R_hat = matMul n (matTranspose Q) (fun a b => A a b + ΔA a b) :=
      funext fun k => funext fun l => hAhat k l
    have hQQT : matMul n Q (matTranspose Q) = idMatrix n :=
      funext fun a => funext fun b => hQ.right_inv a b
    rw [hR, ← matMul_assoc, hQQT, matMul_id_left], hbound⟩⟩

/-- Structured QR contract derived from the existing backward-error theorem
    plus a separately supplied upper-triangularity proof.

    This is intentionally a packaging theorem for arbitrary `R_hat`, not the
    concrete rounded QR result.  The concrete QR algorithms discharge the
    `hUpper` input separately in
    `fl_householderQR_R_structured_backward_error` and
    `fl_householderQR_R_safe_structured_backward_error`. -/
theorem structured_householder_qr_backward (n : ℕ) (hn : 0 < n)
    (A R_hat : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hSeq : OrthogonalSequenceBackwardError n A R_hat n c)
    (hUpper : IsUpperTriangular n R_hat) :
    StructuredHouseholderQRBackwardError n A R_hat
      (↑n * c * frobNorm A) := by
  exact ⟨householder_qr_backward n hn A R_hat c hc hSeq, hUpper⟩

/-- Implementation-backed structured QR theorem for the concrete recursive
    rounded Householder QR `R` algorithm.

    This theorem combines the recursive panel backward-error bridge with the
    structural fact that `fl_householderQR_R` returns an upper-triangular
    matrix by construction. -/
theorem fl_householderQR_R_structured_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp n n A) :
    StructuredHouseholderQRBackwardError n A (fl_householderQR_R fp n A)
      (householderQRBackwardCoeff fp n * frobNorm A) := by
  exact ⟨fl_householderQR_R_backward_error fp n A hready,
    fl_householderQR_R_upper fp n A⟩

/-- Implementation-backed structured QR theorem for the zero-aware concrete
    recursive rounded Householder QR `R` algorithm.

    This theorem packages the preferred safe backward-error theorem with the
    structural fact that the returned `R` matrix is upper triangular. -/
theorem fl_householderQR_R_safe_structured_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hready : HouseholderQRPanelSafeReady fp n n A) :
    StructuredHouseholderQRBackwardError n A (fl_householderQR_R_safe fp n A)
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  exact ⟨fl_householderQR_R_safe_backward_error fp n A hready,
    fl_householderQR_R_safe_upper fp n A⟩

/-- Global-gamma wrapper for the implementation-backed structured zero-aware
    Householder QR theorem. -/
theorem fl_householderQR_R_safe_structured_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    StructuredHouseholderQRBackwardError n A (fl_householderQR_R_safe fp n A)
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  exact fl_householderQR_R_safe_structured_backward_error fp n A
    (HouseholderQRPanelSafeReady_square_of_global_gammaValid fp n A hvalid)

/-- The `Q` field of the public safe Householder QR witness is orthogonal. -/
theorem fl_householderQR_safe_witness_Q_orthogonal_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    IsOrthogonal n (fl_householderQR_safe_witness fp n A).Q := by
  simpa [fl_householderQR_safe_witness] using
    fl_householderQR_Q_safe_orthogonal_of_global_gammaValid fp n A hvalid

/-- The `R` field of the public safe Householder QR witness is upper
    triangular. -/
theorem fl_householderQR_safe_witness_R_upper
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) :
    IsUpperTriangular n (fl_householderQR_safe_witness fp n A).R := by
  simpa [fl_householderQR_safe_witness] using
    fl_householderQR_R_safe_upper fp n A

/-- The `R` field of the public safe Householder QR witness satisfies the
    implementation-backed structured backward-error theorem. -/
theorem fl_householderQR_safe_witness_R_structured_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    StructuredHouseholderQRBackwardError n A
      (fl_householderQR_safe_witness fp n A).R
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  simpa [fl_householderQR_safe_witness] using
    fl_householderQR_R_safe_structured_backward_error_of_global_gammaValid
      fp n A hvalid

/-- The `R_hat` field of the concrete computed-factor API is upper
    triangular.  This is inherited from the zero-aware rounded `R_safe`
    algorithm; it does not claim any property of the rounded `Q_hat` field. -/
theorem fl_householderQR_computed_safe_R_hat_upper
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ) :
    IsUpperTriangular n (fl_householderQR_computed_safe fp n A).R_hat := by
  simpa [fl_householderQR_computed_safe] using
    fl_householderQR_R_safe_upper fp n A

/-- The `R_hat` field of the concrete computed-factor API satisfies the same
    implementation-backed structured backward-error theorem as `R_safe`.

    The rounded `Q_hat` field is intentionally not used in this theorem; the
    QR backward-error statement is still expressed with the exact orthogonal
    witness from `HouseholderQRWitness`. -/
theorem fl_householderQR_computed_safe_R_hat_structured_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    StructuredHouseholderQRBackwardError n A
      (fl_householderQR_computed_safe fp n A).R_hat
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  simpa [fl_householderQR_computed_safe] using
    fl_householderQR_R_safe_structured_backward_error_of_global_gammaValid
      fp n A hvalid

/-- The public safe Householder QR witness satisfies the fixed-`Q` structured
    backward-error contract.

    This ties the explicit `Q` field directly to the perturbation equation,
    rather than relying only on the existential `Q` inside
    `HouseholderQRBackwardError`. -/
theorem fl_householderQR_safe_witness_explicit_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRExplicitBackwardError n A
      (fl_householderQR_safe_witness fp n A).Q
      (fl_householderQR_safe_witness fp n A).R
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  have hPanel :
      HouseholderQRPanelExplicitBackwardError n n A
        (fl_householderQR_Q_safe fp n A)
        (fl_householderQR_R_safe fp n A)
        (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
    simpa [fl_householderQR_Q_safe, fl_householderQR_R_safe,
      householderQRBackwardCoeffSafe] using
      fl_householderQRPanel_R_safe_explicit_backward_error fp n n A
        (HouseholderQRPanelSafeReady_square_of_global_gammaValid fp n A hvalid)
  have hExplicit :=
    householder_qr_panel_explicit_backward_to_square A
      (fl_householderQR_Q_safe fp n A)
      (fl_householderQR_R_safe fp n A)
      (householderQRBackwardCoeffSafe fp n A * frobNorm A)
      hPanel
      (fl_householderQR_R_safe_upper fp n A)
  simpa [fl_householderQR_safe_witness] using hExplicit

/-- The computed-factor `R_hat` field satisfies the explicit exact-witness
    Householder QR backward-error theorem.

    The `Q` used here is still the exact orthogonal witness from
    `fl_householderQR_safe_witness`, not the rounded accumulated `Q_hat` field
    from `fl_householderQR_computed_safe`. -/
theorem fl_householderQR_computed_safe_R_hat_explicit_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRExplicitBackwardError n A
      (fl_householderQR_safe_witness fp n A).Q
      (fl_householderQR_computed_safe fp n A).R_hat
      (householderQRBackwardCoeffSafe fp n A * frobNorm A) := by
  simpa [fl_householderQR_computed_safe] using
    fl_householderQR_safe_witness_explicit_backward_error_of_global_gammaValid
      fp n A hvalid

end LeanFpAnalysis.FP
