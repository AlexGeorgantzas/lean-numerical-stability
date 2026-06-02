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

-- ============================================================
-- §18.3  Theorem 18.4: Householder QR backward error
-- ============================================================

/-- **Theorem 18.4**: Householder QR factorization backward error (normwise).

    The computed R̂ from Householder QR satisfies A + ΔA = Q·R̂
    where Q is orthogonal and ‖ΔA‖_F ≤ c_bound.

    This is the final QR backward-error contract.  The wrapper theorem below
    derives it from a supplied `OrthogonalSequenceBackwardError`; the rebuild is
    adding concrete bridges that prove this sequence hypothesis from rounded
    Householder construction/application steps. -/
structure HouseholderQRBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (c_bound : ℝ) : Prop where
  /-- There exists an orthogonal Q such that A + ΔA = Q·R̂ with bounded ΔA. -/
  result : ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
    IsOrthogonal n Q ∧
    (∀ i j, matMul n Q R_hat i j = A i j + ΔA i j) ∧
    frobNorm ΔA ≤ c_bound

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

end LeanFpAnalysis.FP
