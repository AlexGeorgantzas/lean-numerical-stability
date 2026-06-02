-- Algorithms/QR/QRSolve.lean
--
-- Backward error analysis for QR-based linear system solve (Higham §18.3).
--
-- Theorem 18.5: Solving Ax = b via Householder QR gives
--   (A + ΔA)x̂ = b + Δb with componentwise/normwise bounds.
--
-- The solve proceeds in three stages:
--   1. Compute QR: A + ΔA₁ = Q R̂  (Theorem 18.4)
--   2. Form Qᵀb:  ĉ = Qᵀ(b + Δb)  (Lemma 18.3 applied to b)
--   3. Solve R̂x̂ = ĉ: (R̂ + ΔR)x̂ = ĉ  (backward substitution)
--
-- Combining these yields the overall backward error.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.TriangularSolve
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §18.3  Theorem 18.5: QR-based solve backward error
-- ============================================================

/-- **Theorem 18.5**: QR-based solve backward error (normwise).

    Given a system Ax = b solved via Householder QR factorization:
    1. Factor A + ΔA₁ = Q·R̂  (Theorem 18.4)
    2. Compute ĉ = Qᵀ(b + Δb)  (Lemma 18.3 on b as a single column)
    3. Solve (R̂ + ΔR)x̂ = ĉ  (back substitution, Theorem 8.5)

    The combined backward error is (A + ΔA)x̂ = b + Δb where
    the bounds on ΔA, Δb depend on the per-step error constants.

    This is the final QR-solve contract.  The component-composition theorem
    below proves how QR factorization, `Qᵀb` application, and back substitution
    combine into this contract.  A concrete `fl_qr_solve` loop is still a
    separate implementation-backed bridge to build. -/
structure QRSolveBackwardError (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (c_A c_b : ℝ) : Prop where
  /-- There exist perturbations ΔA, Δb such that (A+ΔA)x̂ = b+Δb
      with ‖ΔA‖_F ≤ c_A and ‖Δb‖ ≤ c_b (normwise). -/
  result : ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
    (∀ i, matMulVec n (fun a b => A a b + ΔA a b) x_hat i = b i + Δb i) ∧
    frobNorm ΔA ≤ c_A ∧
    (∀ i, |Δb i| ≤ c_b)

/-- Rectangular active-panel contract for the right-hand-side transform in
    Householder QR solve.

    The active panel `A` determines the reflector sequence, while `b` is the
    active right-hand side being transformed by that sequence.  The result is
    represented as `Qᵀ(b + Δb)` with a componentwise perturbation bound. -/
structure HouseholderQRRhsPanelBackwardError (m p : ℕ)
    (A : Fin m → Fin p → ℝ) (b c_hat : Fin m → ℝ)
    (c_bound : ℝ) : Prop where
  /-- There exist an orthogonal transformation and a bounded RHS perturbation. -/
  result : ∃ (Q : Fin m → Fin m → ℝ) (Δb : Fin m → ℝ),
    IsOrthogonal m Q ∧
    (∀ i, c_hat i =
      matMulVec m (matTranspose Q) (fun k => b k + Δb k) i) ∧
    (∀ i, |Δb i| ≤ c_bound)

/-- Drop the first entry of a nonempty vector.  This is exact indexing
    infrastructure for the QR solve right-hand-side recursion. -/
noncomputable def vectorTail {m : ℕ} (b : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => b i.succ

/-- Reconstruct a nonempty vector from its first entry and tail. -/
noncomputable def vectorFromTopTail {m : ℕ}
    (b0 : ℝ) (tail : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  fun i =>
    if hi : i = 0 then b0 else tail (i.pred hi)

/-- Embed a tail-vector perturbation into a nonempty vector with zero first
    component. -/
noncomputable def vectorTrailingPerturbation {m : ℕ}
    (tail : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  vectorFromTopTail 0 tail

@[simp] theorem vectorTail_apply {m : ℕ}
    (b : Fin (m + 1) → ℝ) (i : Fin m) :
    vectorTail b i = b i.succ := rfl

@[simp] theorem vectorFromTopTail_zero {m : ℕ}
    (b0 : ℝ) (tail : Fin m → ℝ) :
    vectorFromTopTail b0 tail 0 = b0 := by
  simp [vectorFromTopTail]

@[simp] theorem vectorFromTopTail_succ {m : ℕ}
    (b0 : ℝ) (tail : Fin m → ℝ) (i : Fin m) :
    vectorFromTopTail b0 tail i.succ = tail i := by
  simp [vectorFromTopTail]

@[simp] theorem vectorTail_vectorFromTopTail {m : ℕ}
    (b0 : ℝ) (tail : Fin m → ℝ) :
    vectorTail (vectorFromTopTail b0 tail) = tail := by
  ext i
  rfl

@[simp] theorem vectorFromTopTail_self {m : ℕ}
    (b : Fin (m + 1) → ℝ) :
    vectorFromTopTail (b 0) (vectorTail b) = b := by
  ext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro i
    rfl

@[simp] theorem vectorTrailingPerturbation_zero {m : ℕ}
    (tail : Fin m → ℝ) :
    vectorTrailingPerturbation tail 0 = 0 := by
  rfl

@[simp] theorem vectorTrailingPerturbation_succ {m : ℕ}
    (tail : Fin m → ℝ) (i : Fin m) :
    vectorTrailingPerturbation tail i.succ = tail i := by
  rfl

/-- Empty-row RHS panels satisfy the RHS backward-error target trivially. -/
theorem householder_qr_rhs_panel_backward_zero_rows (p : ℕ)
    (A : Fin 0 → Fin p → ℝ) (b : Fin 0 → ℝ) :
    HouseholderQRRhsPanelBackwardError 0 p A b b 0 := by
  let Z : Fin 0 → ℝ := fun i => Fin.elim0 i
  refine ⟨⟨idMatrix 0, Z, idMatrix_orthogonal 0, ?_, ?_⟩⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Empty-column active panels apply no QR reflectors to the RHS, so the
    transformed RHS is exactly the input RHS. -/
theorem householder_qr_rhs_panel_backward_zero_cols (m : ℕ)
    (A : Fin (m + 1) → Fin 0 → ℝ) (b : Fin (m + 1) → ℝ) :
    HouseholderQRRhsPanelBackwardError (m + 1) 0 A b b 0 := by
  let Z : Fin (m + 1) → ℝ := fun _ => 0
  refine ⟨⟨idMatrix (m + 1), Z, idMatrix_orthogonal (m + 1), ?_, ?_⟩⟩
  · intro i
    simp [matMulVec, matTranspose, idMatrix, Z, Finset.mem_univ]
  · intro i
    simp [Z]

/-- Left multiplication by an embedded trailing-block matrix leaves the top
    component of a vector unchanged. -/
theorem embedTrailingOne_matMulVec_top {m : ℕ}
    (U : Fin m → Fin m → ℝ) (b : Fin (m + 1) → ℝ) :
    matMulVec (m + 1) (embedTrailingOne U) b 0 = b 0 := by
  unfold matMulVec
  rw [Fin.sum_univ_succ]
  simp

/-- The tail of an embedded trailing-block matrix-vector product is the smaller
    matrix-vector product on the vector tail. -/
theorem vectorTail_embedTrailingOne_matMulVec {m : ℕ}
    (U : Fin m → Fin m → ℝ) (b : Fin (m + 1) → ℝ) :
    vectorTail (matMulVec (m + 1) (embedTrailingOne U) b) =
      matMulVec m U (vectorTail b) := by
  ext i
  unfold vectorTail matMulVec
  rw [Fin.sum_univ_succ]
  simp

/-- Lift a tail-vector backward representation to the full vector by embedding
    the trailing orthogonal factor with a leading identity. -/
theorem vectorFromTopTail_lift_trailing_rep {m : ℕ}
    (Q : Fin m → Fin m → ℝ)
    (b0 : ℝ) (tail ctail Δtail : Fin m → ℝ)
    (hTail : ∀ i, ctail i =
      matMulVec m (matTranspose Q) (fun k => tail k + Δtail k) i) :
    vectorFromTopTail b0 ctail =
      matMulVec (m + 1) (embedTrailingOne (matTranspose Q))
        (fun i => vectorFromTopTail b0 tail i +
          vectorTrailingPerturbation Δtail i) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · unfold matMulVec
    rw [Fin.sum_univ_succ]
    simp
  · intro i
    simp only [vectorFromTopTail_succ]
    rw [hTail i]
    unfold matMulVec
    rw [Fin.sum_univ_succ]
    simp

/-- Recursive cons step for the Householder QR RHS transform.

    If the current rounded reflector step has residual form `y = P*b + e`,
    and the recursive tail transform has a backward-error representation, then
    the full RHS transform has a backward-error representation.  The bound is
    deliberately crude: the accumulated residual is first bounded
    componentwise by `c + α`, then transported through `Pᵀ`, costing a factor
    equal to the active dimension. -/
theorem householder_qr_rhs_panel_backward_cons {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (A_tail : Fin m → Fin p → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (b y e : Fin (m + 1) → ℝ)
    (ctail : Fin m → ℝ)
    (c α : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hy : ∀ i, y i = matMulVec (m + 1) P b i + e i)
    (he : ∀ i, |e i| ≤ c)
    (hTail :
      HouseholderQRRhsPanelBackwardError m p A_tail (vectorTail y) ctail α)
    (hc : 0 ≤ c) (hα : 0 ≤ α) :
    HouseholderQRRhsPanelBackwardError (m + 1) (p + 1) A b
      (vectorFromTopTail (y 0) ctail)
      ((m + 1 : ℝ) * (c + α)) := by
  obtain ⟨Qt, Δtail, hQt, hTailRep, hΔtail⟩ := hTail.result
  let ΔtailFull : Fin (m + 1) → ℝ := vectorTrailingPerturbation Δtail
  let Eta : Fin (m + 1) → ℝ := fun i => e i + ΔtailFull i
  let Δb : Fin (m + 1) → ℝ :=
    matMulVec (m + 1) (matTranspose P) Eta
  let M : Fin (m + 1) → Fin (m + 1) → ℝ :=
    matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ := matTranspose M
  refine ⟨⟨Q, Δb, ?_, ?_, ?_⟩⟩
  · have hEmb :
        IsOrthogonal (m + 1) (embedTrailingOne (matTranspose Qt)) :=
      embedTrailingOne_orthogonal (matTranspose Qt) hQt.transpose
    have hM : IsOrthogonal (m + 1) M := hEmb.mul hP
    exact hM.transpose
  · have hLift :=
      vectorFromTopTail_lift_trailing_rep Qt
        (y 0) (vectorTail y) ctail Δtail hTailRep
    have hInside :
        (fun i => vectorFromTopTail (y 0) (vectorTail y) i +
          vectorTrailingPerturbation Δtail i) =
        fun i => y i + ΔtailFull i := by
      ext i
      simp [ΔtailFull]
    have hPΔ : ∀ i,
        matMulVec (m + 1) P Δb i = Eta i := by
      intro i
      have hPPt :
          matMul (m + 1) P (matTranspose P) = idMatrix (m + 1) := by
        ext a b
        exact hP.right_inv a b
      calc
        matMulVec (m + 1) P Δb i
            = matMulVec (m + 1) P
                (matMulVec (m + 1) (matTranspose P) Eta) i := rfl
        _ = matMulVec (m + 1)
              (matMul (m + 1) P (matTranspose P)) Eta i := by
            exact (matMulVec_matMul (m + 1) P (matTranspose P) Eta i).symm
        _ = matMulVec (m + 1) (idMatrix (m + 1)) Eta i := by
            rw [hPPt]
        _ = Eta i := by
            simpa using congr_fun (idMatrix_mulVec (m + 1) Eta) i
    have hyEta :
        (fun i => y i + ΔtailFull i) =
          matMulVec (m + 1) P (fun k => b k + Δb k) := by
      ext i
      calc
        y i + ΔtailFull i
            = (matMulVec (m + 1) P b i + e i) + ΔtailFull i := by
                rw [hy i]
        _ = matMulVec (m + 1) P b i + Eta i := by
            simp [Eta]
            ring
        _ = matMulVec (m + 1) P b i +
              matMulVec (m + 1) P Δb i := by
            rw [hPΔ i]
        _ = matMulVec (m + 1) P (fun k => b k + Δb k) i := by
            unfold matMulVec
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
    intro i
    have hLift' :
        vectorFromTopTail (y 0) ctail =
          matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
            (fun i => y i + ΔtailFull i) := by
      rw [hLift]
      congr
    calc
      vectorFromTopTail (y 0) ctail i
          = matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
              (fun i => y i + ΔtailFull i) i := by
            rw [hLift']
      _ = matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
            (matMulVec (m + 1) P (fun k => b k + Δb k)) i := by
          rw [hyEta]
      _ = matMulVec (m + 1) M (fun k => b k + Δb k) i := by
          exact (matMulVec_matMul (m + 1)
            (embedTrailingOne (matTranspose Qt)) P
            (fun k => b k + Δb k) i).symm
      _ = matMulVec (m + 1) (matTranspose Q)
            (fun k => b k + Δb k) i := by
          simp [Q, M, matTranspose_involutive]
  · have hEtaComp : ∀ i, |Eta i| ≤ c + α := by
      intro i
      have htail : |ΔtailFull i| ≤ α := by
        refine Fin.cases ?_ ?_ i
        · simpa [ΔtailFull] using hα
        · intro i
          simpa [ΔtailFull] using hΔtail i
      calc
        |Eta i| = |e i + ΔtailFull i| := rfl
        _ ≤ |e i| + |ΔtailFull i| := abs_add_le _ _
        _ ≤ c + α := add_le_add (he i) htail
    have hEtaInf : infNormVec Eta ≤ c + α :=
      infNormVec_le_of_abs_le Eta hEtaComp (add_nonneg hc hα)
    intro i
    calc
      |Δb i|
          = |matMulVec (m + 1) (matTranspose P) Eta i| := rfl
      _ ≤ (m + 1 : ℝ) * infNormVec Eta := by
          simpa [Nat.cast_add, Nat.cast_one] using
            hP.transpose.abs_matMulVec_le_card_infNormVec Eta i
      _ ≤ (m + 1 : ℝ) * (c + α) := by
          exact mul_le_mul_of_nonneg_left hEtaInf (by positivity)

/-- Recursive rounded application of the Householder QR reflector sequence to
    a right-hand side.

    The reflectors are chosen from the current active panel of `A`, exactly as
    in `fl_householderQRPanel_R`.  At each nonempty panel step we apply the same
    rounded reflector to `b`, store the computed top entry, and recurse on the
    computed trailing panel and the tail of the transformed right-hand side.

    This is a concrete `fl_*` component for future QR-solve proofs.  It does
    not compute reflectors from `b`; it follows the QR factorization of `A`. -/
noncomputable def fl_householderQRPanel_rhs (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → (Fin m → ℝ) → Fin m → ℝ
  | 0, _, _A, b => b
  | Nat.succ _, 0, _A, b => b
  | m + 1, p + 1, A, b =>
      let v : Fin (m + 1) → ℝ :=
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
      let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (m + 1) (p + 1) v 1 A
      let bstep : Fin (m + 1) → ℝ :=
        fl_householderApply fp (m + 1) v 1 b
      vectorFromTopTail (bstep 0)
        (fl_householderQRPanel_rhs fp m p (trailingPanel Astep)
          (vectorTail bstep))

@[simp] theorem fl_householderQRPanel_rhs_zero_rows (fp : FPModel)
    {p : ℕ} (A : Fin 0 → Fin p → ℝ) (b : Fin 0 → ℝ) :
    fl_householderQRPanel_rhs fp 0 p A b = b := rfl

@[simp] theorem fl_householderQRPanel_rhs_zero_cols (fp : FPModel)
    {m : ℕ} (A : Fin (m + 1) → Fin 0 → ℝ) (b : Fin (m + 1) → ℝ) :
    fl_householderQRPanel_rhs fp (m + 1) 0 A b = b := rfl

@[simp] theorem fl_householderQRPanel_rhs_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ) :
    fl_householderQRPanel_rhs fp (m + 1) (p + 1) A b =
      let v : Fin (m + 1) → ℝ :=
        fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)
      let Astep : Fin (m + 1) → Fin (p + 1) → ℝ :=
        fl_householderApplyMatrixRect fp (m + 1) (p + 1) v 1 A
      let bstep : Fin (m + 1) → ℝ :=
        fl_householderApply fp (m + 1) v 1 b
      vectorFromTopTail (bstep 0)
        (fl_householderQRPanel_rhs fp m p (trailingPanel Astep)
          (vectorTail bstep)) := rfl

/-- The QR right-hand-side recursion stores the top entry computed by the
    current rounded Householder application. -/
theorem fl_householderQRPanel_rhs_top_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ) :
    fl_householderQRPanel_rhs fp (m + 1) (p + 1) A b 0 =
      fl_householderApply fp (m + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 b 0 := by
  simp [fl_householderQRPanel_rhs]

/-- The tail of the QR right-hand-side recursion is the recursive output on the
    concrete trailing panel and the tail of the current transformed right-hand
    side. -/
theorem vectorTail_fl_householderQRPanel_rhs_succ_succ (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ) :
    vectorTail (fl_householderQRPanel_rhs fp (m + 1) (p + 1) A b) =
      fl_householderQRPanel_rhs fp m p (fl_householderTrailingPanelStep fp A)
        (vectorTail
          (fl_householderApply fp (m + 1)
            (fl_householderNormalizedVector fp (Nat.succ_pos m)
              (panelFirstColumn (Nat.succ_pos p) A)) 1 b)) := by
  simp [fl_householderQRPanel_rhs, fl_householderTrailingPanelStep]

/-- Square specialization of the concrete QR right-hand-side transformation. -/
noncomputable def fl_householderQR_rhs (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_householderQRPanel_rhs fp n n A b

/-- Concrete QR-based linear solve:

    1. compute the recursive rounded Householder `R` factor;
    2. apply the same rounded reflector sequence to `b`;
    3. solve the resulting triangular system by concrete rounded back
       substitution.

    The implementation-backed stability theorem for this full solve is still
    pending; this definition fixes the algorithmic object that theorem should
    analyze. -/
noncomputable def fl_householderQR_solve (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n (fl_householderQR_R fp n A)
    (fl_householderQR_rhs fp n A b)

/-- Recursive componentwise perturbation bound for the concrete QR RHS
    transform.

    The bound follows the actual computed RHS recursion: each nonempty step
    contributes the bounded residual from applying the current rounded
    Householder reflector to `b`, and the tail contribution is transported back
    through the current exact reflector with the crude orthogonal factor
    `(m+1)`.  This is intentionally an implementation-backed recursive bound,
    not yet a collapsed Higham-style closed form. -/
noncomputable def householderQRRhsPanelBackwardBound (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → (Fin m → ℝ) → ℝ
  | 0, _, _A, _b => 0
  | Nat.succ _, 0, _A, _b => 0
  | m + 1, p + 1, A, b =>
      let bstep : Fin (m + 1) → ℝ :=
        fl_householderApply fp (m + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 b
      let cstep : ℝ :=
        (m + 1 : ℝ) * householderConstructApplyBound fp (m + 1) *
          infNormVec b
      (m + 1 : ℝ) *
        (cstep +
          householderQRRhsPanelBackwardBound fp m p
            (fl_householderTrailingPanelStep fp A) (vectorTail bstep))

/-- Square specialization of the recursive QR RHS perturbation bound. -/
noncomputable def householderQRRhsBackwardBound (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : ℝ :=
  householderQRRhsPanelBackwardBound fp n n A b

/-- The recursive QR RHS perturbation bound is nonnegative whenever the
    concrete Householder QR panel run is ready. -/
theorem householderQRRhsPanelBackwardBound_nonneg (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ),
      HouseholderQRPanelReady fp m p A →
      0 ≤ householderQRRhsPanelBackwardBound fp m p A b := by
  intro m
  induction m with
  | zero =>
      intro p A b _hready
      simp [householderQRRhsPanelBackwardBound]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A b _hready
          simp [householderQRRhsPanelBackwardBound]
      | succ p =>
          intro A b hready
          have hready' :
              panelFirstColumn (Nat.succ_pos p) A ≠ 0 ∧
              gammaValid fp (11 * (m + 1) + 23) ∧
              HouseholderQRPanelReady fp m p (fl_householderTrailingPanelStep fp A) := by
            simpa using hready
          let bstep : Fin (m + 1) → ℝ :=
            fl_householderApply fp (m + 1)
              (fl_householderNormalizedVector fp (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) A)) 1 b
          let cstep : ℝ :=
            (m + 1 : ℝ) * householderConstructApplyBound fp (m + 1) *
              infNormVec b
          have hcstep : 0 ≤ cstep := by
            have hc :
                0 ≤ householderConstructApplyBound fp (m + 1) :=
              householderConstructApplyBound_nonneg fp (m + 1) hready'.2.1
            exact mul_nonneg
              (mul_nonneg (by positivity) hc)
              (infNormVec_nonneg b)
          have htail :
              0 ≤ householderQRRhsPanelBackwardBound fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep) :=
            ih p (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
              hready'.2.2
          simp [householderQRRhsPanelBackwardBound]
          exact mul_nonneg (by positivity) (add_nonneg hcstep htail)

/-- Residual-vector form of a one-vector Householder application contract.

    `HouseholderAppError` states `y = (P + ΔP)b`.  This lemma exposes the
    equivalent residual form `y = P b + e`, where `e = ΔP b`. -/
theorem HouseholderAppError.exists_residual_vector {n : ℕ}
    {P : Fin n → Fin n → ℝ} {b y : Fin n → ℝ} {c : ℝ}
    (hstep : HouseholderAppError n P b y c) :
    ∃ e : Fin n → ℝ,
      (∀ i, y i = matMulVec n P b i + e i) ∧
      ∃ ΔP : Fin n → Fin n → ℝ,
        frobNorm ΔP ≤ c ∧
        ∀ i, e i = matMulVec n ΔP b i := by
  obtain ⟨ΔP, hΔP, hpert⟩ := hstep.pert
  refine ⟨fun i => matMulVec n ΔP b i, ?_, ⟨ΔP, hΔP, ?_⟩⟩
  · intro i
    rw [hpert i]
    unfold matMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro i
    rfl

/-- Bounded residual-vector form of a one-vector Householder application
    contract.  If `y = (P + ΔP)b` with `‖ΔP‖_F ≤ c`, then each residual
    component in `y = P b + e` is bounded by `n c ‖b‖∞`. -/
theorem HouseholderAppError.exists_residual_vector_bound {n : ℕ}
    {P : Fin n → Fin n → ℝ} {b y : Fin n → ℝ} {c : ℝ}
    (hstep : HouseholderAppError n P b y c) (hc : 0 ≤ c) :
    ∃ e : Fin n → ℝ,
      (∀ i, y i = matMulVec n P b i + e i) ∧
      (∀ i, |e i| ≤ (n : ℝ) * c * infNormVec b) := by
  obtain ⟨e, hy, ΔP, hΔP, he⟩ := hstep.exists_residual_vector
  refine ⟨e, hy, ?_⟩
  intro i
  rw [he i]
  exact abs_matMulVec_le_card_bound_infNormVec ΔP b hc hΔP i

/-- Concrete one-step right-hand-side Householder application where the
    reflector is constructed from the current QR panel's first column. -/
theorem fl_householder_first_column_rhs_step_error (fp : FPModel)
    {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (b : Fin (m + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    HouseholderAppError (m + 1)
      (householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1)
      b
      (fl_householderApply fp (m + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 b)
      (householderConstructApplyBound fp (m + 1)) := by
  simpa [householderConstructApplyBound] using
    fl_householderConstructApply_appError fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos p) A) b hx hvalid

/-- Residual-vector form of the concrete QR first-column right-hand-side
    Householder step. -/
theorem fl_householder_first_column_rhs_step_residual (fp : FPModel)
    {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (b : Fin (m + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    ∃ e : Fin (m + 1) → ℝ,
      (∀ i,
        fl_householderApply fp (m + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 b i =
          matMulVec (m + 1) P b i + e i) ∧
      ∃ ΔP : Fin (m + 1) → Fin (m + 1) → ℝ,
        frobNorm ΔP ≤ householderConstructApplyBound fp (m + 1) ∧
        ∀ i, e i = matMulVec (m + 1) ΔP b i := by
  intro P
  have hstep :=
    fl_householder_first_column_rhs_step_error fp A b hx hvalid
  simpa [P] using hstep.exists_residual_vector

/-- Bounded residual-vector form of the concrete QR first-column right-hand-side
    Householder step. -/
theorem fl_householder_first_column_rhs_step_residual_bound (fp : FPModel)
    {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (b : Fin (m + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
      householder (m + 1)
        (householderNormalizedVector (m + 1)
          (householderVector (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))
          (householderBetaFromScale (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A))) 1
    ∃ e : Fin (m + 1) → ℝ,
      (∀ i,
        fl_householderApply fp (m + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 b i =
          matMulVec (m + 1) P b i + e i) ∧
      (∀ i,
        |e i| ≤ (m + 1 : ℝ) *
          householderConstructApplyBound fp (m + 1) *
          infNormVec b) := by
  intro P
  have hstep :=
    fl_householder_first_column_rhs_step_error fp A b hx hvalid
  have hc :
      0 ≤ householderConstructApplyBound fp (m + 1) :=
    householderConstructApplyBound_nonneg fp (m + 1) hvalid
  simpa [P] using hstep.exists_residual_vector_bound hc

/-- Implementation-backed recursive backward-error theorem for the concrete
    Householder QR right-hand-side transform.

    This proves the RHS analogue of the recursive `R` theorem: under the same
    `HouseholderQRPanelReady` hypotheses, the concrete
    `fl_householderQRPanel_rhs` loop has a representation
    `Qᵀ(b + Δb)` with a componentwise recursive perturbation bound.  The
    theorem does not yet combine this RHS proof with the QR `R` proof and
    triangular solve into the final `fl_householderQR_solve` theorem. -/
theorem fl_householderQRPanel_rhs_backward_error (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ),
      HouseholderQRPanelReady fp m p A →
      HouseholderQRRhsPanelBackwardError m p A b
        (fl_householderQRPanel_rhs fp m p A b)
        (householderQRRhsPanelBackwardBound fp m p A b) := by
  intro m
  induction m with
  | zero =>
      intro p A b _hready
      simpa [fl_householderQRPanel_rhs, householderQRRhsPanelBackwardBound]
        using householder_qr_rhs_panel_backward_zero_rows p A b
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A b _hready
          simpa [fl_householderQRPanel_rhs, householderQRRhsPanelBackwardBound]
            using householder_qr_rhs_panel_backward_zero_cols m A b
      | succ p =>
          intro A b hready
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
          let bstep : Fin (m + 1) → ℝ :=
            fl_householderApply fp (m + 1)
              (fl_householderNormalizedVector fp (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) A)) 1 b
          let cstep : ℝ :=
            (m + 1 : ℝ) * householderConstructApplyBound fp (m + 1) *
              infNormVec b
          obtain ⟨e, hy, he⟩ := by
            have hraw :=
              fl_householder_first_column_rhs_step_residual_bound fp A b
                hready'.1 hready'.2.1
            simpa [P, bstep, cstep, Nat.cast_add, Nat.cast_one] using hraw
          have hPorth : IsOrthogonal (m + 1) P := by
            have hstep :=
              fl_householder_first_column_rhs_step_error fp A b
                hready'.1 hready'.2.1
            simpa [P] using hstep.orth
          have hTail :
              HouseholderQRRhsPanelBackwardError m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                (fl_householderQRPanel_rhs fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                (householderQRRhsPanelBackwardBound fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep)) :=
            ih p (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
              hready'.2.2
          have hcstep : 0 ≤ cstep := by
            have hc :
                0 ≤ householderConstructApplyBound fp (m + 1) :=
              householderConstructApplyBound_nonneg fp (m + 1) hready'.2.1
            exact mul_nonneg
              (mul_nonneg (by positivity) hc)
              (infNormVec_nonneg b)
          have htailNonneg :
              0 ≤ householderQRRhsPanelBackwardBound fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep) :=
            householderQRRhsPanelBackwardBound_nonneg fp m p
              (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
              hready'.2.2
          have hCons :=
            householder_qr_rhs_panel_backward_cons A
              (fl_householderTrailingPanelStep fp A) P b bstep e
              (fl_householderQRPanel_rhs fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
              cstep
              (householderQRRhsPanelBackwardBound fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
              hPorth hy he hTail hcstep htailNonneg
          simpa [fl_householderQRPanel_rhs,
            householderQRRhsPanelBackwardBound, P, bstep, cstep,
            fl_householderTrailingPanelStep, Nat.cast_add, Nat.cast_one]
            using hCons

/-- Square specialization of the implementation-backed RHS-transform theorem
    for concrete Householder QR solve. -/
theorem fl_householderQR_rhs_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp n n A) :
    HouseholderQRRhsPanelBackwardError n n A b
      (fl_householderQR_rhs fp n A b)
      (householderQRRhsBackwardBound fp n A b) := by
  simpa [fl_householderQR_rhs, householderQRRhsBackwardBound] using
    fl_householderQRPanel_rhs_backward_error fp n n A b hready

/-- **Theorem 18.5 composition**: QR solve backward error from components.

    If we have:
    1. QR backward error: A + ΔA₁ = Q·R̂ with ‖ΔA₁‖_F ≤ c₁
    2. Back-substitution backward error: (R̂ + ΔR)x̂ = ĉ with ‖ΔR‖_F ≤ c₂
    3. Qᵀ application backward error on b: ĉ = Qᵀ(b + Δb) with ‖Δb‖ ≤ c₃

    Then (A + ΔA)x̂ = b + Δb where ΔA = ΔA₁ + Q·ΔR, so
    ‖ΔA‖_F ≤ c₁ + c₂ (using orthogonal invariance ‖Q·ΔR‖_F = ‖ΔR‖_F).

    This theorem proves the pointwise algebra for combining the three stages;
    `qr_solve_backward_error_from_components` below packages it with the
    perturbation bounds into `QRSolveBackwardError`. -/
theorem qr_solve_backward_from_components (n : ℕ) (_hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ)
    (ΔA₁ : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hQR : ∀ i j, matMul n Q R_hat i j = A i j + ΔA₁ i j)
    (_hΔA₁ : frobNorm ΔA₁ ≤ c₁)
    (x_hat : Fin n → ℝ) (c_hat : Fin n → ℝ)
    (ΔR : Fin n → Fin n → ℝ)
    (hSolve : ∀ i, matMulVec n (fun a b => R_hat a b + ΔR a b) x_hat i = c_hat i)
    (_hΔR : frobNorm ΔR ≤ c₂)
    (b : Fin n → ℝ) (Δb : Fin n → ℝ)
    (hQb : ∀ i, c_hat i = matMulVec n (matTranspose Q) (fun k => b k + Δb k) i) :
    ∀ i, matMulVec n (fun a b => A a b + ΔA₁ a b +
      matMul n Q ΔR a b) x_hat i = b i + Δb i := by
  intro i
  -- (A + ΔA₁ + Q·ΔR) x̂ = (Q·R̂ + Q·ΔR) x̂ = Q·(R̂ + ΔR)·x̂ = Q·ĉ
  -- Q·ĉ = Q·Qᵀ(b+Δb) = b + Δb
  -- We prove this pointwise.
  unfold matMulVec
  -- LHS: ∑ j, (A i j + ΔA₁ i j + (Q·ΔR) i j) * x̂_j
  -- We split: ∑ (A + ΔA₁) x̂ + ∑ (Q·ΔR) x̂
  -- = ∑ (Q·R̂) x̂ + ∑ (Q·ΔR) x̂  (by hQR)
  -- = ∑ Q·(R̂ + ΔR) x̂  (distributing Q)
  -- = Q · ((R̂+ΔR)x̂)  (matrix-vector)
  -- = Q · ĉ  (by hSolve)
  -- = Q · Qᵀ(b+Δb)  (by hQb)
  -- = (b + Δb)  (by QQᵀ = I)
  -- We unfold and compute directly.
  have hQRpt : ∀ j, A i j + ΔA₁ i j = matMul n Q R_hat i j := by
    intro j; exact (hQR i j).symm
  simp_rw [show ∀ j : Fin n, (A i j + ΔA₁ i j + matMul n Q ΔR i j) * x_hat j =
    (matMul n Q R_hat i j + matMul n Q ΔR i j) * x_hat j from by
      intro j; rw [hQRpt j]]
  -- Factor: Q·R̂ + Q·ΔR = Q·(R̂ + ΔR)
  simp only [matMul]
  simp_rw [show ∀ j : Fin n,
      ((∑ k, Q i k * R_hat k j) + ∑ k, Q i k * ΔR k j) * x_hat j =
      (∑ k, Q i k * (R_hat k j + ΔR k j)) * x_hat j from by
    intro j; congr 1; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring]
  -- Now: ∑ j, (∑ k, Q i k * (R̂+ΔR) k j) * x̂_j
  -- = ∑ k, Q i k * ∑ j, (R̂+ΔR) k j * x̂_j
  -- = ∑ k, Q i k * ((R̂+ΔR)·x̂)_k = ∑ k, Q i k * ĉ_k
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [show ∀ k j : Fin n,
      Q i k * (R_hat k j + ΔR k j) * x_hat j =
      Q i k * ((R_hat k j + ΔR k j) * x_hat j) from by
    intros; ring]
  simp_rw [← Finset.mul_sum]
  -- ∑ k, Q i k * ∑ j, (R̂+ΔR)_kj * x̂_j = ∑ k, Q i k * ĉ_k
  have hRx : ∀ k : Fin n,
      ∑ j : Fin n, (R_hat k j + ΔR k j) * x_hat j = c_hat k := by
    intro k; exact hSolve k
  simp_rw [hRx]
  -- ∑ k, Q i k * ĉ_k = ∑ k, Q i k * (Qᵀ(b+Δb))_k
  simp_rw [hQb]
  -- ∑ k, Q i k * ∑ l, Qᵀ k l * (b l + Δb l) = b i + Δb i
  unfold matMulVec matTranspose
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [show ∀ l k : Fin n,
      Q i k * (Q l k * (b l + Δb l)) = Q i k * Q l k * (b l + Δb l) from by
    intros; ring]
  simp_rw [← Finset.sum_mul, IsOrthogonal.row_orthonormal hQ]
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- **Frobenius norm of combined perturbation** for QR solve.

    If ‖ΔA₁‖_F ≤ c₁ and ‖ΔR‖_F ≤ c₂, then
    ‖ΔA₁ + Q·ΔR‖_F ≤ c₁ + c₂
    since ‖Q·ΔR‖_F = ‖ΔR‖_F by orthogonal invariance. -/
theorem qr_solve_perturbation_bound (n : ℕ)
    (Q : Fin n → Fin n → ℝ) (ΔA₁ ΔR : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hΔA₁ : frobNorm ΔA₁ ≤ c₁)
    (hΔR : frobNorm ΔR ≤ c₂)
    (_hc₁ : 0 ≤ c₁) (_hc₂ : 0 ≤ c₂) :
    frobNorm (fun a b => ΔA₁ a b + matMul n Q ΔR a b) ≤ c₁ + c₂ := by
  calc frobNorm (fun a b => ΔA₁ a b + matMul n Q ΔR a b)
      ≤ frobNorm ΔA₁ +
          frobNorm (matMul n Q ΔR) :=
            frobNorm_add_le ΔA₁ (matMul n Q ΔR)
    _ = frobNorm ΔA₁ +
          frobNorm ΔR := by
        rw [frobNorm_orthogonal_left Q ΔR hQ]
    _ ≤ c₁ + c₂ := by linarith

/-- **Packaged QR-solve backward error from component contracts**.

    This theorem closes the algebraic packaging gap in Theorem 18.5: once the
    three component stages are available,

    * QR factorization: `Q R_hat = A + ΔA₁`;
    * triangular solve: `(R_hat + ΔR) x_hat = c_hat`;
    * orthogonal application to the right-hand side:
      `c_hat = Qᵀ(b + Δb)`;

    the advertised `QRSolveBackwardError` follows with
    `ΔA = ΔA₁ + Q ΔR` and matrix bound `c₁ + c₂`.  This remains
    component-level; it does not yet define the concrete rounded `fl_qr_solve`
    that produces the component hypotheses. -/
theorem qr_solve_backward_error_from_components (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (R_hat : Fin n → Fin n → ℝ)
    (ΔA₁ : Fin n → Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (hQR : ∀ i j, matMul n Q R_hat i j = A i j + ΔA₁ i j)
    (hΔA₁ : frobNorm ΔA₁ ≤ c₁)
    (x_hat : Fin n → ℝ) (c_hat : Fin n → ℝ)
    (ΔR : Fin n → Fin n → ℝ)
    (hSolve : ∀ i,
      matMulVec n (fun a b => R_hat a b + ΔR a b) x_hat i = c_hat i)
    (hΔR : frobNorm ΔR ≤ c₂)
    (b : Fin n → ℝ) (Δb : Fin n → ℝ)
    (hQb : ∀ i,
      c_hat i = matMulVec n (matTranspose Q) (fun k => b k + Δb k) i)
    (hΔb : ∀ i, |Δb i| ≤ c_b)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    QRSolveBackwardError n A b x_hat (c₁ + c₂) c_b := by
  let ΔA : Fin n → Fin n → ℝ := fun a b => ΔA₁ a b + matMul n Q ΔR a b
  refine ⟨ΔA, Δb, ?_, ?_, hΔb⟩
  · intro i
    have hmat :
        (fun a b => A a b + ΔA a b) =
          fun a b => A a b + ΔA₁ a b + matMul n Q ΔR a b := by
      ext a b
      simp [ΔA]
      ring
    rw [hmat]
    exact qr_solve_backward_from_components n hn A Q R_hat ΔA₁ hQ hQR hΔA₁
      x_hat c_hat ΔR hSolve hΔR b Δb hQb i
  · exact qr_solve_perturbation_bound n Q ΔA₁ ΔR hQ hΔA₁ hΔR hc₁ hc₂

end LeanFpAnalysis.FP
