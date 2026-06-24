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
    combine into this contract.  The zero-aware concrete
    `fl_householderQR_solve` bridge is proved at the end of this file. -/
structure QRSolveBackwardError (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (c_A c_b : ℝ) : Prop where
  /-- There exist perturbations ΔA, Δb such that (A+ΔA)x̂ = b+Δb
      with ‖ΔA‖_F ≤ c_A and ‖Δb‖ ≤ c_b (normwise). -/
  result : ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
    (∀ i, matMulVec n (fun a b => A a b + ΔA a b) x_hat i = b i + Δb i) ∧
    frobNorm ΔA ≤ c_A ∧
    (∀ i, |Δb i| ≤ c_b)

/-- QR-solve backward-error bounds are monotone in the advertised matrix and
    right-hand-side perturbation bounds. -/
theorem QRSolveBackwardError.mono {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b x_hat : Fin n → ℝ}
    {c_A c_b c_A' c_b' : ℝ}
    (h : QRSolveBackwardError n A b x_hat c_A c_b)
    (hA : c_A ≤ c_A') (hb : c_b ≤ c_b') :
    QRSolveBackwardError n A b x_hat c_A' c_b' := by
  obtain ⟨ΔA, Δb, hrep, hΔA, hΔb⟩ := h.result
  exact ⟨⟨ΔA, Δb, hrep, le_trans hΔA hA, fun i =>
    le_trans (hΔb i) hb⟩⟩

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

/-- Rectangular active-panel RHS transform contract with the orthogonal factor
    made explicit.

    This strengthens `HouseholderQRRhsPanelBackwardError` by fixing the `Q`
    witness.  It is the RHS analogue of
    `HouseholderQRPanelExplicitBackwardError` from `HouseholderQR.lean`, and it
    lets QR solve component theorems name the same exact `Q` witness used
    by the concrete rounded `R` recursion. -/
structure HouseholderQRRhsPanelExplicitBackwardError (m p : ℕ)
    (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ)
    (Q : Fin m → Fin m → ℝ) (c_hat : Fin m → ℝ)
    (c_bound : ℝ) : Prop where
  /-- The supplied `Q` is orthogonal. -/
  orth : IsOrthogonal m Q
  /-- The supplied `Q` realizes the RHS perturbation equation. -/
  result : ∃ Δb : Fin m → ℝ,
    (∀ i, c_hat i =
      matMulVec m (matTranspose Q) (fun k => b k + Δb k) i) ∧
    (∀ i, |Δb i| ≤ c_bound)

/-- Forget the explicit `Q` witness and recover the existing existential RHS
    panel contract. -/
theorem HouseholderQRRhsPanelExplicitBackwardError.to_backward_error {m p : ℕ}
    {A : Fin m → Fin p → ℝ} {b c_hat : Fin m → ℝ}
    {Q : Fin m → Fin m → ℝ} {c_bound : ℝ}
    (h : HouseholderQRRhsPanelExplicitBackwardError m p A b Q c_hat c_bound) :
    HouseholderQRRhsPanelBackwardError m p A b c_hat c_bound := by
  obtain ⟨Δb, hrep, hΔb⟩ := h.result
  exact ⟨⟨Q, Δb, h.orth, hrep, hΔb⟩⟩

/-- Simultaneous panel contract for Householder QR solve components.

    This is stronger than separately proving QR factorization and RHS
    transform contracts: the same orthogonal matrix `Q` must explain both
    `R_hat = Qᵀ(A + ΔA)` and `c_hat = Qᵀ(b + Δb)`.  The final QR solve theorem
    needs exactly this shared-`Q` form. -/
structure HouseholderQRPanelSolveBackwardError (m p : ℕ)
    (A R_hat : Fin m → Fin p → ℝ) (b c_hat : Fin m → ℝ)
    (c_A c_b : ℝ) : Prop where
  /-- A common orthogonal factor plus bounded matrix and RHS perturbations. -/
  result : ∃ (Q : Fin m → Fin m → ℝ)
      (ΔA : Fin m → Fin p → ℝ) (Δb : Fin m → ℝ),
    IsOrthogonal m Q ∧
    (∀ i j, R_hat i j =
      matMulRect m m p (matTranspose Q)
        (fun r col => A r col + ΔA r col) i j) ∧
    (∀ i, c_hat i =
      matMulVec m (matTranspose Q) (fun k => b k + Δb k) i) ∧
    frobNorm ΔA ≤ c_A ∧
    (∀ i, |Δb i| ≤ c_b)

/-- Simultaneous panel contract for Householder QR solve components with the
    shared orthogonal factor fixed.

    This is the fixed-`Q` strengthening of
    `HouseholderQRPanelSolveBackwardError`.  The current concrete zero-aware
    Householder QR solve will use `fl_householderQRPanel_Q` as this fixed
    witness. -/
structure HouseholderQRPanelSolveFixedBackwardError (m p : ℕ)
    (A R_hat : Fin m → Fin p → ℝ) (b c_hat : Fin m → ℝ)
    (Q : Fin m → Fin m → ℝ) (c_A c_b : ℝ) : Prop where
  /-- The supplied common `Q` is orthogonal. -/
  orth : IsOrthogonal m Q
  /-- The supplied `Q` explains both the rounded panel and the transformed RHS. -/
  result : ∃ (ΔA : Fin m → Fin p → ℝ) (Δb : Fin m → ℝ),
    (∀ i j, R_hat i j =
      matMulRect m m p (matTranspose Q)
        (fun r col => A r col + ΔA r col) i j) ∧
    (∀ i, c_hat i =
      matMulVec m (matTranspose Q) (fun k => b k + Δb k) i) ∧
    frobNorm ΔA ≤ c_A ∧
    (∀ i, |Δb i| ≤ c_b)

/-- Forget the fixed common `Q` witness and recover the existing shared-`Q`
    existential solve component contract. -/
theorem HouseholderQRPanelSolveFixedBackwardError.to_backward_error {m p : ℕ}
    {A R_hat : Fin m → Fin p → ℝ} {b c_hat : Fin m → ℝ}
    {Q : Fin m → Fin m → ℝ} {c_A c_b : ℝ}
    (h : HouseholderQRPanelSolveFixedBackwardError m p A R_hat b c_hat Q
      c_A c_b) :
    HouseholderQRPanelSolveBackwardError m p A R_hat b c_hat c_A c_b := by
  obtain ⟨ΔA, Δb, hR, hb, hΔA, hΔb⟩ := h.result
  exact ⟨⟨Q, ΔA, Δb, h.orth, hR, hb, hΔA, hΔb⟩⟩

/-- Package explicit fixed-`Q` QR-panel and RHS-transform contracts into the
    simultaneous fixed-`Q` solve component contract. -/
theorem HouseholderQRPanelSolveFixedBackwardError.of_explicit_components
    {m p : ℕ}
    {A R_hat : Fin m → Fin p → ℝ} {b c_hat : Fin m → ℝ}
    {Q : Fin m → Fin m → ℝ} {c_A c_b : ℝ}
    (hR : HouseholderQRPanelExplicitBackwardError m p A Q R_hat c_A)
    (hb : HouseholderQRRhsPanelExplicitBackwardError m p A b Q c_hat c_b) :
    HouseholderQRPanelSolveFixedBackwardError m p A R_hat b c_hat Q
      c_A c_b := by
  obtain ⟨ΔA, hRrep, hΔA⟩ := hR.result
  obtain ⟨Δb, hbRep, hΔb⟩ := hb.result
  exact ⟨hR.orth, ⟨ΔA, Δb, hRrep, hbRep, hΔA, hΔb⟩⟩

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

/-- Dropping the first component cannot increase the vector infinity norm.

    This exact-algebra lemma is used to control the RHS vector passed to the
    recursive tail solve after one Householder application. -/
theorem vectorTail_infNormVec_le {m : ℕ}
    (b : Fin (m + 1) → ℝ) :
    infNormVec (vectorTail b) ≤ infNormVec b := by
  apply infNormVec_le_of_abs_le
  · intro i
    simpa [vectorTail] using abs_le_infNormVec b i.succ
  · exact infNormVec_nonneg b

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

/-- Empty-row RHS panels satisfy the explicit-`Q` RHS target trivially with
    the empty identity matrix. -/
theorem householder_qr_rhs_panel_explicit_backward_zero_rows (p : ℕ)
    (A : Fin 0 → Fin p → ℝ) (b : Fin 0 → ℝ) :
    HouseholderQRRhsPanelExplicitBackwardError 0 p A b (idMatrix 0) b 0 := by
  let Z : Fin 0 → ℝ := fun i => Fin.elim0 i
  refine ⟨idMatrix_orthogonal 0, ⟨Z, ?_, ?_⟩⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Empty-column active panels satisfy the explicit-`Q` RHS target trivially
    with the identity matrix. -/
theorem householder_qr_rhs_panel_explicit_backward_zero_cols (m : ℕ)
    (A : Fin (m + 1) → Fin 0 → ℝ) (b : Fin (m + 1) → ℝ) :
    HouseholderQRRhsPanelExplicitBackwardError (m + 1) 0 A b
      (idMatrix (m + 1)) b 0 := by
  let Z : Fin (m + 1) → ℝ := fun _ => 0
  refine ⟨idMatrix_orthogonal (m + 1), ⟨Z, ?_, ?_⟩⟩
  · intro i
    simp [matMulVec, matTranspose, idMatrix, Z, Finset.mem_univ]
  · intro i
    simp [Z]

/-- Empty-row panels satisfy the simultaneous QR/RHS panel target trivially. -/
theorem householder_qr_panel_solve_backward_zero_rows (p : ℕ)
    (A : Fin 0 → Fin p → ℝ) (b : Fin 0 → ℝ) :
    HouseholderQRPanelSolveBackwardError 0 p A A b b 0 0 := by
  let ZA : Fin 0 → Fin p → ℝ := fun i _ => Fin.elim0 i
  let Zb : Fin 0 → ℝ := fun i => Fin.elim0 i
  refine ⟨⟨idMatrix 0, ZA, Zb, idMatrix_orthogonal 0, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · have hZ : frobNorm ZA = 0 := by
      rw [frobNorm_eq_zero_iff]
      intro i
      exact Fin.elim0 i
    simp [ZA, hZ]
  · intro i
    exact Fin.elim0 i

/-- Empty-column active panels apply no QR reflectors, so both the panel and
    RHS are represented exactly with zero perturbations. -/
theorem householder_qr_panel_solve_backward_zero_cols (m : ℕ)
    (A : Fin (m + 1) → Fin 0 → ℝ) (b : Fin (m + 1) → ℝ) :
    HouseholderQRPanelSolveBackwardError (m + 1) 0 A A b b 0 0 := by
  let ZA : Fin (m + 1) → Fin 0 → ℝ := fun _ j => Fin.elim0 j
  let Zb : Fin (m + 1) → ℝ := fun _ => 0
  refine ⟨⟨idMatrix (m + 1), ZA, Zb, idMatrix_orthogonal (m + 1),
    ?_, ?_, ?_, ?_⟩⟩
  · intro i j
    exact Fin.elim0 j
  · intro i
    simp [matMulVec, matTranspose, idMatrix, Zb, Finset.mem_univ]
  · have hZ : frobNorm ZA = 0 := by
      rw [frobNorm_eq_zero_iff]
      intro i j
      exact Fin.elim0 j
    simp [ZA, hZ]
  · intro i
    simp [Zb]

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

/-- Explicit-`Q` recursive cons step for the Householder QR RHS transform.

    This is the fixed-witness version of
    `householder_qr_rhs_panel_backward_cons`: the theorem conclusion names the
    exact orthogonal factor obtained by prepending the current reflector `P` to
    the explicit tail factor `Qt`. -/
theorem householder_qr_rhs_panel_explicit_backward_cons {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (A_tail : Fin m → Fin p → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Qt : Fin m → Fin m → ℝ)
    (b y e : Fin (m + 1) → ℝ)
    (ctail : Fin m → ℝ)
    (c α : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hy : ∀ i, y i = matMulVec (m + 1) P b i + e i)
    (he : ∀ i, |e i| ≤ c)
    (hTail :
      HouseholderQRRhsPanelExplicitBackwardError m p A_tail
        (vectorTail y) Qt ctail α)
    (hc : 0 ≤ c) (hα : 0 ≤ α) :
    HouseholderQRRhsPanelExplicitBackwardError (m + 1) (p + 1) A b
      (matTranspose (matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P))
      (vectorFromTopTail (y 0) ctail)
      ((m + 1 : ℝ) * (c + α)) := by
  obtain ⟨Δtail, hTailRep, hΔtail⟩ := hTail.result
  let ΔtailFull : Fin (m + 1) → ℝ := vectorTrailingPerturbation Δtail
  let Eta : Fin (m + 1) → ℝ := fun i => e i + ΔtailFull i
  let Δb : Fin (m + 1) → ℝ :=
    matMulVec (m + 1) (matTranspose P) Eta
  let M : Fin (m + 1) → Fin (m + 1) → ℝ :=
    matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ := matTranspose M
  refine ⟨?_, ⟨Δb, ?_, ?_⟩⟩
  · have hEmb :
        IsOrthogonal (m + 1) (embedTrailingOne (matTranspose Qt)) :=
      embedTrailingOne_orthogonal (matTranspose Qt) hTail.orth.transpose
    have hM : IsOrthogonal (m + 1) M := hEmb.mul hP
    simpa [Q, M] using hM.transpose
  · have hLift :=
      vectorFromTopTail_lift_trailing_rep Qt
        (y 0) (vectorTail y) ctail Δtail hTailRep
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
      have hInside :
          (fun i => vectorFromTopTail (y 0) (vectorTail y) i +
            vectorTrailingPerturbation Δtail i) =
          fun i => y i + ΔtailFull i := by
        ext i
        simp [ΔtailFull]
      rw [hInside]
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

/-- Algebraic skip step for the QR RHS transform when the active panel column
    is zero.

    No reflector is applied to the RHS; the tail representation is lifted by
    embedding the tail orthogonal factor with a leading identity. -/
theorem householder_qr_rhs_panel_backward_skip_zero_column {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ)
    (ctail : Fin m → ℝ)
    (β : ℝ)
    (_hcol : panelFirstColumn (Nat.succ_pos p) A = 0)
    (hTail :
      HouseholderQRRhsPanelBackwardError m p (trailingPanel A)
        (vectorTail b) ctail β)
    (hβ : 0 ≤ β) :
    HouseholderQRRhsPanelBackwardError (m + 1) (p + 1) A b
      (vectorFromTopTail (b 0) ctail) β := by
  obtain ⟨Qt, Δtail, hQt, hTailRep, hΔtail⟩ := hTail.result
  let Δb : Fin (m + 1) → ℝ := vectorTrailingPerturbation Δtail
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ := embedTrailingOne Qt
  refine ⟨⟨Q, Δb, ?_, ?_, ?_⟩⟩
  · exact embedTrailingOne_orthogonal Qt hQt
  · have hLift :=
      vectorFromTopTail_lift_trailing_rep Qt
        (b 0) (vectorTail b) ctail Δtail hTailRep
    have hInside :
        (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
          vectorTrailingPerturbation Δtail i) =
        fun i => b i + Δb i := by
      ext i
      simp [Δb]
    have hQtrans :
        matTranspose Q = embedTrailingOne (matTranspose Qt) := by
      simp [Q, matTranspose_embedTrailingOne]
    intro i
    calc
      vectorFromTopTail (b 0) ctail i
          = matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
              (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
                vectorTrailingPerturbation Δtail i) i := by
            exact congrFun hLift i
      _ = matMulVec (m + 1) (matTranspose Q)
            (fun i => b i + Δb i) i := by
          rw [hQtrans, hInside]
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa [Δb] using hβ
    · intro i
      simpa [Δb] using hΔtail i

/-- Explicit-`Q` algebraic skip step for the QR RHS transform when the active
    panel column is zero. -/
theorem householder_qr_rhs_panel_explicit_backward_skip_zero_column {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ)
    (Qt : Fin m → Fin m → ℝ)
    (ctail : Fin m → ℝ)
    (β : ℝ)
    (_hcol : panelFirstColumn (Nat.succ_pos p) A = 0)
    (hTail :
      HouseholderQRRhsPanelExplicitBackwardError m p (trailingPanel A)
        (vectorTail b) Qt ctail β)
    (hβ : 0 ≤ β) :
    HouseholderQRRhsPanelExplicitBackwardError (m + 1) (p + 1) A b
      (embedTrailingOne Qt)
      (vectorFromTopTail (b 0) ctail) β := by
  obtain ⟨Δtail, hTailRep, hΔtail⟩ := hTail.result
  let Δb : Fin (m + 1) → ℝ := vectorTrailingPerturbation Δtail
  refine ⟨embedTrailingOne_orthogonal Qt hTail.orth, ⟨Δb, ?_, ?_⟩⟩
  · have hLift :=
      vectorFromTopTail_lift_trailing_rep Qt
        (b 0) (vectorTail b) ctail Δtail hTailRep
    have hInside :
        (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
          vectorTrailingPerturbation Δtail i) =
        fun i => b i + Δb i := by
      ext i
      simp [Δb]
    intro i
    calc
      vectorFromTopTail (b 0) ctail i
          = matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
              (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
                vectorTrailingPerturbation Δtail i) i := by
            exact congrFun hLift i
      _ = matMulVec (m + 1) (matTranspose (embedTrailingOne Qt))
            (fun i => b i + Δb i) i := by
          rw [matTranspose_embedTrailingOne, hInside]
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa [Δb] using hβ
    · intro i
      simpa [Δb] using hΔtail i

/-- Simultaneous cons step for the QR panel and RHS transform.

    This is the shared-`Q` version of `householder_qr_panel_backward_cons` and
    `householder_qr_rhs_panel_backward_cons`: the same tail orthogonal factor
    is used for the trailing panel and RHS tail, then the same current
    reflector `P` is prepended to both. -/
theorem householder_qr_panel_solve_backward_cons {m p : ℕ}
    (A S : Fin (m + 1) → Fin (p + 1) → ℝ)
    (P : Fin (m + 1) → Fin (m + 1) → ℝ)
    (E : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Rtail : Fin m → Fin p → ℝ)
    (b y e : Fin (m + 1) → ℝ)
    (ctail : Fin m → ℝ)
    (c α d β : ℝ)
    (hP : IsOrthogonal (m + 1) P)
    (hSrep : ∀ i j,
      S i j = matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j)
    (hE : frobNorm E ≤ c * frobNorm A)
    (hSzero : panelFirstColumnTailZero S)
    (hy : ∀ i, y i = matMulVec (m + 1) P b i + e i)
    (he : ∀ i, |e i| ≤ d)
    (hTail :
      HouseholderQRPanelSolveBackwardError m p (trailingPanel S) Rtail
        (vectorTail y) ctail
        (α * frobNorm (trailingPanel S)) β)
    (hα : 0 ≤ α) (hd : 0 ≤ d) (hβ : 0 ≤ β) :
    HouseholderQRPanelSolveBackwardError (m + 1) (p + 1) A
      (panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S) Rtail)
      b (vectorFromTopTail (y 0) ctail)
      ((c + α * (1 + c)) * frobNorm A)
      ((m + 1 : ℝ) * (d + β)) := by
  obtain ⟨Qt, ΔT, Δbt, hQt, hTailR, hTailb, hΔT, hΔbt⟩ := hTail.result
  let Δtail : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  let EtaA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    fun i j => E i j + Δtail i j
  let ΔA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) EtaA
  let Δtailb : Fin (m + 1) → ℝ := vectorTrailingPerturbation Δbt
  let Etab : Fin (m + 1) → ℝ := fun i => e i + Δtailb i
  let Δb : Fin (m + 1) → ℝ :=
    matMulVec (m + 1) (matTranspose P) Etab
  let M : Fin (m + 1) → Fin (m + 1) → ℝ :=
    matMul (m + 1) (embedTrailingOne (matTranspose Qt)) P
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ := matTranspose M
  refine ⟨⟨Q, ΔA, Δb, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have hEmb : IsOrthogonal (m + 1) (embedTrailingOne (matTranspose Qt)) :=
      embedTrailingOne_orthogonal (matTranspose Qt) hQt.transpose
    have hM : IsOrthogonal (m + 1) M := hEmb.mul hP
    exact hM.transpose
  · have hLift :=
      panelFromTopAndTrailing_lift_trailing_rep Qt
        (panelTopLeft S) (panelTopRowTail S)
        (trailingPanel S) Rtail ΔT hTailR
    have hSblocks :
        panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
          (trailingPanel S) = S :=
      panelFromTopAndTrailing_of_firstColumnTailZero S hSzero
    have hPA_Eta :
        (fun i j => S i j + Δtail i j) =
          matMulRect (m + 1) (m + 1) (p + 1) P
            (fun r col => A r col + ΔA r col) := by
      ext i j
      have hPPt :
          matMul (m + 1) P (matTranspose P) = idMatrix (m + 1) := by
        ext a b
        exact hP.right_inv a b
      have hPΔ :
          matMulRect (m + 1) (m + 1) (p + 1) P ΔA = EtaA := by
        show matMulRect (m + 1) (m + 1) (p + 1) P
            (matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) EtaA) = EtaA
        rw [← matMulRect_assoc_square_left, hPPt, matMulRect_id_left]
      calc
        S i j + Δtail i j
            = (matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j) +
                Δtail i j := by rw [hSrep i j]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j +
              EtaA i j := by
            simp [EtaA]
            ring
        _ = matMulRect (m + 1) (m + 1) (p + 1) P A i j +
              matMulRect (m + 1) (m + 1) (p + 1) P ΔA i j := by
            rw [hPΔ]
        _ = matMulRect (m + 1) (m + 1) (p + 1) P
              (fun r col => A r col + ΔA r col) i j := by
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
      have hInside :
          (fun i j =>
            panelFromTopAndTrailing (panelTopLeft S) (panelTopRowTail S)
                (trailingPanel S) i j +
              panelTrailingPerturbation ΔT i j) =
            fun i j => S i j + Δtail i j := by
        ext i j
        rw [hSblocks]
      congr
    rw [hLift']
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt))
        (fun i j => S i j + Δtail i j) i j =
      matMulRect (m + 1) (m + 1) (p + 1) (matTranspose Q)
        (fun r col => A r col + ΔA r col) i j
    rw [hPA_Eta]
    show matMulRect (m + 1) (m + 1) (p + 1)
        (embedTrailingOne (matTranspose Qt))
        (matMulRect (m + 1) (m + 1) (p + 1) P
          (fun r col => A r col + ΔA r col)) i j =
      matMulRect (m + 1) (m + 1) (p + 1) (matTranspose Q)
        (fun r col => A r col + ΔA r col) i j
    rw [← matMulRect_assoc_square_left]
    simp [Q, M, matTranspose_involutive]
  · have hLift :=
      vectorFromTopTail_lift_trailing_rep Qt
        (y 0) (vectorTail y) ctail Δbt hTailb
    have hPΔ : ∀ i,
        matMulVec (m + 1) P Δb i = Etab i := by
      intro i
      have hPPt :
          matMul (m + 1) P (matTranspose P) = idMatrix (m + 1) := by
        ext a b
        exact hP.right_inv a b
      calc
        matMulVec (m + 1) P Δb i
            = matMulVec (m + 1) P
                (matMulVec (m + 1) (matTranspose P) Etab) i := rfl
        _ = matMulVec (m + 1)
              (matMul (m + 1) P (matTranspose P)) Etab i := by
            exact (matMulVec_matMul (m + 1) P (matTranspose P) Etab i).symm
        _ = matMulVec (m + 1) (idMatrix (m + 1)) Etab i := by
            rw [hPPt]
        _ = Etab i := by
            simpa using congr_fun (idMatrix_mulVec (m + 1) Etab) i
    have hyEta :
        (fun i => y i + Δtailb i) =
          matMulVec (m + 1) P (fun k => b k + Δb k) := by
      ext i
      calc
        y i + Δtailb i
            = (matMulVec (m + 1) P b i + e i) + Δtailb i := by
                rw [hy i]
        _ = matMulVec (m + 1) P b i + Etab i := by
            simp [Etab]
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
            (fun i => y i + Δtailb i) := by
      rw [hLift]
      have hInside :
          (fun i => vectorFromTopTail (y 0) (vectorTail y) i +
            vectorTrailingPerturbation Δbt i) =
          fun i => y i + Δtailb i := by
        ext i
        simp [Δtailb]
      rw [hInside]
    calc
      vectorFromTopTail (y 0) ctail i
          = matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
              (fun i => y i + Δtailb i) i := by
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
  · have hΔnorm :
        frobNorm ΔA = frobNorm EtaA := by
      show frobNorm
          (matMulRect (m + 1) (m + 1) (p + 1) (matTranspose P) EtaA) =
        frobNorm EtaA
      exact frobNorm_orthogonal_left_rect (matTranspose P) EtaA hP.transpose
    have hΔtailnorm : frobNorm Δtail = frobNorm ΔT := by
      exact frobNorm_panelTrailingPerturbation ΔT
    have hEta :
        frobNorm EtaA ≤ frobNorm E + frobNorm Δtail := by
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
          = frobNorm EtaA := hΔnorm
      _ ≤ frobNorm E + frobNorm Δtail := hEta
      _ = frobNorm E + frobNorm ΔT := by rw [hΔtailnorm]
      _ ≤ c * frobNorm A + α * ((1 + c) * frobNorm A) := by
          exact add_le_add hE hΔTbound
      _ = (c + α * (1 + c)) * frobNorm A := by ring
  · have hEtabComp : ∀ i, |Etab i| ≤ d + β := by
      intro i
      have htail : |Δtailb i| ≤ β := by
        refine Fin.cases ?_ ?_ i
        · simpa [Δtailb] using hβ
        · intro i
          simpa [Δtailb] using hΔbt i
      calc
        |Etab i| = |e i + Δtailb i| := rfl
        _ ≤ |e i| + |Δtailb i| := abs_add_le _ _
        _ ≤ d + β := add_le_add (he i) htail
    have hEtabInf : infNormVec Etab ≤ d + β :=
      infNormVec_le_of_abs_le Etab hEtabComp (add_nonneg hd hβ)
    intro i
    calc
      |Δb i|
          = |matMulVec (m + 1) (matTranspose P) Etab i| := rfl
      _ ≤ (m + 1 : ℝ) * infNormVec Etab := by
          simpa [Nat.cast_add, Nat.cast_one] using
            hP.transpose.abs_matMulVec_le_card_infNormVec Etab i
      _ ≤ (m + 1 : ℝ) * (d + β) := by
          exact mul_le_mul_of_nonneg_left hEtabInf (by positivity)

/-- Shared-`Q` algebraic skip step for a degenerate active Householder QR
    solve panel.

    If the active first column is already zero, the factorization and RHS
    transform both skip the current reflector.  A simultaneous tail proof can
    be lifted to the full panel/vector by embedding the tail orthogonal factor
    with a leading identity. -/
theorem householder_qr_panel_solve_backward_skip_zero_column {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Rtail : Fin m → Fin p → ℝ)
    (b : Fin (m + 1) → ℝ)
    (ctail : Fin m → ℝ)
    (α β : ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0)
    (hTail :
      HouseholderQRPanelSolveBackwardError m p (trailingPanel A) Rtail
        (vectorTail b) ctail
        (α * frobNorm (trailingPanel A)) β)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    HouseholderQRPanelSolveBackwardError (m + 1) (p + 1) A
      (panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A) Rtail)
      b (vectorFromTopTail (b 0) ctail)
      (α * frobNorm A) β := by
  obtain ⟨Qt, ΔT, Δbt, hQt, hTailR, hTailb, hΔT, hΔbt⟩ := hTail.result
  let ΔA : Fin (m + 1) → Fin (p + 1) → ℝ :=
    panelTrailingPerturbation ΔT
  let Δb : Fin (m + 1) → ℝ := vectorTrailingPerturbation Δbt
  let Q : Fin (m + 1) → Fin (m + 1) → ℝ := embedTrailingOne Qt
  refine ⟨⟨Q, ΔA, Δb, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact embedTrailingOne_orthogonal Qt hQt
  · have hLift :=
      panelFromTopAndTrailing_lift_trailing_rep Qt
        (panelTopLeft A) (panelTopRowTail A)
        (trailingPanel A) Rtail ΔT hTailR
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
  · have hLift :=
      vectorFromTopTail_lift_trailing_rep Qt
        (b 0) (vectorTail b) ctail Δbt hTailb
    have hInside :
        (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
          vectorTrailingPerturbation Δbt i) =
        fun i => b i + Δb i := by
      ext i
      simp [Δb]
    have hQtrans :
        matTranspose Q = embedTrailingOne (matTranspose Qt) := by
      simp [Q, matTranspose_embedTrailingOne]
    intro i
    calc
      vectorFromTopTail (b 0) ctail i
          = matMulVec (m + 1) (embedTrailingOne (matTranspose Qt))
              (fun i => vectorFromTopTail (b 0) (vectorTail b) i +
                vectorTrailingPerturbation Δbt i) i := by
            exact congrFun hLift i
      _ = matMulVec (m + 1) (matTranspose Q)
            (fun i => b i + Δb i) i := by
          rw [hQtrans, hInside]
  · have hΔnorm : frobNorm ΔA = frobNorm ΔT := by
      exact frobNorm_panelTrailingPerturbation ΔT
    calc
      frobNorm ΔA = frobNorm ΔT := hΔnorm
      _ ≤ α * frobNorm (trailingPanel A) := hΔT
      _ ≤ α * frobNorm A :=
          mul_le_mul_of_nonneg_left (frobNorm_trailingPanel_le A) hα
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa [Δb] using hβ
    · intro i
      simpa [Δb] using hΔbt i

/-- Zero-aware recursive rounded application of the Householder QR reflector
    sequence to a right-hand side.

    This follows `fl_householderQRPanel_R`: if the active first column is
    zero, no reflector is applied to the RHS and the recursion continues on the
    exact trailing panel and vector tail.  Otherwise it uses the same rounded
    reflector as the concrete nonzero panel step. -/
noncomputable def fl_householderQRPanel_rhs (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → (Fin m → ℝ) → Fin m → ℝ
  | 0, _, _A, b => b
  | Nat.succ _, 0, _A, b => b
  | m + 1, p + 1, A, b =>
      if _hcol : panelFirstColumn (Nat.succ_pos p) A = 0 then
        vectorFromTopTail (b 0)
          (fl_householderQRPanel_rhs fp m p (trailingPanel A)
            (vectorTail b))
      else
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

@[simp] theorem fl_householderQRPanel_rhs_succ_succ_zero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A = 0) :
    fl_householderQRPanel_rhs fp (m + 1) (p + 1) A b =
      vectorFromTopTail (b 0)
        (fl_householderQRPanel_rhs fp m p (trailingPanel A)
          (vectorTail b)) := by
  simp [fl_householderQRPanel_rhs, hcol]

@[simp] theorem fl_householderQRPanel_rhs_succ_succ_nonzero (fp : FPModel)
    {m p : ℕ} (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (b : Fin (m + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
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
          (vectorTail bstep)) := by
  simp [fl_householderQRPanel_rhs, hcol]

/-- Square specialization of the zero-aware concrete QR right-hand-side
    transformation. -/
noncomputable def fl_householderQR_rhs (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_householderQRPanel_rhs fp n n A b

/-- Zero-aware concrete QR-based linear solve. -/
noncomputable def fl_householderQR_solve (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub fp n (fl_householderQR fp n A).R
    (fl_householderQR_rhs fp n A b)

/-- Recursive componentwise perturbation bound for the zero-aware QR RHS
    transform.  Zero active columns do not apply a rounded reflector, so the
    bound recurses directly on the vector tail. -/
noncomputable def householderQRRhsPanelBackwardBound (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → (Fin m → ℝ) → ℝ
  | 0, _, _A, _b => 0
  | Nat.succ _, 0, _A, _b => 0
  | m + 1, p + 1, A, b =>
      if panelFirstColumn (Nat.succ_pos p) A = 0 then
        householderQRRhsPanelBackwardBound fp m p
          (trailingPanel A) (vectorTail b)
      else
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

/-- Square specialization of the zero-aware recursive QR RHS perturbation
    bound. -/
noncomputable def householderQRRhsBackwardBound (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : ℝ :=
  householderQRRhsPanelBackwardBound fp n n A b

/-- Conservative dimension-only coefficient controlling the recursive
    zero-aware QR RHS perturbation bound.

    The recursive RHS proof follows the actual computed vector sequence, so its
    raw bound depends on intermediate rounded right-hand sides.  This
    coefficient eliminates those intermediate vectors using the one-step
    norm-growth lemma below.  The extra `tail + ...` term intentionally also
    dominates zero-column skip branches. -/
noncomputable def householderQRRhsPanelGrowthCoeff (fp : FPModel) :
    (m p : ℕ) → ℝ
  | 0, _ => 0
  | Nat.succ _, 0 => 0
  | m + 1, p + 1 =>
      let tail : ℝ := householderQRRhsPanelGrowthCoeff fp m p
      let C : ℝ := householderConstructApplyBound fp (m + 1)
      tail +
        (m + 1 : ℝ) *
          ((m + 1 : ℝ) * C +
            tail * ((m + 1 : ℝ) * (1 + C)))

/-- Square specialization of `householderQRRhsPanelGrowthCoeff`. -/
noncomputable def householderQRRhsGrowthCoeff (fp : FPModel) (n : ℕ) : ℝ :=
  householderQRRhsPanelGrowthCoeff fp n n

/-- The dimension-only QR RHS growth coefficient is nonnegative under the
    same global one-step gamma-validity condition used for the active panel. -/
theorem householderQRRhsPanelGrowthCoeff_nonneg (fp : FPModel) :
    ∀ (m p : ℕ), gammaValid fp (11 * m + 23) →
      0 ≤ householderQRRhsPanelGrowthCoeff fp m p := by
  intro m
  induction m with
  | zero =>
      intro p _hvalid
      simp [householderQRRhsPanelGrowthCoeff]
  | succ m ih =>
      intro p hvalid
      cases p with
      | zero =>
          simp [householderQRRhsPanelGrowthCoeff]
      | succ p =>
          let tail : ℝ := householderQRRhsPanelGrowthCoeff fp m p
          let C : ℝ := householderConstructApplyBound fp (m + 1)
          have hvalid_tail : gammaValid fp (11 * m + 23) :=
            gammaValid_mono fp (by omega) hvalid
          have htail : 0 ≤ tail := by
            simpa [tail] using ih p hvalid_tail
          have hC : 0 ≤ C := by
            simpa [C] using
              householderConstructApplyBound_nonneg fp (m + 1) hvalid
          have hstep :
              0 ≤ (m + 1 : ℝ) *
                ((m + 1 : ℝ) * C +
                  tail * ((m + 1 : ℝ) * (1 + C))) := by
            have hinside :
                0 ≤ (m + 1 : ℝ) * C +
                  tail * ((m + 1 : ℝ) * (1 + C)) := by
              exact add_nonneg
                (mul_nonneg (by positivity) hC)
                (mul_nonneg htail
                  (mul_nonneg (by positivity) (by linarith)))
            exact mul_nonneg (by positivity) hinside
          simpa [householderQRRhsPanelGrowthCoeff, tail, C] using
            add_nonneg htail hstep

/-- Square specialization: the QR RHS growth coefficient is nonnegative. -/
theorem householderQRRhsGrowthCoeff_nonneg (fp : FPModel) (n : ℕ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    0 ≤ householderQRRhsGrowthCoeff fp n := by
  simpa [householderQRRhsGrowthCoeff] using
    householderQRRhsPanelGrowthCoeff_nonneg fp n n hvalid

/-- Conservative closed growth bound for the square QR RHS growth
    coefficient.

    This is a local derived bound, not a sharp Higham constant.  It replaces
    the decreasing-dimension recursive coefficient by a uniform `n`-dimensional
    growth expression, using monotonicity of the one-step Householder
    construction/application coefficient. -/
theorem householderQRRhsGrowthCoeff_le_closedGrowth
    (fp : FPModel) :
    ∀ n : ℕ, gammaValid fp (11 * n + 23) →
      householderQRRhsGrowthCoeff fp n ≤
        (n : ℝ) * ((n : ℝ) ^ 2 * householderConstructApplyBound fp n) *
          (1 + (n : ℝ) ^ 2 *
            (1 + householderConstructApplyBound fp n)) ^ n := by
  intro n
  induction n with
  | zero =>
      intro _hvalid
      simp [householderQRRhsGrowthCoeff, householderQRRhsPanelGrowthCoeff]
  | succ n ih =>
      intro hvalid
      let sR : ℝ := (n + 1 : ℝ)
      let C : ℝ := householderConstructApplyBound fp (n + 1)
      let A : ℝ := 1 + sR ^ 2 * (1 + C)
      let B : ℝ := sR ^ 2 * C
      let tail : ℝ := householderQRRhsGrowthCoeff fp n
      have hvalid_tail : gammaValid fp (11 * n + 23) :=
        gammaValid_mono fp (by omega) hvalid
      have hC : 0 ≤ C := by
        simpa [C] using
          householderConstructApplyBound_nonneg fp (n + 1) hvalid
      have hCt : 0 ≤ householderConstructApplyBound fp n :=
        householderConstructApplyBound_nonneg fp n hvalid_tail
      have hCt_le_C :
          householderConstructApplyBound fp n ≤ C := by
        simpa [C] using
          householderConstructApplyBound_mono fp (Nat.le_succ n) hvalid
      have hsR_nonneg : 0 ≤ sR := by
        dsimp [sR]
        positivity
      have hA_ge_one : 1 ≤ A := by
        dsimp [A]
        nlinarith [sq_nonneg sR, hC]
      have hA_nonneg : 0 ≤ A := by linarith
      have hB_nonneg : 0 ≤ B := by
        dsimp [B]
        exact mul_nonneg (sq_nonneg sR) hC
      have htail_nonneg : 0 ≤ tail := by
        simpa [tail] using
          householderQRRhsGrowthCoeff_nonneg fp n hvalid_tail
      have hn_sq_le :
          (n : ℝ) ^ 2 ≤ sR ^ 2 := by
        have hn_le_s : (n : ℝ) ≤ sR := by
          dsimp [sR]
          norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg (n : ℝ), sq_nonneg sR]
      have hBt_le_B :
          (n : ℝ) ^ 2 * householderConstructApplyBound fp n ≤ B := by
        dsimp [B]
        exact mul_le_mul hn_sq_le hCt_le_C hCt (sq_nonneg sR)
      have hAt_le_A :
          1 + (n : ℝ) ^ 2 *
              (1 + householderConstructApplyBound fp n) ≤ A := by
        have h1_le : 1 + householderConstructApplyBound fp n ≤ 1 + C := by
          linarith
        have h1_nonneg : 0 ≤ 1 + householderConstructApplyBound fp n := by
          linarith
        have hprod :
            (n : ℝ) ^ 2 * (1 + householderConstructApplyBound fp n) ≤
              sR ^ 2 * (1 + C) :=
          mul_le_mul hn_sq_le h1_le h1_nonneg (sq_nonneg sR)
        dsimp [A]
        linarith
      have hAt_nonneg :
          0 ≤ 1 + (n : ℝ) ^ 2 *
              (1 + householderConstructApplyBound fp n) := by
        exact add_nonneg zero_le_one
          (mul_nonneg (sq_nonneg (n : ℝ)) (by linarith))
      have hpow :
          (1 + (n : ℝ) ^ 2 *
              (1 + householderConstructApplyBound fp n)) ^ n ≤
            A ^ n :=
        pow_le_pow_left₀ hAt_nonneg hAt_le_A n
      have htail_to_global :
          tail ≤ (n : ℝ) * B * A ^ n := by
        have hIH := ih hvalid_tail
        have hprod :
            ((n : ℝ) ^ 2 * householderConstructApplyBound fp n) *
                (1 + (n : ℝ) ^ 2 *
                  (1 + householderConstructApplyBound fp n)) ^ n ≤
              B * A ^ n :=
          mul_le_mul hBt_le_B hpow
            (pow_nonneg hAt_nonneg n) hB_nonneg
        have hscaled :
            (n : ℝ) *
                (((n : ℝ) ^ 2 * householderConstructApplyBound fp n) *
                  (1 + (n : ℝ) ^ 2 *
                    (1 + householderConstructApplyBound fp n)) ^ n) ≤
              (n : ℝ) * (B * A ^ n) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        calc
          tail
              ≤ (n : ℝ) *
                  ((n : ℝ) ^ 2 * householderConstructApplyBound fp n) *
                  (1 + (n : ℝ) ^ 2 *
                    (1 + householderConstructApplyBound fp n)) ^ n := hIH
          _ = (n : ℝ) *
                (((n : ℝ) ^ 2 * householderConstructApplyBound fp n) *
                  (1 + (n : ℝ) ^ 2 *
                    (1 + householderConstructApplyBound fp n)) ^ n) := by
              ring
          _ ≤ (n : ℝ) * (B * A ^ n) := hscaled
          _ = (n : ℝ) * B * A ^ n := by ring
      have hrec :
          householderQRRhsGrowthCoeff fp (n + 1) = B + tail * A := by
        simp [householderQRRhsGrowthCoeff,
          householderQRRhsPanelGrowthCoeff, tail, B, A, C, sR]
        ring
      have hpow_ge_one : 1 ≤ A ^ (n + 1) := by
        have hbase : (1 : ℝ) ^ (n + 1) ≤ A ^ (n + 1) :=
          pow_le_pow_left₀ zero_le_one hA_ge_one (n + 1)
        simpa using hbase
      have hB_le_Bpow : B ≤ B * A ^ (n + 1) := by
        calc
          B = B * 1 := by ring
          _ ≤ B * A ^ (n + 1) :=
              mul_le_mul_of_nonneg_left hpow_ge_one hB_nonneg
      calc
        householderQRRhsGrowthCoeff fp (n + 1)
            = B + tail * A := hrec
        _ ≤ B + ((n : ℝ) * B * A ^ n) * A := by
            have hmul :
                tail * A ≤ ((n : ℝ) * B * A ^ n) * A :=
              mul_le_mul_of_nonneg_right htail_to_global hA_nonneg
            exact add_le_add (le_refl B) hmul
        _ = B + (n : ℝ) * B * A ^ (n + 1) := by
            rw [pow_succ]
            ring
        _ ≤ ((n + 1 : ℕ) : ℝ) * B * A ^ (n + 1) := by
            calc
              B + (n : ℝ) * B * A ^ (n + 1)
                  ≤ B * A ^ (n + 1) +
                      (n : ℝ) * B * A ^ (n + 1) := by
                    exact add_le_add hB_le_Bpow (le_refl _)
              _ = (((n : ℝ) + 1) * B * A ^ (n + 1)) := by ring
              _ = ((n + 1 : ℕ) : ℝ) * B * A ^ (n + 1) := by
                    norm_num [Nat.cast_add, Nat.cast_one]
        _ = ((n + 1 : ℕ) : ℝ) *
              (((n + 1 : ℕ) : ℝ) ^ 2 *
                householderConstructApplyBound fp (n + 1)) *
              (1 + ((n + 1 : ℕ) : ℝ) ^ 2 *
                (1 + householderConstructApplyBound fp (n + 1))) ^ (n + 1) := by
            simp [A, B, C, sR]

/-- The zero-aware recursive QR RHS perturbation bound is nonnegative whenever
    the zero-aware panel run has the required gamma hypotheses on nonzero branches. -/
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
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
            simpa [householderQRRhsPanelBackwardBound, hcol] using
              ih p (trailingPanel A) (vectorTail b) htailReady
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
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
                householderConstructApplyBound_nonneg fp (m + 1) hready'.1
              exact mul_nonneg
                (mul_nonneg (by positivity) hc)
                (infNormVec_nonneg b)
            have htail :
                0 ≤ householderQRRhsPanelBackwardBound fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep) :=
              ih p (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hready'.2
            simp [householderQRRhsPanelBackwardBound, hcol]
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

/-- Infinity-norm growth bound for the concrete QR first-column RHS
    Householder step.

    This is a derived consequence of the implementation-backed one-reflector
    error theorem: the rounded step is `P b + e`, the exact reflector `P` is
    orthogonal, and `|e_i|` is bounded componentwise.  The factor is deliberately
    crude but source-traceable to the same concrete `fl_householderApply`
    bridge used by the RHS backward-error proof. -/
theorem fl_householder_first_column_rhs_step_infNormVec_le (fp : FPModel)
    {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (b : Fin (m + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    let y : Fin (m + 1) → ℝ :=
      fl_householderApply fp (m + 1)
        (fl_householderNormalizedVector fp (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A)) 1 b
    infNormVec y ≤
      ((m + 1 : ℝ) *
        (1 + householderConstructApplyBound fp (m + 1))) *
        infNormVec b := by
  intro y
  let P : Fin (m + 1) → Fin (m + 1) → ℝ :=
    householder (m + 1)
      (householderNormalizedVector (m + 1)
        (householderVector (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A))
        (householderBetaFromScale (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A))) 1
  let C : ℝ := householderConstructApplyBound fp (m + 1)
  obtain ⟨e, hy, he⟩ := by
    have hraw :=
      fl_householder_first_column_rhs_step_residual_bound fp A b hx hvalid
    simpa [P, y, C, Nat.cast_add, Nat.cast_one] using hraw
  have hPorth : IsOrthogonal (m + 1) P := by
    have hstep :=
      fl_householder_first_column_rhs_step_error fp A b hx hvalid
    simpa [P, C] using hstep.orth
  have hC : 0 ≤ C := by
    simpa [C] using householderConstructApplyBound_nonneg fp (m + 1) hvalid
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |y i|
          = |fl_householderApply fp (m + 1)
              (fl_householderNormalizedVector fp (Nat.succ_pos m)
                (panelFirstColumn (Nat.succ_pos p) A)) 1 b i| := by
              rfl
      _ = |matMulVec (m + 1) P b i + e i| := by
          simpa [P] using congrArg abs (hy i)
      _ ≤ |matMulVec (m + 1) P b i| + |e i| := abs_add_le _ _
      _ ≤ (m + 1 : ℝ) * infNormVec b +
            (m + 1 : ℝ) * C * infNormVec b := by
          exact add_le_add
            (by
              simpa [Nat.cast_add, Nat.cast_one] using
                hPorth.abs_matMulVec_le_card_infNormVec b i)
            (by simpa [C, Nat.cast_add, Nat.cast_one] using he i)
      _ = ((m + 1 : ℝ) * (1 + C)) * infNormVec b := by ring
      _ = ((m + 1 : ℝ) *
            (1 + householderConstructApplyBound fp (m + 1))) *
            infNormVec b := by simp [C]
  · exact mul_nonneg
      (mul_nonneg (by positivity) (by linarith))
      (infNormVec_nonneg b)

/-- Tail version of
    `fl_householder_first_column_rhs_step_infNormVec_le`. -/
theorem vectorTail_fl_householder_first_column_rhs_step_infNormVec_le
    (fp : FPModel)
    {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) (b : Fin (m + 1) → ℝ)
    (hx : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23)) :
    infNormVec
      (vectorTail
        (fl_householderApply fp (m + 1)
          (fl_householderNormalizedVector fp (Nat.succ_pos m)
            (panelFirstColumn (Nat.succ_pos p) A)) 1 b)) ≤
      ((m + 1 : ℝ) *
        (1 + householderConstructApplyBound fp (m + 1))) *
        infNormVec b := by
  let y : Fin (m + 1) → ℝ :=
    fl_householderApply fp (m + 1)
      (fl_householderNormalizedVector fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos p) A)) 1 b
  exact le_trans (vectorTail_infNormVec_le y)
    (by
      simpa [y] using
        fl_householder_first_column_rhs_step_infNormVec_le fp A b hx hvalid)

/-- The implementation-backed recursive zero-aware QR RHS perturbation bound
    is controlled by the dimension-only RHS growth coefficient times
    `‖b‖∞`.

    This theorem is the first closed-form bridge for the RHS side of QR solve:
    the left side follows the actual computed Householder QR RHS recursion,
    while the right side removes intermediate rounded vectors using
    `fl_householder_first_column_rhs_step_infNormVec_le`. -/
theorem householderQRRhsPanelBackwardBound_le_growthCoeff
    (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ),
      gammaValid fp (11 * m + 23) →
      HouseholderQRPanelReady fp m p A →
      householderQRRhsPanelBackwardBound fp m p A b ≤
        householderQRRhsPanelGrowthCoeff fp m p * infNormVec b := by
  intro m
  induction m with
  | zero =>
      intro p A b _hvalid _hready
      simp [householderQRRhsPanelBackwardBound,
        householderQRRhsPanelGrowthCoeff]
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A b _hvalid _hready
          simp [householderQRRhsPanelBackwardBound,
            householderQRRhsPanelGrowthCoeff]
      | succ p =>
          intro A b hvalid hready
          let tailCoeff : ℝ := householderQRRhsPanelGrowthCoeff fp m p
          let C : ℝ := householderConstructApplyBound fp (m + 1)
          let nR : ℝ := (m + 1 : ℝ)
          have hvalid_tail : gammaValid fp (11 * m + 23) :=
            gammaValid_mono fp (by omega) hvalid
          have htailCoeff : 0 ≤ tailCoeff := by
            simpa [tailCoeff] using
              householderQRRhsPanelGrowthCoeff_nonneg fp m p hvalid_tail
          have hC : 0 ≤ C := by
            simpa [C] using
              householderConstructApplyBound_nonneg fp (m + 1) hvalid
          have hnR : 0 ≤ nR := by
            dsimp [nR]
            positivity
          have hstepNonneg :
              0 ≤ nR *
                (nR * C + tailCoeff * (nR * (1 + C))) := by
            have hinside :
                0 ≤ nR * C + tailCoeff * (nR * (1 + C)) := by
              exact add_nonneg
                (mul_nonneg hnR hC)
                (mul_nonneg htailCoeff
                  (mul_nonneg hnR (by linarith)))
            exact mul_nonneg hnR hinside
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
            have htail :=
              ih p (trailingPanel A) (vectorTail b) hvalid_tail htailReady
            have htailNorm : infNormVec (vectorTail b) ≤ infNormVec b :=
              vectorTail_infNormVec_le b
            have htailToB :
                householderQRRhsPanelBackwardBound fp m p
                    (trailingPanel A) (vectorTail b) ≤
                  tailCoeff * infNormVec b := by
              exact le_trans htail
                (mul_le_mul_of_nonneg_left htailNorm htailCoeff)
            have hdom :
                tailCoeff * infNormVec b ≤
                  (tailCoeff +
                    nR * (nR * C + tailCoeff * (nR * (1 + C)))) *
                    infNormVec b := by
              have hb : 0 ≤ infNormVec b := infNormVec_nonneg b
              nlinarith
            simpa [householderQRRhsPanelBackwardBound,
              householderQRRhsPanelGrowthCoeff, hcol, tailCoeff, C, nR]
              using le_trans htailToB hdom
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
            let bstep : Fin (m + 1) → ℝ :=
              fl_householderApply fp (m + 1)
                (fl_householderNormalizedVector fp (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A)) 1 b
            let cstep : ℝ :=
              (m + 1 : ℝ) * householderConstructApplyBound fp (m + 1) *
                infNormVec b
            have htail :=
              ih p (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hvalid_tail hready'.2
            have htailNorm :
                infNormVec (vectorTail bstep) ≤
                  nR * (1 + C) * infNormVec b := by
              simpa [bstep, C, nR, Nat.cast_add, Nat.cast_one] using
                vectorTail_fl_householder_first_column_rhs_step_infNormVec_le
                  fp A b hcol hready'.1
            have htailToB :
                householderQRRhsPanelBackwardBound fp m p
                    (fl_householderTrailingPanelStep fp A) (vectorTail bstep) ≤
                  tailCoeff * (nR * (1 + C) * infNormVec b) := by
              exact le_trans htail
                (mul_le_mul_of_nonneg_left htailNorm htailCoeff)
            have hmain :
                nR *
                    (nR * C * infNormVec b +
                      householderQRRhsPanelBackwardBound fp m p
                        (fl_householderTrailingPanelStep fp A)
                        (vectorTail bstep)) ≤
                  (tailCoeff +
                    nR * (nR * C + tailCoeff * (nR * (1 + C)))) *
                    infNormVec b := by
              have hb : 0 ≤ infNormVec b := infNormVec_nonneg b
              nlinarith
            simpa [householderQRRhsPanelBackwardBound,
              householderQRRhsPanelGrowthCoeff, hcol, tailCoeff, C, nR,
              bstep, cstep, Nat.cast_add, Nat.cast_one] using hmain

/-- Square specialization of
    `householderQRRhsPanelBackwardBound_le_growthCoeff`. -/
theorem householderQRRhsBackwardBound_le_growthCoeff
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23))
    (hready : HouseholderQRPanelReady fp n n A) :
    householderQRRhsBackwardBound fp n A b ≤
      householderQRRhsGrowthCoeff fp n * infNormVec b := by
  simpa [householderQRRhsBackwardBound, householderQRRhsGrowthCoeff] using
    householderQRRhsPanelBackwardBound_le_growthCoeff fp
      n n A b hvalid hready

/-- Global-gamma square specialization for the concrete zero-aware QR run. -/
theorem householderQRRhsBackwardBound_le_growthCoeff_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    householderQRRhsBackwardBound fp n A b ≤
      householderQRRhsGrowthCoeff fp n * infNormVec b := by
  exact householderQRRhsBackwardBound_le_growthCoeff fp n A b hvalid
    (HouseholderQRPanelReady_square_of_global_gammaValid fp n A hvalid)

/-- Implementation-backed recursive backward-error theorem for the zero-aware
    concrete Householder QR right-hand-side transform. -/
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
      simpa [fl_householderQRPanel_rhs,
        householderQRRhsPanelBackwardBound] using
        householder_qr_rhs_panel_backward_zero_rows p A b
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A b _hready
          simpa [fl_householderQRPanel_rhs,
            householderQRRhsPanelBackwardBound] using
            householder_qr_rhs_panel_backward_zero_cols m A b
      | succ p =>
          intro A b hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
            have hTailRaw :=
              ih p (trailingPanel A) (vectorTail b) htailReady
            have hβ :
                0 ≤ householderQRRhsPanelBackwardBound fp m p
                  (trailingPanel A) (vectorTail b) :=
              householderQRRhsPanelBackwardBound_nonneg fp m p
                (trailingPanel A) (vectorTail b) htailReady
            have hSkip :=
              householder_qr_rhs_panel_backward_skip_zero_column A b
                (fl_householderQRPanel_rhs fp m p
                  (trailingPanel A) (vectorTail b))
                (householderQRRhsPanelBackwardBound fp m p
                  (trailingPanel A) (vectorTail b))
                hcol hTailRaw hβ
            simpa [fl_householderQRPanel_rhs,
              householderQRRhsPanelBackwardBound, hcol] using hSkip
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
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
                  hcol hready'.1
              simpa [P, bstep, cstep, Nat.cast_add, Nat.cast_one] using hraw
            have hPorth : IsOrthogonal (m + 1) P := by
              have hstep :=
                fl_householder_first_column_rhs_step_error fp A b
                  hcol hready'.1
              simpa [P] using hstep.orth
            have hTail :
                HouseholderQRRhsPanelBackwardError m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                  (fl_householderQRPanel_rhs fp m p
                    (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                  (householderQRRhsPanelBackwardBound fp m p
                    (fl_householderTrailingPanelStep fp A) (vectorTail bstep)) :=
              ih p (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hready'.2
            have hcstep : 0 ≤ cstep := by
              have hc :
                  0 ≤ householderConstructApplyBound fp (m + 1) :=
                householderConstructApplyBound_nonneg fp (m + 1) hready'.1
              exact mul_nonneg
                (mul_nonneg (by positivity) hc)
                (infNormVec_nonneg b)
            have htailNonneg :
                0 ≤ householderQRRhsPanelBackwardBound fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep) :=
              householderQRRhsPanelBackwardBound_nonneg fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hready'.2
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
              householderQRRhsPanelBackwardBound, hcol, P, bstep, cstep,
              fl_householderTrailingPanelStep, Nat.cast_add, Nat.cast_one]
              using hCons

/-- Square specialization of the zero-aware implementation-backed
    RHS-transform theorem. -/
theorem fl_householderQR_rhs_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp n n A) :
    HouseholderQRRhsPanelBackwardError n n A b
      (fl_householderQR_rhs fp n A b)
      (householderQRRhsBackwardBound fp n A b) := by
  simpa [fl_householderQR_rhs, householderQRRhsBackwardBound] using
    fl_householderQRPanel_rhs_backward_error fp n n A b hready

/-- Implementation-backed recursive backward-error theorem for the zero-aware
    concrete Householder QR RHS transform with the exact `Q` witness
    fixed.

    This is the RHS-side bridge needed for fixed-witness QR solve component
    theorems: the same `fl_householderQRPanel_Q` recursion that explains
    `R` also explains the rounded right-hand-side transform. -/
theorem fl_householderQRPanel_rhs_explicit_backward_error
    (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ),
      HouseholderQRPanelReady fp m p A →
      HouseholderQRRhsPanelExplicitBackwardError m p A b
        (fl_householderQRPanel_Q fp m p A)
        (fl_householderQRPanel_rhs fp m p A b)
        (householderQRRhsPanelBackwardBound fp m p A b) := by
  intro m
  induction m with
  | zero =>
      intro p A b _hready
      simpa [fl_householderQRPanel_Q, fl_householderQRPanel_rhs,
        householderQRRhsPanelBackwardBound] using
        householder_qr_rhs_panel_explicit_backward_zero_rows p A b
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A b _hready
          simpa [fl_householderQRPanel_Q, fl_householderQRPanel_rhs,
            householderQRRhsPanelBackwardBound] using
            householder_qr_rhs_panel_explicit_backward_zero_cols m A b
      | succ p =>
          intro A b hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
            have hTailRaw :=
              ih p (trailingPanel A) (vectorTail b) htailReady
            have hβ :
                0 ≤ householderQRRhsPanelBackwardBound fp m p
                  (trailingPanel A) (vectorTail b) :=
              householderQRRhsPanelBackwardBound_nonneg fp m p
                (trailingPanel A) (vectorTail b) htailReady
            have hSkip :=
              householder_qr_rhs_panel_explicit_backward_skip_zero_column A b
                (fl_householderQRPanel_Q fp m p (trailingPanel A))
                (fl_householderQRPanel_rhs fp m p
                  (trailingPanel A) (vectorTail b))
                (householderQRRhsPanelBackwardBound fp m p
                  (trailingPanel A) (vectorTail b))
                hcol hTailRaw hβ
            simpa [fl_householderQRPanel_Q,
              fl_householderQRPanel_rhs,
              householderQRRhsPanelBackwardBound, hcol] using hSkip
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
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
                  hcol hready'.1
              simpa [P, bstep, cstep, Nat.cast_add, Nat.cast_one] using hraw
            have hPorth : IsOrthogonal (m + 1) P := by
              have hstep :=
                fl_householder_first_column_rhs_step_error fp A b
                  hcol hready'.1
              simpa [P] using hstep.orth
            have hTail :
                HouseholderQRRhsPanelExplicitBackwardError m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                  (fl_householderQRPanel_Q fp m p
                    (fl_householderTrailingPanelStep fp A))
                  (fl_householderQRPanel_rhs fp m p
                    (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                  (householderQRRhsPanelBackwardBound fp m p
                    (fl_householderTrailingPanelStep fp A) (vectorTail bstep)) :=
              ih p (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hready'.2
            have hcstep : 0 ≤ cstep := by
              have hc :
                  0 ≤ householderConstructApplyBound fp (m + 1) :=
                householderConstructApplyBound_nonneg fp (m + 1) hready'.1
              exact mul_nonneg
                (mul_nonneg (by positivity) hc)
                (infNormVec_nonneg b)
            have htailNonneg :
                0 ≤ householderQRRhsPanelBackwardBound fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep) :=
              householderQRRhsPanelBackwardBound_nonneg fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hready'.2
            have hCons :=
              householder_qr_rhs_panel_explicit_backward_cons A
                (fl_householderTrailingPanelStep fp A) P
                (fl_householderQRPanel_Q fp m p
                  (fl_householderTrailingPanelStep fp A))
                b bstep e
                (fl_householderQRPanel_rhs fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                cstep
                (householderQRRhsPanelBackwardBound fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                hPorth hy he hTail hcstep htailNonneg
            simpa [fl_householderQRPanel_Q,
              fl_householderQRPanel_rhs,
              householderQRRhsPanelBackwardBound, hcol, P, bstep, cstep,
              fl_householderTrailingPanelStep, Nat.cast_add, Nat.cast_one]
              using hCons

/-- Square specialization of the explicit fixed-`Q` RHS theorem. -/
theorem fl_householderQR_rhs_explicit_backward_error
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp n n A) :
    HouseholderQRRhsPanelExplicitBackwardError n n A b
      (fl_householderQR_Q fp n A)
      (fl_householderQR_rhs fp n A b)
      (householderQRRhsBackwardBound fp n A b) := by
  simpa [fl_householderQR_Q, fl_householderQR_rhs,
    householderQRRhsBackwardBound] using
    fl_householderQRPanel_rhs_explicit_backward_error fp n n A b hready

/-- Global-gamma wrapper for the explicit fixed-`Q` RHS theorem. -/
theorem fl_householderQR_rhs_explicit_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRRhsPanelExplicitBackwardError n n A b
      (fl_householderQR_Q fp n A)
      (fl_householderQR_rhs fp n A b)
      (householderQRRhsBackwardBound fp n A b) := by
  exact fl_householderQR_rhs_explicit_backward_error fp n A b
    (HouseholderQRPanelReady_square_of_global_gammaValid fp n A hvalid)

/-- Global-gamma wrapper for the zero-aware implementation-backed RHS-transform
    theorem. -/
theorem fl_householderQR_rhs_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRRhsPanelBackwardError n n A b
      (fl_householderQR_rhs fp n A b)
      (householderQRRhsBackwardBound fp n A b) := by
  exact fl_householderQR_rhs_backward_error fp n A b
    (HouseholderQRPanelReady_square_of_global_gammaValid fp n A hvalid)

/-- Implementation-backed simultaneous backward-error theorem for the
    zero-aware concrete Householder QR `R` panel and RHS transform. -/
theorem fl_householderQRPanel_solve_components_backward_error
    (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ),
      HouseholderQRPanelReady fp m p A →
      HouseholderQRPanelSolveBackwardError m p A
        (fl_householderQRPanel_R fp m p A)
        b (fl_householderQRPanel_rhs fp m p A b)
        (householderQRPanelBackwardCoeff fp m p A * frobNorm A)
        (householderQRRhsPanelBackwardBound fp m p A b) := by
  intro m
  induction m with
  | zero =>
      intro p A b _hready
      simpa [fl_householderQRPanel_R, fl_householderQRPanel_rhs,
        householderQRPanelBackwardCoeff,
        householderQRRhsPanelBackwardBound] using
        householder_qr_panel_solve_backward_zero_rows p A b
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A b _hready
          simpa [fl_householderQRPanel_R, fl_householderQRPanel_rhs,
            householderQRPanelBackwardCoeff,
            householderQRRhsPanelBackwardBound] using
            householder_qr_panel_solve_backward_zero_cols m A b
      | succ p =>
          intro A b hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · have htailReady :
                HouseholderQRPanelReady fp m p (trailingPanel A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
            have hTailRaw :=
              ih p (trailingPanel A) (vectorTail b) htailReady
            have hα :
                0 ≤ householderQRPanelBackwardCoeff fp m p
                  (trailingPanel A) :=
              householderQRPanelBackwardCoeff_nonneg fp m p
                (trailingPanel A) htailReady
            have hβ :
                0 ≤ householderQRRhsPanelBackwardBound fp m p
                  (trailingPanel A) (vectorTail b) :=
              householderQRRhsPanelBackwardBound_nonneg fp m p
                (trailingPanel A) (vectorTail b) htailReady
            have hSkip :=
              householder_qr_panel_solve_backward_skip_zero_column A
                (fl_householderQRPanel_R fp m p (trailingPanel A))
                b
                (fl_householderQRPanel_rhs fp m p
                  (trailingPanel A) (vectorTail b))
                (householderQRPanelBackwardCoeff fp m p
                  (trailingPanel A))
                (householderQRRhsPanelBackwardBound fp m p
                  (trailingPanel A) (vectorTail b))
                hcol hTailRaw hα hβ
            simpa [fl_householderQRPanel_R, fl_householderQRPanel_rhs,
              householderQRPanelBackwardCoeff,
              householderQRRhsPanelBackwardBound, hcol] using hSkip
          · have hready' :
                gammaValid fp (11 * (m + 1) + 23) ∧
                HouseholderQRPanelReady fp m p
                  (fl_householderTrailingPanelStep fp A) := by
              simpa [HouseholderQRPanelReady, hcol] using hready
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
            let bstep : Fin (m + 1) → ℝ :=
              fl_householderApply fp (m + 1)
                (fl_householderNormalizedVector fp (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A)) 1 b
            let cstep_rhs : ℝ :=
              (m + 1 : ℝ) * householderConstructApplyBound fp (m + 1) *
                infNormVec b
            obtain ⟨E, hSrep, hE, hSzero⟩ :=
              fl_householder_first_column_panel_stored_residual_and_shape fp A
                hcol hready'.1
            obtain ⟨e, hy, he⟩ := by
              have hraw :=
                fl_householder_first_column_rhs_step_residual_bound fp A b
                  hcol hready'.1
              simpa [P, bstep, cstep_rhs, Nat.cast_add, Nat.cast_one] using hraw
            have hPorth : IsOrthogonal (m + 1) P := by
              have hstep :=
                fl_householder_first_column_rhs_step_error fp A b
                  hcol hready'.1
              simpa [P] using hstep.orth
            have hStrailing :
                trailingPanel S = fl_householderTrailingPanelStep fp A := by
              simp [S, Ahat, fl_householderTrailingPanelStep]
            have hTailRaw :=
              ih p (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hready'.2
            have hTail :
                HouseholderQRPanelSolveBackwardError m p
                  (trailingPanel S)
                  (fl_householderQRPanel_R fp m p
                    (fl_householderTrailingPanelStep fp A))
                  (vectorTail bstep)
                  (fl_householderQRPanel_rhs fp m p
                    (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                  (householderQRPanelBackwardCoeff fp m p
                    (fl_householderTrailingPanelStep fp A) *
                    frobNorm (trailingPanel S))
                  (householderQRRhsPanelBackwardBound fp m p
                    (fl_householderTrailingPanelStep fp A) (vectorTail bstep)) := by
              rw [hStrailing]
              exact hTailRaw
            have hα :
                0 ≤ householderQRPanelBackwardCoeff fp m p
                  (fl_householderTrailingPanelStep fp A) :=
              householderQRPanelBackwardCoeff_nonneg fp m p
                (fl_householderTrailingPanelStep fp A) hready'.2
            have hcstep_rhs : 0 ≤ cstep_rhs := by
              have hc :
                  0 ≤ householderConstructApplyBound fp (m + 1) :=
                householderConstructApplyBound_nonneg fp (m + 1) hready'.1
              exact mul_nonneg
                (mul_nonneg (by positivity) hc)
                (infNormVec_nonneg b)
            have hβ :
                0 ≤ householderQRRhsPanelBackwardBound fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep) :=
              householderQRRhsPanelBackwardBound_nonneg fp m p
                (fl_householderTrailingPanelStep fp A) (vectorTail bstep)
                hready'.2
            have hCons :=
              householder_qr_panel_solve_backward_cons A S P E
                (fl_householderQRPanel_R fp m p
                  (fl_householderTrailingPanelStep fp A))
                b bstep e
                (fl_householderQRPanel_rhs fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                (householderConstructApplyBound fp (m + 1))
                (householderQRPanelBackwardCoeff fp m p
                  (fl_householderTrailingPanelStep fp A))
                cstep_rhs
                (householderQRRhsPanelBackwardBound fp m p
                  (fl_householderTrailingPanelStep fp A) (vectorTail bstep))
                hPorth hSrep hE hSzero hy he hTail hα hcstep_rhs hβ
            simpa [fl_householderQRPanel_R, fl_householderQRPanel_rhs,
              householderQRPanelBackwardCoeff,
              householderQRRhsPanelBackwardBound, hcol,
              S, Ahat, P, bstep, cstep_rhs, fl_householderTrailingPanelStep,
              Nat.cast_add, Nat.cast_one] using hCons

/-- Square specialization of the zero-aware simultaneous concrete QR/RHS
    component theorem. -/
theorem fl_householderQR_solve_components_backward_error (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp n n A) :
    HouseholderQRPanelSolveBackwardError n n A
      (fl_householderQR_R fp n A)
      b (fl_householderQR_rhs fp n A b)
      (householderQRBackwardCoeff fp n A * frobNorm A)
      (householderQRRhsBackwardBound fp n A b) := by
  simpa [fl_householderQR_R, fl_householderQR_rhs,
    householderQRBackwardCoeff, householderQRRhsBackwardBound] using
    fl_householderQRPanel_solve_components_backward_error fp n n A b hready

/-- Global-gamma wrapper for the zero-aware simultaneous concrete QR/RHS
    component theorem. -/
theorem fl_householderQR_solve_components_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelSolveBackwardError n n A
      (fl_householderQR_R fp n A)
      b (fl_householderQR_rhs fp n A b)
      (householderQRBackwardCoeff fp n A * frobNorm A)
      (householderQRRhsBackwardBound fp n A b) := by
  exact fl_householderQR_solve_components_backward_error fp n A b
    (HouseholderQRPanelReady_square_of_global_gammaValid fp n A hvalid)

/-- Implementation-backed simultaneous backward-error theorem for the
    zero-aware concrete Householder QR `R` panel and RHS transform with the
    exact `Q` witness fixed.

    This packages the explicit `R` theorem from `HouseholderQR.lean` and
    the explicit RHS theorem above.  It strengthens
    `fl_householderQRPanel_solve_components_backward_error` by naming the
    concrete exact orthogonal factor generated by the same zero-aware QR recursion. -/
theorem fl_householderQRPanel_solve_components_fixed_Q_backward_error
    (fp : FPModel) (m p : ℕ)
    (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ)
    (hready : HouseholderQRPanelReady fp m p A) :
    HouseholderQRPanelSolveFixedBackwardError m p A
      (fl_householderQRPanel_R fp m p A)
      b (fl_householderQRPanel_rhs fp m p A b)
      (fl_householderQRPanel_Q fp m p A)
      (householderQRPanelBackwardCoeff fp m p A * frobNorm A)
      (householderQRRhsPanelBackwardBound fp m p A b) := by
  have hR :=
    fl_householderQRPanel_R_explicit_backward_error fp m p A hready
  have hb :=
    fl_householderQRPanel_rhs_explicit_backward_error fp m p A b hready
  exact HouseholderQRPanelSolveFixedBackwardError.of_explicit_components hR hb

/-- Square specialization of the fixed-`Q` simultaneous concrete QR/RHS
    component theorem. -/
theorem fl_householderQR_solve_components_fixed_Q_backward_error
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp n n A) :
    HouseholderQRPanelSolveFixedBackwardError n n A
      (fl_householderQR_R fp n A)
      b (fl_householderQR_rhs fp n A b)
      (fl_householderQR_Q fp n A)
      (householderQRBackwardCoeff fp n A * frobNorm A)
      (householderQRRhsBackwardBound fp n A b) := by
  simpa [fl_householderQR_R, fl_householderQR_rhs,
    fl_householderQR_Q, householderQRBackwardCoeff,
    householderQRRhsBackwardBound] using
    fl_householderQRPanel_solve_components_fixed_Q_backward_error
      fp n n A b hready

/-- Global-gamma wrapper for the fixed-`Q` simultaneous concrete QR/RHS
    component theorem. -/
theorem fl_householderQR_solve_components_fixed_Q_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderQRPanelSolveFixedBackwardError n n A
      (fl_householderQR_R fp n A)
      b (fl_householderQR_rhs fp n A b)
      (fl_householderQR_Q fp n A)
      (householderQRBackwardCoeff fp n A * frobNorm A)
      (householderQRRhsBackwardBound fp n A b) := by
  exact fl_householderQR_solve_components_fixed_Q_backward_error
    fp n A b
    (HouseholderQRPanelReady_square_of_global_gammaValid fp n A hvalid)

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
    `ΔA = ΔA₁ + Q ΔR` and matrix bound `c₁ + c₂`.  This remains a reusable
    component-level transfer theorem.  The concrete rounded solve paths are
    connected to it by `fl_householderQR_solve_backward_error` and
    `fl_householderQR_solve_backward_error`. -/
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

/-- Implementation-backed backward-error theorem for the zero-aware concrete
    Householder QR solve.

    This is the zero-aware theorem of `fl_householderQR_solve_backward_error`.
    The QR factorization and RHS-transform stages handle zero active columns by
    exact skip branches and analyze nonzero active columns through the concrete
    rounded Householder kernels.  The remaining solve-side assumptions are the
    standard back-substitution requirements: nonzero diagonal of the computed
    `R`, `0 < n`, and `gammaValid fp n`. -/
theorem fl_householderQR_solve_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hready : HouseholderQRPanelReady fp n n A)
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0)
    (hgamma : gammaValid fp n) :
    QRSolveBackwardError n A b (fl_householderQR_solve fp n A b)
      (householderQRBackwardCoeff fp n A * frobNorm A +
        gamma fp n * frobNorm (fl_householderQR_R fp n A))
      (householderQRRhsBackwardBound fp n A b) := by
  let R_hat : Fin n → Fin n → ℝ := fl_householderQR_R fp n A
  let c_hat : Fin n → ℝ := fl_householderQR_rhs fp n A b
  let Q : Fin n → Fin n → ℝ := fl_householderQR_Q fp n A
  have hComp :=
    fl_householderQR_solve_components_fixed_Q_backward_error
      fp n A b hready
  obtain ⟨ΔA₁, Δb, hR, hQb, hΔA₁, hΔb⟩ := hComp.result
  have hQ : IsOrthogonal n Q := hComp.orth
  have hQR : ∀ i j, matMul n Q R_hat i j = A i j + ΔA₁ i j := by
    intro i j
    have hRmat :
        R_hat = matMul n (matTranspose Q)
          (fun r col => A r col + ΔA₁ r col) := by
      ext r col
      simpa [R_hat, matMul, matMulRect] using hR r col
    have hQQT : matMul n Q (matTranspose Q) = idMatrix n := by
      ext r col
      exact hQ.right_inv r col
    rw [hRmat, ← matMul_assoc, hQQT, matMul_id_left]
  have hUT : ∀ i j : Fin n, j.val < i.val → R_hat i j = 0 := by
    simpa [R_hat, IsUpperTriangular] using
      fl_householderQR_R_upper fp n A
  obtain ⟨ΔR, hΔRentry, hBack⟩ :=
    backSub_backward_error fp n R_hat c_hat
      (by simpa [R_hat] using hdiag) hUT hgamma
  have hSolve : ∀ i,
      matMulVec n (fun r col => R_hat r col + ΔR r col)
        (fl_householderQR_solve fp n A b) i = c_hat i := by
    intro i
    unfold matMulVec
    simpa [R_hat, c_hat, fl_householderQR_solve] using hBack i
  have hΔR :
      frobNorm ΔR ≤ gamma fp n * frobNorm R_hat :=
    frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le ΔR R_hat
      (gamma_nonneg fp hgamma) hΔRentry
  have hc₁ :
      0 ≤ householderQRBackwardCoeff fp n A * frobNorm A := by
    have hcoeff : 0 ≤ householderQRBackwardCoeff fp n A := by
      simpa [householderQRBackwardCoeff] using
        householderQRPanelBackwardCoeff_nonneg fp n n A hready
    exact mul_nonneg hcoeff (frobNorm_nonneg A)
  have hc₂ :
      0 ≤ gamma fp n * frobNorm R_hat :=
    mul_nonneg (gamma_nonneg fp hgamma) (frobNorm_nonneg R_hat)
  exact qr_solve_backward_error_from_components n hn A Q R_hat ΔA₁
    hQ hQR hΔA₁
    (fl_householderQR_solve fp n A b) c_hat ΔR hSolve hΔR
    b Δb hQb hΔb hc₁ hc₂

/-- Global-gamma wrapper for the implementation-backed zero-aware concrete
    Householder QR solve theorem.

    The single `gammaValid fp (11*n+23)` assumption supplies the QR reflector
    construction/application gamma conditions and the smaller back-substitution
    `gammaValid fp n` condition.  The nonzero diagonal hypothesis remains
    explicit because it is the mathematical side condition for the triangular
    solve stage. -/
theorem fl_householderQR_solve_backward_error_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp (11 * n + 23))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0) :
    QRSolveBackwardError n A b (fl_householderQR_solve fp n A b)
      (householderQRBackwardCoeff fp n A * frobNorm A +
        gamma fp n * frobNorm (fl_householderQR_R fp n A))
      (householderQRRhsBackwardBound fp n A b) := by
  have hready :
      HouseholderQRPanelReady fp n n A :=
    HouseholderQRPanelReady_square_of_global_gammaValid fp n A hvalid
  have hgamma : gammaValid fp n :=
    gammaValid_mono fp (by omega) hvalid
  exact fl_householderQR_solve_backward_error fp n A b
    hn hready hdiag hgamma

/-- Implementation-backed zero-aware Householder QR solve theorem with the QR
    factorization part absorbed into the same single Higham-style `gamma` term
    used by the Householder QR factorization theorem.

    The final solve bound still contains the separate backward-substitution
    contribution `gamma n * ‖R‖_F`, because that is the triangular solve
    stage, not the QR factorization stage. -/
theorem fl_householderQR_solve_backward_error_gammaHigham_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0) :
    QRSolveBackwardError n A b (fl_householderQR_solve fp n A b)
      ((gamma fp (n * householderConstructApplyGammaIndex n) * frobNorm A) +
        gamma fp n * frobNorm (fl_householderQR_R fp n A))
      (householderQRRhsBackwardBound fp n A b) := by
  let K := householderConstructApplyGammaIndex n
  have hK_le_nK : K ≤ n * K := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right K hn1
  have hbase_le_K : 11 * n + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hbase_valid : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK) hvalid
  have hraw :=
    fl_householderQR_solve_backward_error_of_global_gammaValid
      fp n A b hn hbase_valid hdiag
  refine hraw.mono ?_ le_rfl
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (householderQRBackwardCoeff_le_gamma_higham fp n A hn hvalid)
      (frobNorm_nonneg A))
    le_rfl

/-- Source-facing implementation-backed zero-aware Householder QR solve theorem
    with both the QR-factorization bound and the RHS-transform bound presented
    by dimension-only coefficients.

    Compared with
    `fl_householderQR_solve_backward_error_gammaHigham_of_global_gammaValid`,
    this theorem replaces the raw recursive RHS perturbation expression by
    `householderQRRhsGrowthCoeff fp n * ‖b‖∞`.  The RHS coefficient is still
    derived from the concrete rounded RHS recursion; it is not an assumed
    contract. -/
theorem fl_householderQR_solve_backward_error_gammaHigham_rhsGrowth_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0) :
    QRSolveBackwardError n A b (fl_householderQR_solve fp n A b)
      ((gamma fp (n * householderConstructApplyGammaIndex n) * frobNorm A) +
        gamma fp n * frobNorm (fl_householderQR_R fp n A))
      (householderQRRhsGrowthCoeff fp n * infNormVec b) := by
  let K := householderConstructApplyGammaIndex n
  have hK_le_nK : K ≤ n * K := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right K hn1
  have hbase_le_K : 11 * n + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hbase_valid : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK) hvalid
  have hraw :=
    fl_householderQR_solve_backward_error_gammaHigham_of_global_gammaValid
      fp n A b hn hvalid hdiag
  refine hraw.mono le_rfl ?_
  exact householderQRRhsBackwardBound_le_growthCoeff_of_global_gammaValid
    fp n A b hbase_valid

/-- Source-facing implementation-backed zero-aware Householder QR solve theorem
    with a nonrecursive closed growth expression for the RHS perturbation
    bound.

    The RHS expression is conservative and locally derived from
    `householderQRRhsGrowthCoeff_le_closedGrowth`; it should be read as a
    convenient citation bound rather than Higham's sharp hidden constant. -/
theorem fl_householderQR_solve_backward_error_gammaHigham_rhsClosedGrowth_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0) :
    QRSolveBackwardError n A b (fl_householderQR_solve fp n A b)
      ((gamma fp (n * householderConstructApplyGammaIndex n) * frobNorm A) +
        gamma fp n * frobNorm (fl_householderQR_R fp n A))
      (((n : ℝ) * ((n : ℝ) ^ 2 * householderConstructApplyBound fp n) *
          (1 + (n : ℝ) ^ 2 *
            (1 + householderConstructApplyBound fp n)) ^ n) *
        infNormVec b) := by
  let K := householderConstructApplyGammaIndex n
  have hK_le_nK : K ≤ n * K := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right K hn1
  have hbase_le_K : 11 * n + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hbase_valid : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK) hvalid
  have hraw :=
    fl_householderQR_solve_backward_error_gammaHigham_rhsGrowth_of_global_gammaValid
      fp n A b hn hvalid hdiag
  refine hraw.mono le_rfl ?_
  exact mul_le_mul_of_nonneg_right
    (householderQRRhsGrowthCoeff_le_closedGrowth fp n hbase_valid)
    (infNormVec_nonneg b)

/-- Source-facing implementation-backed zero-aware Householder QR solve theorem
    with both solve-side printed bounds depending only on the original inputs.

    Compared with
    `fl_householderQR_solve_backward_error_gammaHigham_rhsClosedGrowth_of_global_gammaValid`,
    this theorem also removes the intermediate `‖R‖_F` from the matrix
    perturbation bound, using the explicit QR backward-error theorem to prove
    `‖R‖_F ≤ (1 + gamma_K) ‖A‖_F`.  The back-substitution contribution is
    still kept visibly separate in the coefficient
    `gamma_n * (1 + gamma_K)`. -/
theorem fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid
    (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0) :
    QRSolveBackwardError n A b (fl_householderQR_solve fp n A b)
      ((gamma fp (n * householderConstructApplyGammaIndex n) +
          gamma fp n *
            (1 + gamma fp (n * householderConstructApplyGammaIndex n))) *
        frobNorm A)
      (((n : ℝ) * ((n : ℝ) ^ 2 * householderConstructApplyBound fp n) *
          (1 + (n : ℝ) ^ 2 *
            (1 + householderConstructApplyBound fp n)) ^ n) *
        infNormVec b) := by
  let K := householderConstructApplyGammaIndex n
  let G : ℝ := gamma fp (n * K)
  let gn : ℝ := gamma fp n
  have hK_le_nK : K ≤ n * K := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right K hn1
  have hbase_le_K : 11 * n + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hbase_valid : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK) hvalid
  have hn_valid : gammaValid fp n :=
    gammaValid_mono fp (by omega) hbase_valid
  have hraw :=
    fl_householderQR_solve_backward_error_gammaHigham_rhsClosedGrowth_of_global_gammaValid
      fp n A b hn hvalid hdiag
  refine hraw.mono ?_ le_rfl
  have hR :
      frobNorm (fl_householderQR_R fp n A) ≤ (1 + G) * frobNorm A := by
    simpa [G, K] using
      fl_householderQR_R_frobNorm_le_gammaHigham_of_global_gammaValid
        fp n A hn hvalid
  have htri :
      gn * frobNorm (fl_householderQR_R fp n A) ≤
        gn * ((1 + G) * frobNorm A) := by
    exact mul_le_mul_of_nonneg_left hR (by
      simpa [gn] using gamma_nonneg fp hn_valid)
  calc
    (gamma fp (n * householderConstructApplyGammaIndex n) * frobNorm A) +
        gamma fp n * frobNorm (fl_householderQR_R fp n A)
        ≤ G * frobNorm A + gn * ((1 + G) * frobNorm A) := by
            simpa [G, gn, K] using add_le_add_left htri (G * frobNorm A)
    _ = (G + gn * (1 + G)) * frobNorm A := by ring
    _ = (gamma fp (n * householderConstructApplyGammaIndex n) +
          gamma fp n *
            (1 + gamma fp (n * householderConstructApplyGammaIndex n))) *
        frobNorm A := by
        simp [G, gn, K]

end LeanFpAnalysis.FP
