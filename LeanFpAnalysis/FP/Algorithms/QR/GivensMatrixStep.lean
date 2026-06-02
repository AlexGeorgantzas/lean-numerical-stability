-- Algorithms/QR/GivensMatrixStep.lean
--
-- Matrix-column bridge for concrete Givens rotation application.

import LeanFpAnalysis.FP.Algorithms.QR.GivensSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

/-- Apply one computed Givens rotation to every column of a square matrix.

    The coefficients are computed once from the supplied two-vector
    `(xi,xj)` by `fl_givensC`/`fl_givensS`, and each output column is then
    computed by the rounded vector kernel `fl_givensApply`. -/
noncomputable def fl_givensApplyMatrix (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    fl_givensApply fp n p q
      (fl_givensC fp xi xj) (fl_givensS fp xi xj) (fun k => A k j) i

/-- Apply one computed Givens rotation to every column of an `m × cols`
    rectangular panel. -/
noncomputable def fl_givensApplyMatrixRect (fp : FPModel) (m cols : ℕ)
    (p q : Fin m) (xi xj : ℝ) (A : Fin m → Fin cols → ℝ) :
    Fin m → Fin cols → ℝ :=
  fun i j =>
    fl_givensApply fp m p q
      (fl_givensC fp xi xj) (fl_givensS fp xi xj) (fun k => A k j) i

/-- Columnwise matrix-step form for one Givens rotation.

    Each output column is represented as `(G + ΔG_j) A[:,j]`; the perturbation
    is column-dependent because each vector application performs separate
    rounded operations. -/
structure ColumnwiseGivensStepError (n : ℕ)
    (G : Fin n → Fin n → ℝ) (A A_hat : Fin n → Fin n → ℝ)
    (c : ℝ) : Prop where
  /-- The exact Givens rotation is orthogonal. -/
  orth : IsOrthogonal n G
  /-- Every computed output column has a column-dependent perturbation. -/
  pert : ∀ j : Fin n, ∃ ΔGj : Fin n → Fin n → ℝ,
    frobNorm ΔGj ≤ c ∧
    ∀ i : Fin n, A_hat i j =
      matMulVec n (fun a b => G a b + ΔGj a b) (fun k => A k j) i

/-- Rectangular panel form of `ColumnwiseGivensStepError`. -/
structure ColumnwiseGivensStepErrorRect (m cols : ℕ)
    (G : Fin m → Fin m → ℝ) (A A_hat : Fin m → Fin cols → ℝ)
    (c : ℝ) : Prop where
  /-- The exact Givens rotation is orthogonal. -/
  orth : IsOrthogonal m G
  /-- Every computed output column has a column-dependent perturbation. -/
  pert : ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
    frobNorm ΔGj ≤ c ∧
    ∀ i : Fin m, A_hat i j =
      matMulVec m (fun a b => G a b + ΔGj a b) (fun k => A k j) i

/-- Package per-column `GivensAppError` facts as a square matrix-step error. -/
theorem columnwiseGivensStepError_of_appError (n : ℕ)
    (G : Fin n → Fin n → ℝ) (A A_hat : Fin n → Fin n → ℝ) (c : ℝ)
    (hG : IsOrthogonal n G)
    (hcols : ∀ j : Fin n,
      GivensAppError n G (fun i => A i j) (fun i => A_hat i j) c) :
    ColumnwiseGivensStepError n G A A_hat c := by
  refine ⟨hG, ?_⟩
  intro j
  exact (hcols j).pert

/-- Package per-column `GivensAppError` facts as a rectangular panel-step
    error. -/
theorem columnwiseGivensStepErrorRect_of_appError (m cols : ℕ)
    (G : Fin m → Fin m → ℝ) (A A_hat : Fin m → Fin cols → ℝ) (c : ℝ)
    (hG : IsOrthogonal m G)
    (hcols : ∀ j : Fin cols,
      GivensAppError m G (fun i => A i j) (fun i => A_hat i j) c) :
    ColumnwiseGivensStepErrorRect m cols G A A_hat c := by
  refine ⟨hG, ?_⟩
  intro j
  exact (hcols j).pert

/-- Concrete computed-coefficient Givens application satisfies the square
    columnwise matrix-step contract. -/
theorem fl_givensApply_computed_matrix_step_error (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (A : Fin n → Fin n → ℝ)
    (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    ColumnwiseGivensStepError n
      (givensRotation n p q (givensC xi xj) (givensS xi xj))
      A
      (fl_givensApplyMatrix fp n p q xi xj A)
      (gamma fp 8 *
        frobNorm (givensRotation n p q (givensC xi xj) (givensS xi xj))) := by
  let G := givensRotation n p q (givensC xi xj) (givensS xi xj)
  have hG : IsOrthogonal n G := by
    simpa [G] using givensRotation_constructed_orthogonal n p q xi xj hpq h
  apply columnwiseGivensStepError_of_appError n G
  · exact hG
  · intro j
    simpa [G, fl_givensApplyMatrix] using
      fl_givensApply_computed_app_error_conservative fp n p q xi xj
        (fun k => A k j) hpq h hvalid

/-- Concrete computed-coefficient Givens application satisfies the rectangular
    columnwise matrix-step contract. -/
theorem fl_givensApply_computed_matrix_step_error_rect (fp : FPModel)
    (m cols : ℕ)
    (p q : Fin m) (xi xj : ℝ) (A : Fin m → Fin cols → ℝ)
    (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    ColumnwiseGivensStepErrorRect m cols
      (givensRotation m p q (givensC xi xj) (givensS xi xj))
      A
      (fl_givensApplyMatrixRect fp m cols p q xi xj A)
      (gamma fp 8 *
        frobNorm (givensRotation m p q (givensC xi xj) (givensS xi xj))) := by
  let G := givensRotation m p q (givensC xi xj) (givensS xi xj)
  have hG : IsOrthogonal m G := by
    simpa [G] using givensRotation_constructed_orthogonal m p q xi xj hpq h
  apply columnwiseGivensStepErrorRect_of_appError m cols G
  · exact hG
  · intro j
    simpa [G, fl_givensApplyMatrixRect] using
      fl_givensApply_computed_app_error_conservative fp m p q xi xj
        (fun k => A k j) hpq h hvalid

/-- Residual form of a square columnwise Givens matrix step. -/
theorem ColumnwiseGivensStepError.column_residual {n : ℕ}
    {G A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepError n G A A_hat c) :
    ∀ j : Fin n, ∃ ΔGj : Fin n → Fin n → ℝ,
      frobNorm ΔGj ≤ c ∧
      ∀ i : Fin n, A_hat i j =
        matMul n G A i j +
          matMulVec n ΔGj (fun k => A k j) i := by
  intro j
  obtain ⟨ΔGj, hΔGj, hcol⟩ := hstep.pert j
  refine ⟨ΔGj, hΔGj, ?_⟩
  intro i
  rw [hcol i]
  unfold matMulVec matMul
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix residual form of a square columnwise Givens step. -/
theorem ColumnwiseGivensStepError.exists_residual_matrix {n : ℕ}
    {G A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepError n G A A_hat c) :
    ∃ E : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, A_hat i j = matMul n G A i j + E i j) ∧
      ∀ j : Fin n, ∃ ΔGj : Fin n → Fin n → ℝ,
        frobNorm ΔGj ≤ c ∧
        ∀ i : Fin n, E i j =
          matMulVec n ΔGj (fun k => A k j) i := by
  classical
  let hres := hstep.column_residual
  let ΔG : Fin n → Fin n → Fin n → ℝ := fun j => Classical.choose (hres j)
  let E : Fin n → Fin n → ℝ :=
    fun i j => matMulVec n (ΔG j) (fun k => A k j) i
  refine ⟨E, ?_, ?_⟩
  · intro i j
    have hspec := Classical.choose_spec (hres j)
    exact hspec.2 i
  · intro j
    have hspec := Classical.choose_spec (hres j)
    refine ⟨ΔG j, hspec.1, ?_⟩
    intro i
    rfl

/-- Normwise residual consequence of a square columnwise Givens step. -/
theorem ColumnwiseGivensStepError.exists_residual_matrix_bound {n : ℕ}
    {G A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepError n G A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, A_hat i j = matMul n G A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A := by
  obtain ⟨E, hEA, hcol⟩ := hstep.exists_residual_matrix
  exact ⟨E, hEA, frobNorm_columnwise_matMulVec_le E A hc hcol⟩

/-- Residual form of a rectangular columnwise Givens panel step. -/
theorem ColumnwiseGivensStepErrorRect.column_residual {m cols : ℕ}
    {G : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepErrorRect m cols G A A_hat c) :
    ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
      frobNorm ΔGj ≤ c ∧
      ∀ i : Fin m, A_hat i j =
        matMulRect m m cols G A i j +
          matMulVec m ΔGj (fun k => A k j) i := by
  intro j
  obtain ⟨ΔGj, hΔGj, hcol⟩ := hstep.pert j
  refine ⟨ΔGj, hΔGj, ?_⟩
  intro i
  rw [hcol i]
  unfold matMulVec matMulRect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix residual form of a rectangular columnwise Givens panel step. -/
theorem ColumnwiseGivensStepErrorRect.exists_residual_matrix {m cols : ℕ}
    {G : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepErrorRect m cols G A A_hat c) :
    ∃ E : Fin m → Fin cols → ℝ,
      (∀ (i : Fin m) (j : Fin cols),
        A_hat i j = matMulRect m m cols G A i j + E i j) ∧
      ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
        frobNorm ΔGj ≤ c ∧
        ∀ i : Fin m, E i j =
          matMulVec m ΔGj (fun k => A k j) i := by
  classical
  let hres := hstep.column_residual
  let ΔG : Fin cols → Fin m → Fin m → ℝ := fun j => Classical.choose (hres j)
  let E : Fin m → Fin cols → ℝ :=
    fun i j => matMulVec m (ΔG j) (fun k => A k j) i
  refine ⟨E, ?_, ?_⟩
  · intro i j
    have hspec := Classical.choose_spec (hres j)
    exact hspec.2 i
  · intro j
    have hspec := Classical.choose_spec (hres j)
    refine ⟨ΔG j, hspec.1, ?_⟩
    intro i
    rfl

/-- Normwise residual consequence of a rectangular columnwise Givens step. -/
theorem ColumnwiseGivensStepErrorRect.exists_residual_matrix_bound
    {m cols : ℕ}
    {G : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepErrorRect m cols G A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin m → Fin cols → ℝ,
      (∀ (i : Fin m) (j : Fin cols),
        A_hat i j = matMulRect m m cols G A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A := by
  obtain ⟨E, hEA, hcol⟩ := hstep.exists_residual_matrix
  exact ⟨E, hEA, frobNorm_columnwise_matMulVec_le_rect E A hc hcol⟩

end LeanFpAnalysis.FP
