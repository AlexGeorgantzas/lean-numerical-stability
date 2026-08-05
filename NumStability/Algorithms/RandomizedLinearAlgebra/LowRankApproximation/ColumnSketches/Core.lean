import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.RankFactorizations.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.ColumnSketches.Core

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.LowRankApprox`; the historical path re-exports this module.
-/















/-!
# Low-rank approximation foundations for the RandNLA CACM formalization

This file begins the local foundation for the paper's low-rank approximation
claims, including the structural condition around equation (9).  It deliberately
separates exact analysis objects from implementation-facing floating-point
objects: sampling probabilities remain exact mathematical inputs by the current
project convention, while computed projectors/bases are handled in
`Preconditioning.lean` by explicit certificates.
-/

namespace NumStability

open scoped BigOperators



































































































































































































































































































































































































































































































































/-- Exact right Gram matrix `A^T A` for a rectangular real matrix.  This is an
analysis object.  Implementation-facing theorems must separately certify any
computed Gram entries. -/
noncomputable def rectRightGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k

/-- The exact right Gram matrix is symmetric. -/
theorem rectRightGram_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectRightGram A) := by
  intro j k
  unfold rectRightGram
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic form of `A^T A` is the squared norm of `A x`. -/
theorem finiteQuadraticForm_rectRightGram_eq_sum_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    finiteQuadraticForm (rectRightGram A) x =
      ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
  classical
  unfold finiteQuadraticForm finiteMatVec rectRightGram
  calc
    ∑ a : Fin n,
        x a *
          ∑ b : Fin n,
            (∑ i : Fin m, A i a * A i b) * x b
        =
          ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin m,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ b : Fin n, ∑ a : Fin n, ∑ i : Fin m,
            (A i a * x a) * (A i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ b : Fin n, ∑ i : Fin m, ∑ a : Fin n,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ b : Fin n, ∑ a : Fin n,
            (A i a * x a) * (A i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ a : Fin n, ∑ b : Fin n,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m,
            (∑ a : Fin n, A i a * x a) *
              (∑ b : Fin n, A i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ =
          ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- The exact right Gram matrix is positive semidefinite. -/
theorem rectRightGram_finitePSD {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    finitePSD (rectRightGram A) := by
  intro x
  rw [finiteQuadraticForm_rectRightGram_eq_sum_sq A x]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Mathlib positive-semidefinite form of `rectRightGram_finitePSD`. -/
theorem rectRightGram_matrix_posSemidef {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Matrix.PosSemidef ((rectRightGram A) : Matrix (Fin n) (Fin n) ℝ) :=
  finitePSD.to_matrix_posSemidef
    (rectRightGram A) (rectRightGram_symmetric A) (rectRightGram_finitePSD A)












/-- Exact singular-value squares, defined as the ordered zero-indexed Hermitian
eigenvalues of the exact right Gram `A^T A`.  This does not construct singular
vectors or an SVD. -/
noncomputable def rectSingularValueSq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => (rectRightGram_matrix_posSemidef A).1.eigenvalues₀
    (finCardIndex n j)

/-- Exact singular values, obtained by square-rooting the right-Gram
eigenvalues. -/
noncomputable def rectSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (rectSingularValueSq A j)

/-- The right-Gram singular-value squares are nonnegative. -/
theorem rectSingularValueSq_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectSingularValueSq A j := by
  let hpsd := rectRightGram_matrix_posSemidef A
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let j0 : Fin (Fintype.card (Fin n)) := finCardIndex n j
  have h := hpsd.eigenvalues_nonneg (e j0)
  change 0 ≤ hpsd.1.eigenvalues₀ (e.symm (e j0)) at h
  have hej : e.symm (e j0) = j0 := e.symm_apply_apply j0
  rw [hej] at h
  simpa [rectSingularValueSq, hpsd, j0] using h

/-- The right-Gram singular-value squares are ordered in the mathlib
zero-indexed Hermitian eigenvalue order. -/
theorem rectSingularValueSq_antitone {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Antitone (rectSingularValueSq A) := by
  intro i j hij
  let hpsd := rectRightGram_matrix_posSemidef A
  have hanti := hpsd.1.eigenvalues₀_antitone
  have hcast : finCardIndex n i ≤ finCardIndex n j :=
    finCardIndex_le hij
  exact hanti hcast

/-- Exact singular values are nonnegative. -/
theorem rectSingularValue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectSingularValue A j := by
  unfold rectSingularValue
  exact Real.sqrt_nonneg _

/-- Exact singular values inherit the Hermitian eigenvalue order from the
right-Gram singular-value squares. -/
theorem rectSingularValue_antitone {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Antitone (rectSingularValue A) := by
  intro i j hij
  unfold rectSingularValue
  exact Real.sqrt_le_sqrt (rectSingularValueSq_antitone A hij)

/-- Squaring the exact singular values recovers the right-Gram eigenvalues. -/
theorem rectSingularValue_sq_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    (rectSingularValue A j) ^ 2 = rectSingularValueSq A j := by
  unfold rectSingularValue
  exact Real.sq_sqrt (rectSingularValueSq_nonneg A j)

/-- Basis-indexed exact eigenvalues of the right Gram `A^T A`.  This index is
the one used by mathlib's Hermitian eigenvector basis; it is intentionally
separate from the ordered zero-indexed sequence `rectSingularValueSq`. -/
noncomputable def rectRightGramEigenvalue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => (rectRightGram_matrix_posSemidef A).1.eigenvalues j

/-- Exact right-Gram eigenvector table, represented as a real square matrix.
Its columns are the mathlib Hermitian eigenvectors of the exact analysis Gram
`A^T A`.  Implementation-facing theorems must separately certify any computed
singular-vector table. -/
noncomputable def rectRightGramEigenbasis {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ((Matrix.IsHermitian.eigenvectorUnitary
      (rectRightGram_matrix_posSemidef A).1 :
      Matrix (Fin n) (Fin n) ℝ) i j)

/-- Basis-indexed exact singular values attached to
`rectRightGramEigenbasis`. -/
noncomputable def rectRightGramBasisSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (rectRightGramEigenvalue A j)

/-- The right-Gram eigenvector table is orthogonal. -/
theorem rectRightGramEigenbasis_isOrthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsOrthogonal n (rectRightGramEigenbasis A) := by
  constructor
  · intro i j
    let U :=
      Matrix.IsHermitian.eigenvectorUnitary
        (rectRightGram_matrix_posSemidef A).1
    have h := Unitary.coe_star_mul_self U
    have hij := congr_fun (congr_fun h i) j
    simpa [rectRightGramEigenbasis, U, Matrix.mul_apply, Matrix.one_apply,
      matTranspose, idMatrix] using hij
  · intro i j
    let U :=
      Matrix.IsHermitian.eigenvectorUnitary
        (rectRightGram_matrix_posSemidef A).1
    have h := Unitary.coe_mul_star_self U
    have hij := congr_fun (congr_fun h i) j
    simpa [rectRightGramEigenbasis, U, Matrix.mul_apply, Matrix.one_apply,
      matTranspose, idMatrix] using hij

/-- Column orthonormality of the right-Gram eigenvector table. -/
theorem rectRightGramEigenbasis_col_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n,
        rectRightGramEigenbasis A k i *
          rectRightGramEigenbasis A k j =
      idMatrix n i j := by
  simpa [idMatrix] using
    (rectRightGramEigenbasis_isOrthogonal A).col_orthonormal i j

/-- Row orthonormality of the right-Gram eigenvector table. -/
theorem rectRightGramEigenbasis_row_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n,
        rectRightGramEigenbasis A i k *
          rectRightGramEigenbasis A j k =
      idMatrix n i j := by
  simpa [idMatrix] using
    (rectRightGramEigenbasis_isOrthogonal A).row_orthonormal i j

/-- Basis-indexed right-Gram eigenvalues are nonnegative because
`A^T A` is positive semidefinite. -/
theorem rectRightGramEigenvalue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectRightGramEigenvalue A j := by
  let hpsd := rectRightGram_matrix_posSemidef A
  simpa [rectRightGramEigenvalue, hpsd] using hpsd.eigenvalues_nonneg j

/-- Basis-indexed right-Gram singular values are nonnegative. -/
theorem rectRightGramBasisSingularValue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectRightGramBasisSingularValue A j := by
  unfold rectRightGramBasisSingularValue
  exact Real.sqrt_nonneg _

/-- Squaring a basis-indexed right-Gram singular value recovers its
basis-indexed eigenvalue. -/
theorem rectRightGramBasisSingularValue_sq_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    (rectRightGramBasisSingularValue A j) ^ 2 =
      rectRightGramEigenvalue A j := by
  unfold rectRightGramBasisSingularValue
  exact Real.sq_sqrt (rectRightGramEigenvalue_nonneg A j)

/-- Each column of `rectRightGramEigenbasis` is an eigenvector of the exact
right Gram, with basis-indexed eigenvalue `rectRightGramEigenvalue`. -/
theorem rectRightGramEigenbasis_eigenvector {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a j : Fin n) :
    ∑ k : Fin n,
        rectRightGram A j k * rectRightGramEigenbasis A k a =
      rectRightGramEigenvalue A a * rectRightGramEigenbasis A j a := by
  let hG := (rectRightGram_matrix_posSemidef A).1
  have h := hG.mulVec_eigenvectorBasis a
  have hj := congr_fun h j
  simpa [rectRightGramEigenbasis, rectRightGramEigenvalue, hG, Matrix.mulVec,
    Matrix.IsHermitian.eigenvectorUnitary_apply] using hj

/-- Exact diagonalization of the right Gram by the right-Gram eigenvector table:
`V^T (A^T A) V` is diagonal with the basis-indexed eigenvalues. -/
theorem rectRightGramEigenbasis_diagonalizes {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) =
      if a = b then rectRightGramEigenvalue A a else 0 := by
  have heig :
      ∀ j : Fin n,
        ∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b =
          rectRightGramEigenvalue A b *
            rectRightGramEigenbasis A j b := by
    intro j
    exact rectRightGramEigenbasis_eigenvector A b j
  have horth :
      ∑ j : Fin n,
          rectRightGramEigenbasis A j a *
            rectRightGramEigenbasis A j b =
        idMatrix n a b :=
    rectRightGramEigenbasis_col_orthonormal A a b
  calc
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b)
        =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (rectRightGramEigenvalue A b *
                rectRightGramEigenbasis A j b) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [heig j]
    _ =
          rectRightGramEigenvalue A b *
            (∑ j : Fin n,
              rectRightGramEigenbasis A j a *
                rectRightGramEigenbasis A j b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = if a = b then rectRightGramEigenvalue A a else 0 := by
            by_cases hab : a = b
            · subst b
              simp [horth, idMatrix]
            · simp [horth, idMatrix, hab]

/-- Singular-value-square form of the right-Gram diagonalization. -/
theorem rectRightGramEigenbasis_diagonalizes_singularValueSq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) =
      if a = b then (rectRightGramBasisSingularValue A a) ^ 2 else 0 := by
  rw [rectRightGramEigenbasis_diagonalizes]
  by_cases hab : a = b
  · simp [hab, rectRightGramBasisSingularValue_sq_eq]
  · simp [hab]

/-- The exact column `A v_a`, where `v_a` is a basis-indexed right-Gram
eigenvector. -/
noncomputable def rectRightGramProjectedColumn {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i a => ∑ j : Fin n, A i j * rectRightGramEigenbasis A j a

/-- Left singular-vector candidates obtained from the basis-indexed
right-Gram eigenbasis by `u_a = A v_a / tau_a`.  The main orthonormality and
reconstruction theorem below requires strict positivity of every displayed
basis-indexed singular value. -/
noncomputable def rectRightGramLeftSingularFromEigenbasis {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i a =>
    (1 / rectRightGramBasisSingularValue A a) *
      rectRightGramProjectedColumn A i a

/-- Diagonal matrix formed from the basis-indexed right-Gram singular values. -/
noncomputable def rectRightGramBasisSingularDiagonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun a b => if a = b then rectRightGramBasisSingularValue A a else 0

/-- The dot product of projected columns `A v_a` and `A v_b` is the corresponding
right-Gram quadratic form. -/
theorem rectRightGramProjectedColumn_dot {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramProjectedColumn A i a *
          rectRightGramProjectedColumn A i b =
      ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) := by
  classical
  unfold rectRightGramProjectedColumn rectRightGram
  calc
    ∑ i : Fin m,
        (∑ j : Fin n, A i j * rectRightGramEigenbasis A j a) *
          (∑ k : Fin n, A i k * rectRightGramEigenbasis A k b)
        =
          ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
            (A i j * rectRightGramEigenbasis A j a) *
              (A i k * rectRightGramEigenbasis A k b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ =
          ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
            rectRightGramEigenbasis A j a *
              ((A i j * A i k) * rectRightGramEigenbasis A k b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (∑ k : Fin n,
                (∑ i : Fin m, A i j * A i k) *
                  rectRightGramEigenbasis A k b) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            calc
              ∑ i : Fin m,
                  rectRightGramEigenbasis A j a *
                    ((A i j * A i k) *
                      rectRightGramEigenbasis A k b)
                  =
                    rectRightGramEigenbasis A j a *
                      (∑ i : Fin m,
                        (A i j * A i k) *
                          rectRightGramEigenbasis A k b) := by
                    rw [Finset.mul_sum]
              _ =
                    rectRightGramEigenbasis A j a *
                      ((∑ i : Fin m, A i j * A i k) *
                        rectRightGramEigenbasis A k b) := by
                    rw [Finset.sum_mul]
    _ =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (∑ k : Fin n,
                (∑ i : Fin m, A i j * A i k) *
                  rectRightGramEigenbasis A k b) := rfl

/-- Diagonal form of `rectRightGramProjectedColumn_dot`. -/
theorem rectRightGramProjectedColumn_dot_diagonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramProjectedColumn A i a *
          rectRightGramProjectedColumn A i b =
      if a = b then (rectRightGramBasisSingularValue A a) ^ 2 else 0 := by
  rw [rectRightGramProjectedColumn_dot]
  exact rectRightGramEigenbasis_diagonalizes_singularValueSq A a b

/-- The squared norm of the projected column `A v_a` is the corresponding
basis-indexed singular value squared. -/
theorem rectRightGramProjectedColumn_normSq_eq_singularValue_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) :
    ∑ i : Fin m, (rectRightGramProjectedColumn A i a) ^ 2 =
      (rectRightGramBasisSingularValue A a) ^ 2 := by
  have h := rectRightGramProjectedColumn_dot_diagonal A a a
  simpa [pow_two] using h

/-- Eigenvalue form of the projected-column squared-norm identity. -/
theorem rectRightGramProjectedColumn_normSq_eq_eigenvalue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) :
    ∑ i : Fin m, (rectRightGramProjectedColumn A i a) ^ 2 =
      rectRightGramEigenvalue A a := by
  rw [rectRightGramProjectedColumn_normSq_eq_singularValue_sq,
    rectRightGramBasisSingularValue_sq_eq]

/-- A zero basis-indexed right-Gram singular value forces the corresponding
projected column `A v_a` to vanish coordinatewise. -/
theorem rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a = 0)
    (i : Fin m) :
    rectRightGramProjectedColumn A i a = 0 := by
  have hsum :
      ∑ k : Fin m, (rectRightGramProjectedColumn A k a) ^ 2 = 0 := by
    simpa [hτ] using
      rectRightGramProjectedColumn_normSq_eq_singularValue_sq A a
  have hterm :
      (rectRightGramProjectedColumn A i a) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (rectRightGramProjectedColumn A k a))).mp
      hsum i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hterm

/-- Eigenvalue-zero variant of
`rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero`. -/
theorem rectRightGramProjectedColumn_eq_zero_of_eigenvalue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hα : rectRightGramEigenvalue A a = 0)
    (i : Fin m) :
    rectRightGramProjectedColumn A i a = 0 := by
  apply rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero A a
  have hsq :
      (rectRightGramBasisSingularValue A a) ^ 2 = 0 := by
    simpa [hα] using rectRightGramBasisSingularValue_sq_eq A a
  exact sq_eq_zero_iff.mp hsq

/-- Zero-safe left singular-vector candidates.  When the basis-indexed singular
value vanishes we set the candidate column to zero; otherwise it is
`A v_a / tau_a`. -/
noncomputable def rectRightGramLeftSingularZeroSafe {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ := by
  classical
  exact fun i a =>
    if rectRightGramBasisSingularValue A a = 0 then 0
    else
      (1 / rectRightGramBasisSingularValue A a) *
        rectRightGramProjectedColumn A i a

/-- The zero-safe left candidate is zero on zero singular-value columns. -/
theorem rectRightGramLeftSingularZeroSafe_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a = 0)
    (i : Fin m) :
    rectRightGramLeftSingularZeroSafe A i a = 0 := by
  classical
  simp [rectRightGramLeftSingularZeroSafe, hτ]

/-- Away from zero singular values, the zero-safe left candidate is the usual
normalized projected column. -/
theorem rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a ≠ 0)
    (i : Fin m) :
    rectRightGramLeftSingularZeroSafe A i a =
      (1 / rectRightGramBasisSingularValue A a) *
        rectRightGramProjectedColumn A i a := by
  classical
  simp [rectRightGramLeftSingularZeroSafe, hτ]

/-- The zero-safe left candidates satisfy `tau_a u_a = A v_a` for every basis
index, including zero singular values. -/
theorem rectRightGramLeftSingularZeroSafe_factor_column
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (a : Fin n) :
    rectRightGramBasisSingularValue A a *
        rectRightGramLeftSingularZeroSafe A i a =
      rectRightGramProjectedColumn A i a := by
  classical
  by_cases hτ : rectRightGramBasisSingularValue A a = 0
  · have hy :
        rectRightGramProjectedColumn A i a = 0 :=
      rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero A a hτ i
    simp [rectRightGramLeftSingularZeroSafe, hτ, hy]
  · rw [rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
      A a hτ i]
    field_simp [hτ]

/-- If every basis-indexed right-Gram singular value is strictly positive, the
left candidates `A v_a / tau_a` have orthonormal columns. -/
theorem rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramLeftSingularFromEigenbasis A i b =
      idMatrix n a b := by
  let τ := rectRightGramBasisSingularValue A
  have hdot := rectRightGramProjectedColumn_dot_diagonal A a b
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramLeftSingularFromEigenbasis A i b
        =
          (1 / τ a) * (1 / τ b) *
            (∑ i : Fin m,
              rectRightGramProjectedColumn A i a *
                rectRightGramProjectedColumn A i b) := by
            unfold rectRightGramLeftSingularFromEigenbasis
            calc
              ∑ i : Fin m,
                  1 / rectRightGramBasisSingularValue A a *
                      rectRightGramProjectedColumn A i a *
                    (1 / rectRightGramBasisSingularValue A b *
                      rectRightGramProjectedColumn A i b)
                  =
                    ∑ i : Fin m,
                      ((1 / τ a) * (1 / τ b)) *
                        (rectRightGramProjectedColumn A i a *
                          rectRightGramProjectedColumn A i b) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ =
                    (1 / τ a) * (1 / τ b) *
                      (∑ i : Fin m,
                        rectRightGramProjectedColumn A i a *
                          rectRightGramProjectedColumn A i b) := by
                    rw [Finset.mul_sum]
    _ =
          (1 / τ a) * (1 / τ b) *
            (if a = b then τ a ^ 2 else 0) := by
            rw [hdot]
    _ = idMatrix n a b := by
            by_cases hab : a = b
            · subst b
              have hne : τ a ≠ 0 := ne_of_gt (hpos a)
              simp [idMatrix]
              field_simp [hne]
            · simp [idMatrix, hab]

/-- The zero-safe left candidates are orthonormal on any pair of strictly
positive basis-indexed singular values.  This is the selected-column version
needed by ordered top-`k` source-split constructors: positivity only has to be
known for the displayed columns under consideration, not for every singular
direction. -/
theorem rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a b : Fin n}
    (ha : 0 < rectRightGramBasisSingularValue A a)
    (hb : 0 < rectRightGramBasisSingularValue A b) :
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b =
      idMatrix n a b := by
  let τ := rectRightGramBasisSingularValue A
  have hane : τ a ≠ 0 := ne_of_gt ha
  have hbne : τ b ≠ 0 := ne_of_gt hb
  have hdot := rectRightGramProjectedColumn_dot_diagonal A a b
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b
        =
          (1 / τ a) * (1 / τ b) *
            (∑ i : Fin m,
              rectRightGramProjectedColumn A i a *
                rectRightGramProjectedColumn A i b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
              A a hane i,
              rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
                A b hbne i]
            ring
    _ =
          (1 / τ a) * (1 / τ b) *
            (if a = b then τ a ^ 2 else 0) := by
            rw [hdot]
    _ = idMatrix n a b := by
            by_cases hab : a = b
            · subst b
              simp [idMatrix]
              field_simp [hane]
            · simp [idMatrix, hab]

/-- A positive zero-safe left singular-vector candidate is orthogonal to any
distinct zero-safe candidate.  The second candidate may have zero singular
value, in which case it is the zero column by definition. -/
theorem rectRightGramLeftSingularZeroSafe_cross_zero_of_pos_ne
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a b : Fin n}
    (ha : 0 < rectRightGramBasisSingularValue A a) (hab : a ≠ b) :
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b =
      0 := by
  let τ := rectRightGramBasisSingularValue A
  by_cases hb0 : τ b = 0
  · calc
      ∑ i : Fin m,
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramLeftSingularZeroSafe A i b
          =
            ∑ i : Fin m,
              rectRightGramLeftSingularZeroSafe A i a * 0 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [rectRightGramLeftSingularZeroSafe_eq_zero_of_singularValue_eq_zero
                A b hb0 i]
      _ = 0 := by simp
  · have hbpos : 0 < τ b := by
      exact lt_of_le_of_ne
        (rectRightGramBasisSingularValue_nonneg A b) (Ne.symm hb0)
    have horth :=
      rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
        A ha hbpos
    simpa [idMatrix, hab] using horth

/-- Expanding in the exact right-Gram eigenbasis reconstructs every row of
`A`. -/
theorem rectRightGramProjectedColumn_reconstruct {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    ∑ a : Fin n,
        rectRightGramProjectedColumn A i a *
          rectRightGramEigenbasis A j a =
      A i j := by
  unfold rectRightGramProjectedColumn
  calc
    ∑ a : Fin n,
        (∑ k : Fin n, A i k * rectRightGramEigenbasis A k a) *
          rectRightGramEigenbasis A j a
        =
          ∑ k : Fin n,
            A i k *
              (∑ a : Fin n,
                rectRightGramEigenbasis A k a *
                  rectRightGramEigenbasis A j a) := by
            calc
              ∑ a : Fin n,
                  (∑ k : Fin n, A i k *
                    rectRightGramEigenbasis A k a) *
                    rectRightGramEigenbasis A j a
                  =
                    ∑ a : Fin n, ∑ k : Fin n,
                      (A i k * rectRightGramEigenbasis A k a) *
                        rectRightGramEigenbasis A j a := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [Finset.sum_mul]
              _ =
                    ∑ k : Fin n, ∑ a : Fin n,
                      (A i k * rectRightGramEigenbasis A k a) *
                        rectRightGramEigenbasis A j a := by
                    rw [Finset.sum_comm]
              _ =
                    ∑ k : Fin n,
                      A i k *
                        (∑ a : Fin n,
                          rectRightGramEigenbasis A k a *
                            rectRightGramEigenbasis A j a) := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro a _
                    ring
    _ =
          ∑ k : Fin n, A i k * idMatrix n k j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [rectRightGramEigenbasis_row_orthonormal A k j]
    _ = A i j := by
            simp [idMatrix]

/-- Basis-indexed SVD-style reconstruction from the zero-safe left candidates.
This removes the full-positive hypothesis but remains basis-indexed rather than
ordered. -/
theorem rectRightGram_basisSVD_representation {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    A i j =
      ∑ a : Fin n,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  rw [← rectRightGramProjectedColumn_reconstruct A i j]
  apply Finset.sum_congr rfl
  intro a _
  have hf := rectRightGramLeftSingularZeroSafe_factor_column A i a
  rw [← hf]
  ring

/-- Exact selected-index head from the zero-safe basis-indexed right-Gram
reconstruction.  This is an analysis object, not a computed SVD routine. -/
noncomputable def rectRightGramBasisSVDHead {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    s.sum fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a

/-- Exact complementary tail from the zero-safe basis-indexed right-Gram
reconstruction.  The complement is taken inside the finite right-index type. -/
noncomputable def rectRightGramBasisSVDTail {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    sᶜ.sum fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a

/-- The selected-index head plus the complementary tail reconstructs `A`
entrywise.  This is the basis-indexed source-split algebra needed before the
ordered head/tail handoff. -/
theorem rectRightGramBasisSVD_head_add_tail {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDHead A s i j +
        rectRightGramBasisSVDTail A s i j = A i j := by
  classical
  unfold rectRightGramBasisSVDHead rectRightGramBasisSVDTail
  let term : Fin n → ℝ :=
    fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a
  have hpartition :
      s.sum term + sᶜ.sum term =
        ∑ a : Fin n, term a := by
    rw [← Finset.sum_union disjoint_compl_right]
    rw [Finset.union_compl]
  rw [show
      s.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) +
        sᶜ.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) =
        s.sum term + sᶜ.sum term by rfl]
  rw [hpartition]
  exact (rectRightGram_basisSVD_representation A i j).symm

/-- Entrywise orientation of the selected-index head/tail split. -/
theorem rectRightGramBasisSVD_head_tail_entry {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    A i j =
      rectRightGramBasisSVDHead A s i j +
        rectRightGramBasisSVDTail A s i j := by
  exact (rectRightGramBasisSVD_head_add_tail A s i j).symm

/-- Rank factorization of the selected-index head through its selected
cardinality.  This is still exact-object algebra; it does not choose the
ordered top singular directions. -/
noncomputable def rectRightGramBasisSVDHeadRankFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    RectRankFactorization m n s.card (rectRightGramBasisSVDHead A s) where
  left := fun i a =>
    rectRightGramLeftSingularZeroSafe A i (s.orderEmbOfFin rfl a)
  right := fun a j =>
    rectRightGramBasisSingularValue A (s.orderEmbOfFin rfl a) *
      rectRightGramEigenbasis A j (s.orderEmbOfFin rfl a)
  factorization := by
    classical
    intro i j
    unfold rectRightGramBasisSVDHead
    let e : Fin s.card → Fin n := fun a => s.orderEmbOfFin rfl a
    let term : Fin n → ℝ :=
      fun a =>
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a
    have hsum :
        s.sum term = ∑ a : Fin s.card, term (e a) := by
      have hsub :
          (∑ a : Fin s.card, term (e a)) = ∑ x : s, term x := by
        refine Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv
          (fun a : Fin s.card => term (e a))
          (fun x : s => term x) ?_
        intro a
        simp [e]
      calc
        s.sum term = ∑ x : s, term x := by
              simpa using (Finset.sum_coe_sort s term).symm
        _ = ∑ a : Fin s.card, term (e a) := hsub.symm
    rw [hsum]
    apply Finset.sum_congr rfl
    intro a _
    simp [e, term]
    ring

/-- The selected-index right-Gram head has rank at most the selected
cardinality. -/
theorem rectRightGramBasisSVDHead_rankAtMost {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    RectRankAtMost m n s.card (rectRightGramBasisSVDHead A s) :=
  ⟨rectRightGramBasisSVDHeadRankFactorization A s⟩

/-- If the selected set has displayed cardinality `k`, the selected right-Gram
head has rank at most the paper-facing rank parameter `k`. -/
theorem rectRightGramBasisSVDHead_rankAtMost_of_card_eq {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (hcard : s.card = k) :
    RectRankAtMost m n k (rectRightGramBasisSVDHead A s) :=
  rectRankAtMost_of_eq_rank hcard
    (rectRightGramBasisSVDHead_rankAtMost A s)

/-- Selected basis-index set induced by an injective displayed index map
`Fin k ↪ Fin n`.  This is the exact-object selected-index vocabulary for the
paper-facing rank parameter before proving that a particular embedding
enumerates the ordered top singular directions. -/
def rectRightGramSelectedIndexSet {n k : ℕ} (e : Fin k ↪ Fin n) :
    Finset (Fin n) :=
  Finset.univ.map e

/-- The selected set induced by an embedding `Fin k ↪ Fin n` has cardinality
`k`. -/
theorem rectRightGramSelectedIndexSet_card {n k : ℕ}
    (e : Fin k ↪ Fin n) :
    (rectRightGramSelectedIndexSet e).card = k := by
  simp [rectRightGramSelectedIndexSet]

/-- The complement of an embedding-selected right-Gram index set has exactly
the remaining cardinality: selected plus complement directions account for all
ambient right coordinates.  This is the cardinality bridge needed before
reindexing constructed ordered head/tail source splits into a `k+q` rectangular
source-factor theorem. -/
theorem rectRightGramSelectedIndexSet_card_add_compl_card {n k : ℕ}
    (e : Fin k ↪ Fin n) :
    k + ((rectRightGramSelectedIndexSet e)ᶜ).card = n := by
  have h :=
    Finset.card_add_card_compl (rectRightGramSelectedIndexSet e)
  simpa [rectRightGramSelectedIndexSet_card e, Fintype.card_fin] using h

/-- Sums over an embedding-selected right-Gram index set are the corresponding
displayed sums over `Fin k`. -/
theorem rectRightGramSelectedIndexSet_sum {n k : ℕ}
    (e : Fin k ↪ Fin n) (term : Fin n → ℝ) :
    (rectRightGramSelectedIndexSet e).sum term =
      ∑ a : Fin k, term (e a) := by
  unfold rectRightGramSelectedIndexSet
  rw [Finset.sum_map]

/-- Sums over the complement of a right-Gram finite set are the corresponding
displayed sums over its canonical `orderEmbOfFin` enumeration. -/
theorem rectRightGramComplement_sum_orderEmbOfFin {n : ℕ}
    (s : Finset (Fin n)) (term : Fin n → ℝ) :
    (sᶜ).sum term =
      ∑ a : Fin ((sᶜ).card), term ((sᶜ).orderEmbOfFin rfl a) := by
  classical
  let e : Fin ((sᶜ).card) → Fin n := fun a => (sᶜ).orderEmbOfFin rfl a
  have hsub :
      (∑ a : Fin ((sᶜ).card), term (e a)) =
        ∑ x : {x // x ∈ (sᶜ)}, term x := by
    refine Fintype.sum_equiv ((sᶜ).orderIsoOfFin rfl).toEquiv
      (fun a : Fin ((sᶜ).card) => term (e a))
      (fun x : {x // x ∈ (sᶜ)} => term x) ?_
    intro a
    simp [e]
  calc
    (sᶜ).sum term = ∑ x : {x // x ∈ (sᶜ)}, term x := by
          simpa using (Finset.sum_coe_sort (sᶜ) term).symm
    _ = ∑ a : Fin ((sᶜ).card), term (e a) := hsub.symm














/-- Semantic certificate that an injective selected-index embedding enumerates
the ordered top right-Gram singular directions.  The certificate is intentionally
separate from the basis-indexed right-Gram eigenbasis construction: mathlib's
eigenbasis comes with an arbitrary finite basis order, while
`rectSingularValue` is the ordered zero-indexed right-Gram sequence. -/
structure RectRightGramOrderedTopEmbeddingCertificate {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n) : Prop where
  singularValue_eq :
    ∀ a : Fin k,
      rectRightGramBasisSingularValue A (e a) =
        rectSingularValue A (rectTopIndex hk a)

/-- Under the semantic ordered-top embedding certificate, the selected
basis-indexed singular-value squares agree with the ordered right-Gram
singular-value squares on the displayed first `k` indices. -/
theorem rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n)
    (h : RectRightGramOrderedTopEmbeddingCertificate A hk e) (a : Fin k) :
    (rectRightGramBasisSingularValue A (e a)) ^ 2 =
      rectSingularValueSq A (rectTopIndex hk a) := by
  rw [h.singularValue_eq a]
  exact rectSingularValue_sq_eq A (rectTopIndex hk a)

/-- Under the semantic ordered-top embedding certificate, the selected
basis-indexed singular values inherit the ordered sequence's antitone order. -/
theorem rectRightGramOrderedTopEmbeddingCertificate_selected_antitone {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n)
    (h : RectRightGramOrderedTopEmbeddingCertificate A hk e) :
    Antitone fun a : Fin k => rectRightGramBasisSingularValue A (e a) := by
  intro a b hab
  change rectRightGramBasisSingularValue A (e b) ≤
    rectRightGramBasisSingularValue A (e a)
  rw [h.singularValue_eq b, h.singularValue_eq a]
  exact rectSingularValue_antitone A (rectTopIndex_le hab)

/-- The exact equivalence used by mathlib to reindex the ordered Hermitian
eigenvalue sequence into the matrix's basis-index type.  For the right-Gram
matrix this is also the bridge between ordered singular values and the
basis-indexed eigenvector table. -/
noncomputable def rectRightGramOrderedEigenbasisEquiv (n : ℕ) :
    Fin (Fintype.card (Fin n)) ≃ Fin n :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))

/-- Constructed embedding of the displayed top-`k` ordered singular directions
into the right-Gram basis-index type, using the same mathlib reindexing
equivalence as `Matrix.IsHermitian.eigenvalues` and `eigenvectorBasis`. -/
noncomputable def rectRightGramOrderedTopEmbedding {n k : ℕ}
    (hk : k ≤ n) : Fin k ↪ Fin n where
  toFun a := rectRightGramOrderedEigenbasisEquiv n
    (finCardIndex n (rectTopIndex hk a))
  inj' := by
    intro a b h
    have hidx :
        finCardIndex n (rectTopIndex hk a) =
          finCardIndex n (rectTopIndex hk b) :=
      (rectRightGramOrderedEigenbasisEquiv n).injective h
    apply Fin.ext
    simpa [finCardIndex, rectTopIndex] using congrArg Fin.val hidx

/-- The constructed ordered-top embedding satisfies the semantic certificate:
by construction it selects the right-Gram eigenbasis columns whose
basis-indexed eigenvalues are the first `k` ordered right-Gram eigenvalues. -/
theorem rectRightGramOrderedTopEmbedding_certificate {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    RectRightGramOrderedTopEmbeddingCertificate A hk
      (rectRightGramOrderedTopEmbedding hk) where
  singularValue_eq := by
    intro a
    unfold rectRightGramBasisSingularValue rectSingularValue
      rectRightGramEigenvalue rectSingularValueSq
      rectRightGramOrderedTopEmbedding rectRightGramOrderedEigenbasisEquiv
    simp [finCardIndex, Matrix.IsHermitian.eigenvalues]

/-- Ordered singular-value coordinate corresponding to a basis-indexed
right-Gram eigenvector.  This is the inverse of the same finite equivalence
used by mathlib's `eigenvalues` and `eigenvectorBasis` APIs, cast back to the
paper-facing `Fin n` index type. -/
noncomputable def rectRightGramBasisOrderedIndex (n : ℕ) (b : Fin n) : Fin n :=
  Fin.cast (by simp) ((rectRightGramOrderedEigenbasisEquiv n).symm b)

/-- Casting the ordered coordinate back to mathlib's cardinality index recovers
the inverse eigenbasis reindexing. -/
theorem finCardIndex_rectRightGramBasisOrderedIndex (n : ℕ) (b : Fin n) :
    finCardIndex n (rectRightGramBasisOrderedIndex n b) =
      (rectRightGramOrderedEigenbasisEquiv n).symm b := by
  apply Fin.ext
  simp [finCardIndex, rectRightGramBasisOrderedIndex]

/-- A basis-indexed right-Gram singular value is the ordered singular value at
the basis column's inverse mathlib reindexing coordinate. -/
theorem rectRightGramBasisSingularValue_eq_orderedIndex {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin n) :
    rectRightGramBasisSingularValue A b =
      rectSingularValue A (rectRightGramBasisOrderedIndex n b) := by
  unfold rectRightGramBasisSingularValue rectSingularValue
    rectRightGramEigenvalue rectSingularValueSq
    rectRightGramBasisOrderedIndex rectRightGramOrderedEigenbasisEquiv
  simp [finCardIndex, Matrix.IsHermitian.eigenvalues]

/-- If a basis index is not selected by the constructed top-`k` embedding, then
its ordered coordinate lies at or beyond the displayed top block. -/
theorem rectRightGramOrderedTopEmbedding_not_mem_index_ge {n k : ℕ}
    (hk : k ≤ n) {b : Fin n}
    (hb : b ∉ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) :
    k ≤ (rectRightGramBasisOrderedIndex n b).val := by
  classical
  by_contra hge
  have hlt : (rectRightGramBasisOrderedIndex n b).val < k :=
    Nat.lt_of_not_ge hge
  let a : Fin k := ⟨(rectRightGramBasisOrderedIndex n b).val, hlt⟩
  have heq : rectRightGramOrderedTopEmbedding hk a = b := by
    change rectRightGramOrderedEigenbasisEquiv n
        (finCardIndex n (rectTopIndex hk a)) = b
    rw [← (rectRightGramOrderedEigenbasisEquiv n).apply_symm_apply b]
    congr 1
  have hmem :
      b ∈ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk) := by
    rw [← heq]
    simp [rectRightGramSelectedIndexSet]
  exact hb hmem

/-- Every displayed top index precedes the ordered coordinate of an unselected
basis direction. -/
theorem rectTopIndex_le_rectRightGramBasisOrderedIndex_of_not_mem_orderedTopEmbedding
    {n k : ℕ} (hk : k ≤ n) {b : Fin n}
    (hb : b ∉ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
    (a : Fin k) :
    rectTopIndex hk a ≤ rectRightGramBasisOrderedIndex n b := by
  rw [Fin.le_def]
  exact Nat.le_trans (Nat.le_of_lt a.isLt)
    (rectRightGramOrderedTopEmbedding_not_mem_index_ge hk hb)

/-- For the constructed ordered-top embedding, every selected singular value
dominates every unselected basis-indexed singular value.  This is the exact
spectral-index comparison needed before a future Eckart--Young/tail-optimality
step; it does not itself prove a best-rank theorem. -/
theorem rectRightGramOrderedTopEmbedding_complement_singularValue_le_selected
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) {b : Fin n}
    (hb : b ∉ rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
    (a : Fin k) :
    rectRightGramBasisSingularValue A b ≤
      rectRightGramBasisSingularValue A (rectRightGramOrderedTopEmbedding hk a) := by
  rw [rectRightGramBasisSingularValue_eq_orderedIndex A b,
    (rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq a]
  exact rectSingularValue_antitone A
    (rectTopIndex_le_rectRightGramBasisOrderedIndex_of_not_mem_orderedTopEmbedding
      hk hb a)


















/-- Positivity of the kth ordered singular value forces positivity of all
displayed top-`k` ordered singular values. -/
theorem rectSingularValue_top_pos_of_last_pos {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a : Fin k, 0 < rectSingularValue A (rectTopIndex hk a) := by
  intro a
  have hle :
      rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)) ≤
        rectSingularValue A (rectTopIndex hk a) :=
    rectSingularValue_antitone A (rectTopIndex_le_last hk hk0 a)
  exact lt_of_lt_of_le hlast hle

/-- Positivity of the kth ordered singular value gives positive selected
basis-indexed singular values for the constructed ordered-top embedding. -/
theorem rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a : Fin k,
      0 <
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) := by
  intro a
  rw [(rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq a]
  exact rectSingularValue_top_pos_of_last_pos A hk hk0 hlast a

/-- Positivity of the kth ordered singular value gives nonzero selected
basis-indexed singular values for the constructed ordered-top embedding. -/
theorem rectRightGramOrderedTopEmbedding_selected_nonzero_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a : Fin k,
      rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) ≠ 0 := by
  intro a
  exact ne_of_gt
    (rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
      A hk hk0 hlast a)

/-- Under a positive kth ordered singular value, the zero-safe left candidates
selected by the constructed ordered-top embedding have orthonormal columns.
This is an exact source-SVD left-basis ingredient; computed singular-vector
tables remain separate non-probability FP/certificate obligations. -/
theorem rectRightGramOrderedTopEmbedding_leftZeroSafe_col_orthonormal_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (a b : Fin k) :
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk b) =
      idMatrix k a b := by
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk b)
        =
      idMatrix n (rectRightGramOrderedTopEmbedding hk a)
        (rectRightGramOrderedTopEmbedding hk b) := by
        exact
          rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos A
            (rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
              A hk hk0 hlast a)
            (rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
              A hk hk0 hlast b)
    _ = idMatrix k a b := by
        by_cases hab : a = b
        · subst b
          simp [idMatrix]
        · have hne :
              rectRightGramOrderedTopEmbedding hk a ≠
                rectRightGramOrderedTopEmbedding hk b := by
            intro h
            exact hab ((rectRightGramOrderedTopEmbedding hk).injective h)
          simp [idMatrix, hab, hne]

/-- Ordered top-`k` zero-safe left candidate table.  This is an exact analysis
object; a computed singular-vector table needs a separate non-probability
perturbation certificate. -/
noncomputable def rectRightGramOrderedHeadLeft {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) : Fin m → Fin k → ℝ :=
  fun i a => rectRightGramLeftSingularZeroSafe A i
    (rectRightGramOrderedTopEmbedding hk a)

/-- Ordered top-`k` right singular-vector table from the exact right-Gram
eigenbasis. -/
noncomputable def rectRightGramOrderedHeadRight {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) : Fin n → Fin k → ℝ :=
  fun j a => rectRightGramEigenbasis A j
    (rectRightGramOrderedTopEmbedding hk a)

/-- Ordered top-`k` diagonal singular-value table from the exact right-Gram
singular values selected by the constructed embedding. -/
noncomputable def rectRightGramOrderedHeadSingularDiagonal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin k → Fin k → ℝ :=
  fun a b =>
    if a = b then
      rectRightGramBasisSingularValue A (rectRightGramOrderedTopEmbedding hk a)
    else
      0

/-- Complement-tail left candidate table obtained by enumerating the complement
of a selected right-Gram index set.  This is an exact analysis object; it is
not a computed tail-left basis, and zero singular values need a separate
nullspace completion before a full rectangular SVD certificate can use it as an
orthonormal tail basis. -/
noncomputable def rectRightGramBasisSVDTailLeft {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin ((sᶜ).card) → ℝ :=
  fun i a =>
    rectRightGramLeftSingularZeroSafe A i ((sᶜ).orderEmbOfFin rfl a)

/-- Complement-tail right table obtained by enumerating the complement of a
selected right-Gram index set. -/
noncomputable def rectRightGramBasisSVDTailRight {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin n → Fin ((sᶜ).card) → ℝ :=
  fun j a => rectRightGramEigenbasis A j ((sᶜ).orderEmbOfFin rfl a)

/-- Complement-tail diagonal singular-value table obtained by enumerating the
complement of a selected right-Gram index set. -/
noncomputable def rectRightGramBasisSVDTailSingularDiagonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin ((sᶜ).card) → Fin ((sᶜ).card) → ℝ :=
  fun a b =>
    if a = b then
      rectRightGramBasisSingularValue A ((sᶜ).orderEmbOfFin rfl a)
    else
      0

/-- Ordered complement-tail left candidate table for the constructed top-`k`
selection. -/
noncomputable def rectRightGramOrderedTailLeft {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin m →
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  rectRightGramBasisSVDTailLeft A
    (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))

/-- Ordered complement-tail right table for the constructed top-`k` selection. -/
noncomputable def rectRightGramOrderedTailRight {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin n →
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  rectRightGramBasisSVDTailRight A
    (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))

/-- Ordered complement-tail diagonal singular-value table for the constructed
top-`k` selection. -/
noncomputable def rectRightGramOrderedTailSingularDiagonal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) →
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  rectRightGramBasisSVDTailSingularDiagonal A
    (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))

/-- If every complement-enumerated basis-indexed singular value is strictly
positive, the complement-tail zero-safe left candidate table has orthonormal
columns.  This closes the positive-complement branch only; if some complement
singular value vanishes, a separate nullspace-completed tail-left basis is
needed. -/
theorem rectRightGramBasisSVDTailLeft_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (hpos :
      ∀ c : Fin ((sᶜ).card),
        0 < rectRightGramBasisSingularValue A
          ((sᶜ).orderEmbOfFin rfl c))
    (c d : Fin ((sᶜ).card)) :
    ∑ i : Fin m,
        rectRightGramBasisSVDTailLeft A s i c *
          rectRightGramBasisSVDTailLeft A s i d =
      idMatrix ((sᶜ).card) c d := by
  classical
  let ec : Fin n := (sᶜ).orderEmbOfFin rfl c
  let ed : Fin n := (sᶜ).orderEmbOfFin rfl d
  have horth :
      ∑ i : Fin m,
          rectRightGramLeftSingularZeroSafe A i ec *
            rectRightGramLeftSingularZeroSafe A i ed =
        idMatrix n ec ed :=
    rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
      A (hpos c) (hpos d)
  calc
    ∑ i : Fin m,
        rectRightGramBasisSVDTailLeft A s i c *
          rectRightGramBasisSVDTailLeft A s i d
        =
          idMatrix n ec ed := by
          simpa [rectRightGramBasisSVDTailLeft, ec, ed] using horth
    _ = idMatrix ((sᶜ).card) c d := by
          by_cases hcd : c = d
          · subst d
            have heq : ec = ed := by
              simp [ec, ed]
            simp [idMatrix, heq]
          · have hne : ec ≠ ed := by
              intro h
              exact hcd (((sᶜ).orderEmbOfFin rfl).injective h)
            simp [idMatrix, hcd, hne]

/-- Ordered complement-tail left orthonormality under strict positivity of all
constructed complement singular values.  This is still an exact-object theorem:
computed singular vectors or tail-left basis routines need separate
non-probability FP certificates. -/
theorem rectRightGramOrderedTailLeft_col_orthonormal_of_complement_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hpos :
      ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        0 < rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c))
    (c d :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    ∑ i : Fin m,
        rectRightGramOrderedTailLeft A hk i c *
          rectRightGramOrderedTailLeft A hk i d =
      idMatrix
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d := by
  simpa [rectRightGramOrderedTailLeft] using
    rectRightGramBasisSVDTailLeft_col_orthonormal_of_pos
      A (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
      hpos c d

/-- If a complement-enumerated singular value is zero, the corresponding
zero-safe tail-left column is identically zero, so its self-dot is zero. -/
theorem rectRightGramBasisSVDTailLeft_self_dot_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    {c : Fin ((sᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        ((sᶜ).orderEmbOfFin rfl c) = 0) :
    ∑ i : Fin m,
        rectRightGramBasisSVDTailLeft A s i c *
          rectRightGramBasisSVDTailLeft A s i c =
      0 := by
  unfold rectRightGramBasisSVDTailLeft
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl c) *
          rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl c)
        =
          ∑ i : Fin m, 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [rectRightGramLeftSingularZeroSafe_eq_zero_of_singularValue_eq_zero
            A ((sᶜ).orderEmbOfFin rfl c) hzero i]
          ring
    _ = 0 := by simp

/-- The raw zero-safe complement-tail left table cannot itself be column
orthonormal if any complement singular value is zero.  This is the formal
obstruction that forces a nullspace-completed tail-left basis in the zero-tail
case. -/
theorem not_rectRightGramBasisSVDTailLeft_col_orthonormal_of_zero_singularValue
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    {c : Fin ((sᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        ((sᶜ).orderEmbOfFin rfl c) = 0) :
    ¬ (∀ c d : Fin ((sᶜ).card),
      ∑ i : Fin m,
          rectRightGramBasisSVDTailLeft A s i c *
            rectRightGramBasisSVDTailLeft A s i d =
        idMatrix ((sᶜ).card) c d) := by
  intro horth
  have hself :=
    rectRightGramBasisSVDTailLeft_self_dot_eq_zero_of_singularValue_eq_zero
      A s hzero
  have hdiag := horth c c
  have hbad : (0 : ℝ) = 1 := by
    calc
      (0 : ℝ) =
          ∑ i : Fin m,
            rectRightGramBasisSVDTailLeft A s i c *
              rectRightGramBasisSVDTailLeft A s i c := hself.symm
      _ = idMatrix ((sᶜ).card) c c := hdiag
      _ = 1 := by simp [idMatrix]
  norm_num at hbad

/-- Ordered specialization of the zero-tail obstruction: the constructed
ordered zero-safe tail-left table cannot be orthonormal if any constructed
complement singular value is zero. -/
theorem not_rectRightGramOrderedTailLeft_col_orthonormal_of_zero_complement_singularValue
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    {c :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) = 0) :
    ¬ (∀ c d :
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
      ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
        idMatrix
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) := by
  simpa [rectRightGramOrderedTailLeft] using
    not_rectRightGramBasisSVDTailLeft_col_orthonormal_of_zero_singularValue
      A (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
      hzero

/-- Under a positive kth ordered singular value, the ordered head-left table
has orthonormal columns. -/
theorem rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (a b : Fin k) :
    ∑ i : Fin m,
        rectRightGramOrderedHeadLeft A hk i a *
          rectRightGramOrderedHeadLeft A hk i b =
      idMatrix k a b := by
  simpa [rectRightGramOrderedHeadLeft] using
    rectRightGramOrderedTopEmbedding_leftZeroSafe_col_orthonormal_of_last_pos
      A hk hk0 hlast a b

/-- Under a positive kth ordered singular value, the constructed ordered
head-left block is left-orthogonal to the constructed complement-tail
zero-safe left block.  This closes the exact cross field
`U_ord^T U_tail = 0`; tail-left orthonormality still requires a separate
nullspace-completion argument. -/
theorem rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast : 0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (a : Fin k)
    (c :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    ∑ i : Fin m,
        rectRightGramOrderedHeadLeft A hk i a *
          rectRightGramOrderedTailLeft A hk i c =
      0 := by
  classical
  let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
  let b : Fin n := (sᶜ).orderEmbOfFin rfl c
  have hhead_mem :
      rectRightGramOrderedTopEmbedding hk a ∈ s := by
    simp [s, rectRightGramSelectedIndexSet]
  have htail_mem : b ∈ sᶜ := by
    simp [b, Finset.orderEmbOfFin_mem]
  have htail_not_mem : b ∉ s := Finset.mem_compl.mp htail_mem
  have hne : rectRightGramOrderedTopEmbedding hk a ≠ b := by
    intro h
    exact htail_not_mem (by simpa [h] using hhead_mem)
  have hpos :=
    rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
      A hk hk0 hlast a
  simpa [rectRightGramOrderedHeadLeft, rectRightGramOrderedTailLeft,
    rectRightGramBasisSVDTailLeft, s, b] using
    rectRightGramLeftSingularZeroSafe_cross_zero_of_pos_ne
      A hpos hne

/-- The ordered head-right table has orthonormal columns by restriction of the
exact right-Gram eigenbasis to the constructed top-`k` embedding. -/
theorem rectRightGramOrderedHeadRight_col_orthonormal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (a b : Fin k) :
    ∑ j : Fin n,
        rectRightGramOrderedHeadRight A hk j a *
          rectRightGramOrderedHeadRight A hk j b =
      idMatrix k a b := by
  calc
    ∑ j : Fin n,
        rectRightGramOrderedHeadRight A hk j a *
          rectRightGramOrderedHeadRight A hk j b
        =
      idMatrix n (rectRightGramOrderedTopEmbedding hk a)
        (rectRightGramOrderedTopEmbedding hk b) := by
        simpa [rectRightGramOrderedHeadRight] using
          rectRightGramEigenbasis_col_orthonormal A
            (rectRightGramOrderedTopEmbedding hk a)
            (rectRightGramOrderedTopEmbedding hk b)
    _ = idMatrix k a b := by
        by_cases hab : a = b
        · subst b
          simp [idMatrix]
        · have hne :
              rectRightGramOrderedTopEmbedding hk a ≠
                rectRightGramOrderedTopEmbedding hk b := by
            intro h
            exact hab ((rectRightGramOrderedTopEmbedding hk).injective h)
          simp [idMatrix, hab, hne]

/-- The complement-tail right table has orthonormal columns by restriction of
the exact right-Gram eigenbasis to the complement enumeration. -/
theorem rectRightGramBasisSVDTailRight_col_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (a b : Fin ((sᶜ).card)) :
    ∑ j : Fin n,
        rectRightGramBasisSVDTailRight A s j a *
          rectRightGramBasisSVDTailRight A s j b =
      idMatrix ((sᶜ).card) a b := by
  calc
    ∑ j : Fin n,
        rectRightGramBasisSVDTailRight A s j a *
          rectRightGramBasisSVDTailRight A s j b
        =
      idMatrix n ((sᶜ).orderEmbOfFin rfl a)
        ((sᶜ).orderEmbOfFin rfl b) := by
        simpa [rectRightGramBasisSVDTailRight] using
          rectRightGramEigenbasis_col_orthonormal A
            ((sᶜ).orderEmbOfFin rfl a) ((sᶜ).orderEmbOfFin rfl b)
    _ = idMatrix ((sᶜ).card) a b := by
        by_cases hab : a = b
        · subst b
          simp [idMatrix]
        · have hne :
              (sᶜ).orderEmbOfFin rfl a ≠
                (sᶜ).orderEmbOfFin rfl b := by
            intro h
            exact hab (((sᶜ).orderEmbOfFin rfl).injective h)
          simp [idMatrix, hab, hne]

/-- The ordered complement-tail right table has orthonormal columns by
specializing the arbitrary-complement theorem to the constructed top-`k` set. -/
theorem rectRightGramOrderedTailRight_col_orthonormal {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (a b :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    ∑ j : Fin n,
        rectRightGramOrderedTailRight A hk j a *
          rectRightGramOrderedTailRight A hk j b =
      idMatrix (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
  simpa [rectRightGramOrderedTailRight] using
    rectRightGramBasisSVDTailRight_col_orthonormal A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) a b

/-- The selected right-Gram head induced by an injective selected-index map has
rank at most the displayed paper rank `k`. -/
theorem rectRightGramBasisSVDHead_rankAtMost_of_embedding {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n) :
    RectRankAtMost m n k
      (rectRightGramBasisSVDHead A (rectRightGramSelectedIndexSet e)) :=
  rectRightGramBasisSVDHead_rankAtMost_of_card_eq A
    (rectRightGramSelectedIndexSet e) (rectRightGramSelectedIndexSet_card e)

/-- The positive basis-indexed singular values convert the left-candidate
definition back into the projected column identity `tau_a u_a=A v_a`. -/
theorem rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (i : Fin m) (a : Fin n) :
    rectRightGramBasisSingularValue A a *
        rectRightGramLeftSingularFromEigenbasis A i a =
      rectRightGramProjectedColumn A i a := by
  have hne : rectRightGramBasisSingularValue A a ≠ 0 :=
    ne_of_gt (hpos a)
  unfold rectRightGramLeftSingularFromEigenbasis
  field_simp [hne]

/-- Full-positive basis-indexed SVD-style reconstruction from the right-Gram
eigenbasis.  This is exact-object algebra under a visible positivity
hypothesis; it is not yet the ordered rank-deficient rectangular SVD split. -/
theorem rectRightGram_fullPositive_basisSVD_representation {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (i : Fin m) (j : Fin n) :
    A i j =
      ∑ a : Fin n,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  rw [← rectRightGramProjectedColumn_reconstruct A i j]
  apply Finset.sum_congr rfl
  intro a _
  have hf :=
    rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos A hpos i a
  rw [← hf]
  ring












































































































































































































































































































































































































































































































































































































































































































































namespace UnitaryInvariantRectNormLike

















end UnitaryInvariantRectNormLike

































































































/-- Exact right-subspace projection approximation `A (V Vᵀ)`. -/
noncomputable def rightBasisProjectorApprox {m n q : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin q → ℝ) :
    Fin m → Fin n → ℝ :=
  preconditionColumns A (basisColumnProjector V)

/-- Exact left-subspace projection approximation `(U Uᵀ) A`. -/
noncomputable def leftBasisProjectorApprox {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  preconditionRows (basisColumnProjector U) A

/-- The exact right projected approximation factors through the displayed
right-basis dimension. -/
noncomputable def rightBasisProjectorApproxFactorization {m n q : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin q → ℝ) :
    RectRankFactorization m n q (rightBasisProjectorApprox A V) where
  left := fun i a => ∑ j : Fin n, A i j * V j a
  right := fun a j => V j a
  factorization := by
    intro i j
    unfold rightBasisProjectorApprox preconditionColumns basisColumnProjector
    calc
      (∑ k : Fin n, A i k * ∑ a : Fin q, V k a * V j a)
          = ∑ k : Fin n, ∑ a : Fin q, A i k * (V k a * V j a) := by
              simp_rw [Finset.mul_sum]
      _ = ∑ a : Fin q, ∑ k : Fin n, A i k * (V k a * V j a) := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin q, (∑ k : Fin n, A i k * V k a) * V j a := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- The exact right projected approximation has rank at most the number of
displayed basis columns. -/
theorem rightBasisProjectorApprox_rankAtMost {m n q : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin q → ℝ) :
    RectRankAtMost m n q (rightBasisProjectorApprox A V) :=
  ⟨rightBasisProjectorApproxFactorization A V⟩

/-- The exact left projected approximation factors through the displayed
left-basis dimension. -/
noncomputable def leftBasisProjectorApproxFactorization {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (A : Fin m → Fin n → ℝ) :
    RectRankFactorization m n q (leftBasisProjectorApprox U A) where
  left := U
  right := fun a j => ∑ i : Fin m, U i a * A i j
  factorization := by
    intro i j
    unfold leftBasisProjectorApprox preconditionRows basisColumnProjector
    calc
      (∑ k : Fin m, (∑ a : Fin q, U i a * U k a) * A k j)
          = ∑ k : Fin m, ∑ a : Fin q, (U i a * U k a) * A k j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ a : Fin q, ∑ k : Fin m, (U i a * U k a) * A k j := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin q, U i a * (∑ k : Fin m, U k a * A k j) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- The exact left projected approximation has rank at most the number of
displayed basis columns. -/
theorem leftBasisProjectorApprox_rankAtMost {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (A : Fin m → Fin n → ℝ) :
    RectRankAtMost m n q (leftBasisProjectorApprox U A) :=
  ⟨leftBasisProjectorApproxFactorization U A⟩































/-- An exact right basis-product approximation with exactly `k` displayed
basis vectors is a valid comparison candidate for a best rank-`k` Frobenius
approximation. -/
theorem IsBestRankApproxFrob.residual_le_rightBasisProjectorApprox {m n k : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (V : Fin n → Fin k → ℝ) :
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A (rightBasisProjectorApprox A V) :=
  hbest.residual_le_of_rankAtMost (rightBasisProjectorApprox_rankAtMost A V)

/-- An exact left basis-product approximation with exactly `k` displayed
basis vectors is a valid comparison candidate for a best rank-`k` Frobenius
approximation. -/
theorem IsBestRankApproxFrob.residual_le_leftBasisProjectorApprox {m n k : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (U : Fin m → Fin k → ℝ) :
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A (leftBasisProjectorApprox U A) :=
  hbest.residual_le_of_rankAtMost (leftBasisProjectorApprox_rankAtMost U A)

/-- Exact column sketch `A Z`, the column-space object appearing in the
source equation (9) as `P_{A Z}`. -/
noncomputable def columnSketch {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin m → Fin r → ℝ :=
  preconditionColumns A Z

/-- Exact head matrix generated by multiplying the sketch `A Z` by a displayed
coefficient table `W`.  The source equation (9) pseudoinverse route will later
instantiate `W` with a source-subspace coefficient such as a `V_k^T Z`
pseudoinverse expression. -/
noncomputable def columnSketchHead {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => ∑ a : Fin r, columnSketch A Z i a * W a j

/-- Exact residual tail associated with the displayed sketch coefficient table
`W`: `A - (A Z) W`. -/
noncomputable def columnSketchTail {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => A i j - columnSketchHead A Z W i j

/-- Certificate that a displayed head matrix lies in the exact column space of
the sketch `A Z`.  In the source equation (9) proof, this is the algebraic
obligation that the leading SVD part is reproduced by the sketch projector. -/
structure ColumnSketchHeadFactorization {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Head : Fin m → Fin n → ℝ) where
  coeff : Fin r → Fin n → ℝ
  factorization :
    ∀ i j, Head i j = ∑ a : Fin r, columnSketch A Z i a * coeff a j

/-- The canonical head `(A Z) W` factors through the sketch columns. -/
noncomputable def columnSketchHead_headFactorization {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    ColumnSketchHeadFactorization A Z (columnSketchHead A Z W) where
  coeff := W
  factorization := by
    intro i j
    rfl

/-- Exact selected right-Gram eigenvector sketch matrix.  Its columns are the
right-Gram eigenbasis vectors indexed by the selected finite set `s`. -/
noncomputable def rectRightGramBasisSketchMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin n → Fin s.card → ℝ :=
  fun j a => rectRightGramEigenbasis A j (s.orderEmbOfFin rfl a)

/-- Coefficient table for the selected right-Gram eigenvector sketch head. -/
noncomputable def rectRightGramBasisSketchCoeff {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin s.card → Fin n → ℝ :=
  fun a j => rectRightGramEigenbasis A j (s.orderEmbOfFin rfl a)

/-- The selected eigenvector sketch columns are exactly the selected projected
columns `A v_a`. -/
theorem columnSketch_rectRightGramBasisSketchMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (a : Fin s.card) :
    columnSketch A (rectRightGramBasisSketchMatrix A s) i a =
      rectRightGramProjectedColumn A i (s.orderEmbOfFin rfl a) := by
  rfl

/-- The selected right-Gram head is the column-sketch head generated by the
selected eigenvector sketch and coefficient table. -/
theorem rectRightGramBasisSketch_head_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDHead A s i j =
      columnSketchHead A (rectRightGramBasisSketchMatrix A s)
        (rectRightGramBasisSketchCoeff A s) i j := by
  classical
  unfold rectRightGramBasisSVDHead columnSketchHead
  let e : Fin s.card → Fin n := fun a => s.orderEmbOfFin rfl a
  let term : Fin n → ℝ :=
    fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a
  have hsum :
      s.sum term = ∑ a : Fin s.card, term (e a) := by
    have hsub :
        (∑ a : Fin s.card, term (e a)) = ∑ x : s, term x := by
      refine Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv
        (fun a : Fin s.card => term (e a))
        (fun x : s => term x) ?_
      intro a
      simp [e]
    calc
      s.sum term = ∑ x : s, term x := by
            simpa using (Finset.sum_coe_sort s term).symm
      _ = ∑ a : Fin s.card, term (e a) := hsub.symm
  rw [show
      s.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) = s.sum term by rfl]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro a _
  rw [columnSketch_rectRightGramBasisSketchMatrix A s i a]
  have hf := rectRightGramLeftSingularZeroSafe_factor_column A i (e a)
  rw [← hf]
  simp [rectRightGramBasisSketchCoeff, e]
  ring

/-- Column-sketch factorization of the selected right-Gram head through the
selected eigenvector sketch. -/
noncomputable def rectRightGramBasisSketchHeadFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    ColumnSketchHeadFactorization A (rectRightGramBasisSketchMatrix A s)
      (rectRightGramBasisSVDHead A s) where
  coeff := rectRightGramBasisSketchCoeff A s
  factorization := by
    intro i j
    exact rectRightGramBasisSketch_head_eq A s i j

/-- The selected right-Gram head lies in the exact selected-eigenvector sketch
column space. -/
noncomputable def rectRightGramBasisSVDHead_columnSketchHeadFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    ColumnSketchHeadFactorization A (rectRightGramBasisSketchMatrix A s)
      (rectRightGramBasisSVDHead A s) :=
  rectRightGramBasisSketchHeadFactorization A s

/-- The canonical head/tail pair induced by `W` splits `A`. -/
theorem columnSketchHeadTail_split {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) :
    ∀ i j, A i j = columnSketchHead A Z W i j + columnSketchTail A Z W i j := by
  intro i j
  unfold columnSketchTail
  ring

/-- If a left multiplier reproduces the sketch columns, then it reproduces any
head matrix that factors through those columns. -/
theorem preconditionRows_reproduces_head_of_columnSketchHeadFactorization
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P : Fin m → Fin m → ℝ) (Head : Fin m → Fin n → ℝ)
    (hrepr :
      ∀ i a, preconditionRows P (columnSketch A Z) i a = columnSketch A Z i a)
    (hHead : ColumnSketchHeadFactorization A Z Head) :
    ∀ i j, preconditionRows P Head i j = Head i j := by
  intro i j
  calc
    preconditionRows P Head i j
        = ∑ k : Fin m, P i k * Head k j := by rfl
    _ = ∑ k : Fin m,
          P i k * (∑ a : Fin r, columnSketch A Z k a * hHead.coeff a j) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hHead.factorization k j]
    _ = ∑ k : Fin m, ∑ a : Fin r,
          P i k * (columnSketch A Z k a * hHead.coeff a j) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ a : Fin r, ∑ k : Fin m,
          P i k * (columnSketch A Z k a * hHead.coeff a j) := by
          rw [Finset.sum_comm]
    _ = ∑ a : Fin r,
          (∑ k : Fin m, P i k * columnSketch A Z k a) * hHead.coeff a j := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ a : Fin r,
          preconditionRows P (columnSketch A Z) i a * hHead.coeff a j := by
          rfl
    _ = ∑ a : Fin r, columnSketch A Z i a * hHead.coeff a j := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hrepr i a]
    _ = Head i j := by
          rw [hHead.factorization i j]










/-- If a left multiplier factors through `r` displayed columns, then multiplying
any `m × n` matrix on the left by it gives a matrix of repository rank at most
`r`. -/
noncomputable def leftProductFactorizationOfLeftFactorThrough {m n r : ℕ}
    {P : Fin m → Fin m → ℝ} {B : Fin m → Fin r → ℝ}
    (hP : LeftFactorThrough P B) (A : Fin m → Fin n → ℝ) :
    RectRankFactorization m n r (preconditionRows P A) where
  left := B
  right := fun a j => ∑ k : Fin m, hP.coeff a k * A k j
  factorization := by
    intro i j
    unfold preconditionRows
    calc
      (∑ k : Fin m, P i k * A k j)
          = ∑ k : Fin m, (∑ a : Fin r, B i a * hP.coeff a k) * A k j := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hP.factorization]
      _ = ∑ k : Fin m, ∑ a : Fin r, (B i a * hP.coeff a k) * A k j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ a : Fin r, ∑ k : Fin m, (B i a * hP.coeff a k) * A k j := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin r, B i a * (∑ k : Fin m, hP.coeff a k * A k j) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- Rank-at-most wrapper for a left product whose multiplier factors through
`r` displayed columns. -/
theorem preconditionRows_rankAtMost_of_leftFactorThrough {m n r : ℕ}
    {P : Fin m → Fin m → ℝ} {B : Fin m → Fin r → ℝ}
    (hP : LeftFactorThrough P B) (A : Fin m → Fin n → ℝ) :
    RectRankAtMost m n r (preconditionRows P A) :=
  ⟨leftProductFactorizationOfLeftFactorThrough hP A⟩

/-- Exact equation (9) projector candidate: if `P_AZ` factors through the
column sketch `A Z`, then `P_AZ A` has repository rank at most the number of
sketch columns. -/
theorem sketchColumnProjectorApprox_rankAtMost {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z)) :
    RectRankAtMost m n r (preconditionRows P_AZ A) :=
  preconditionRows_rankAtMost_of_leftFactorThrough hP A





































































































































































































































































































































































































































































































































































































































































































































































/-- Exact left multiplier obtained by multiplying the column sketch `A Z` by a
displayed coefficient table `C`.  Later pseudoinverse infrastructure can
instantiate `C` with `(A Z)^+`; this definition itself is only exact algebra. -/
noncomputable def columnSketchLeftMultiplier {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i j => ∑ a : Fin r, columnSketch A Z i a * C a j

/-- Exact right multiplier `C (A Z)` appearing in the Moore-Penrose equations
for a coefficient table `C`.  The source proof eventually needs the full
four-equation pseudoinverse surface; this definition exposes the `C B` side
without constructing a pseudoinverse. -/
noncomputable def columnSketchRightMultiplier {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    Fin r → Fin r → ℝ :=
  preconditionRows C (columnSketch A Z)

/-- Exact Gram matrix `Bᵀ B` for the column sketch `B = A Z`.  This is an
analysis object used to state the full-column-rank pseudoinverse route; no
floating-point cost is charged unless an implementation actually computes it. -/
noncomputable def columnSketchGram {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun a b => ∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b

/-- The exact sketch Gram matrix `BᵀB` is symmetric. -/
theorem columnSketchGram_symmetric {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    IsSymmetricFiniteMatrix (columnSketchGram A Z) := by
  intro a b
  unfold columnSketchGram
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic form of a column-sketch Gram matrix is the squared norm of
the corresponding sketched column combination. -/
theorem finiteQuadraticForm_columnSketchGram_eq_sum_sq {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (x : Fin r → ℝ) :
    finiteQuadraticForm (columnSketchGram A Z) x =
      ∑ i : Fin m, (∑ a : Fin r, columnSketch A Z i a * x a) ^ 2 := by
  classical
  unfold finiteQuadraticForm finiteMatVec columnSketchGram
  calc
    ∑ a : Fin r,
        x a *
          ∑ b : Fin r,
            (∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b) *
              x b
        =
          ∑ a : Fin r, ∑ b : Fin r, ∑ i : Fin m,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ b : Fin r, ∑ a : Fin r, ∑ i : Fin m,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ b : Fin r, ∑ i : Fin m, ∑ a : Fin r,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ b : Fin r, ∑ a : Fin r,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ a : Fin r, ∑ b : Fin r,
            (columnSketch A Z i a * x a) *
              (columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m,
            (∑ a : Fin r, columnSketch A Z i a * x a) *
              (∑ b : Fin r, columnSketch A Z i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ =
          ∑ i : Fin m, (∑ a : Fin r, columnSketch A Z i a * x a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Every exact column-sketch Gram matrix is positive semidefinite. -/
theorem columnSketchGram_finitePSD {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    finitePSD (columnSketchGram A Z) := by
  intro x
  rw [finiteQuadraticForm_columnSketchGram_eq_sum_sq A Z x]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _






















/-- Exact coefficient table `G^{-1} Bᵀ` for the column sketch `B = A Z` and a
supplied inverse candidate `Ginv` for `G = BᵀB`. -/
noncomputable def columnSketchGramInverseCoefficient {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ) :
    Fin r → Fin m → ℝ :=
  fun a i => ∑ b : Fin r, Ginv a b * columnSketch A Z i b

/-- The concrete exact Gram-inverse projector candidate
`P = (A Z) ((A Z)ᵀ(A Z))^{-1}(A Z)ᵀ`.  This is an analysis object unless an
implementation-facing theorem supplies floating-point certificates for the
Gram, inverse, products, and storage. -/
noncomputable def columnSketchGramInverseProjector {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin m → Fin m → ℝ :=
  columnSketchLeftMultiplier A Z
    (columnSketchGramInverseCoefficient A Z
      (nonsingInv r (columnSketchGram A Z)))

/-- Concrete computed-object certificate for the low-rank column-sketch
Gram-inverse projector when the exact analysis projector is stored by rounded
multiply-one copies before it is applied to `A`.

This charges only the non-probability storage/copy of the already supplied
projector entries.  It is not a floating-point routine for forming the sketch
Gram, inverting it, or multiplying out the projector; those routine
instantiations remain separate implementation-facing obligations. -/
noncomputable def columnSketchGramInverseProjectorStoredMulOne
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    ComputedPreconditioner fp (columnSketchGramInverseProjector A Z) :=
  ComputedPreconditioner.ofComputedMatrix
    (ComputedMatrix.flMulOne fp (columnSketchGramInverseProjector A Z))

@[simp] theorem columnSketchGramInverseProjectorStoredMulOne_matrix
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    (columnSketchGramInverseProjectorStoredMulOne fp A Z).matrix =
      fun i k => fp.fl_mul (columnSketchGramInverseProjector A Z i k) 1 :=
  rfl

@[simp] theorem columnSketchGramInverseProjectorStoredMulOne_abs_error
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ) :
    (columnSketchGramInverseProjectorStoredMulOne fp A Z).abs_error =
      fun i k => fp.u * |columnSketchGramInverseProjector A Z i k| :=
  rfl

/-- Entrywise storage/copy error for the concrete rounded multiply-one
realization of the low-rank column-sketch Gram-inverse projector. -/
theorem columnSketchGramInverseProjectorStoredMulOne_entry_error_bound
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (i k : Fin m) :
    |(columnSketchGramInverseProjectorStoredMulOne fp A Z).matrix i k -
        columnSketchGramInverseProjector A Z i k| ≤
      fp.u * |columnSketchGramInverseProjector A Z i k| :=
  (columnSketchGramInverseProjectorStoredMulOne fp A Z).entry_abs_error_bound i k

/-- Implementation-facing entrywise error for applying the stored low-rank
Gram-inverse projector to the input matrix.

The algorithmic operations charged here are: rounded multiply-one storage of
every projector entry and the rounded length-`m` matrix product
`fl(P_hat A)`.  Sampling probabilities and laws are exact by convention, and
the exact projector itself remains the analysis reference. -/
theorem fl_columnSketchGramInverseProjectorStoredMulOne_preconditionRows_entry_error_bound
    (fp : FPModel) {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hm : gammaValid fp m) (i : Fin m) (j : Fin n) :
    |fl_preconditionRowsWithComputedLeft fp
        (columnSketchGramInverseProjectorStoredMulOne fp A Z) A i j -
      preconditionRows (columnSketchGramInverseProjector A Z) A i j| ≤
      gamma fp m *
          ∑ k : Fin m,
            |fp.fl_mul (columnSketchGramInverseProjector A Z i k) 1| *
              |A k j| +
        ∑ k : Fin m,
          (fp.u * |columnSketchGramInverseProjector A Z i k|) * |A k j| := by
  simpa [columnSketchGramInverseProjectorStoredMulOne,
    flPreconditionRowsWithComputedLeftEntryErrorBudget] using
    fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
      fp (columnSketchGramInverseProjectorStoredMulOne fp A Z) A hm i j

/-- Certificate for the source full-column-rank route
`C = (BᵀB)^{-1}Bᵀ`.  The inverse and symmetry fields are explicit because this
file does not yet construct `G^{-1}` from rank/SVD facts. -/
structure ColumnSketchGramInverseCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ) : Prop where
  inverse : IsInverse r (columnSketchGram A Z) Ginv
  symmetric_inverse : IsSymmetricFiniteMatrix Ginv

/-- A nonzero determinant of the exact sketch Gram matrix supplies the concrete
repository `nonsingInv` Gram-inverse certificate.  This is still an exact-object
route: it reduces LR.1 to proving the determinant/nonzero-full-rank condition,
not to computing the inverse in floating point. -/
theorem columnSketchGramInverseCertificate_of_det_ne_zero
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) where
  inverse :=
    isInverse_nonsingInv_of_det_ne_zero r (columnSketchGram A Z) hdet
  symmetric_inverse :=
    nonsingInv_symmetric_of_symmetric (columnSketchGram A Z)
      (columnSketchGram_symmetric A Z)

/-- Thin exact factorization certificate for the column sketch `B = A Z`.
The source SVD/QR route can instantiate this with `B = U R`, orthonormal
columns in `U`, and nonsingular square factor `R`. -/
structure ColumnSketchThinFactorCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ) : Prop where
  factorization :
    ∀ i a, columnSketch A Z i a = ∑ c : Fin r, U i c * R c a
  orthonormal_columns :
    ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b
  det_factor_ne_zero :
    Matrix.det (R : Matrix (Fin r) (Fin r) ℝ) ≠ 0


















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Exact source cross factor `Vᵀ Z`.  The sampling law for `Z` remains an
exact mathematical input; computing this product is a separate non-probability
FP obligation. -/
noncomputable def rightSketchCrossGram {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun a b => ∑ j : Fin n, V j a * Z j b





















































































































































namespace DiagonalSourceSVDTailCertificate



































end DiagonalSourceSVDTailCertificate


















































































































































































































































































































































































































































































































































/-- Linearity of the exact column sketch through an explicitly supplied
head/tail split. -/
theorem columnSketch_eq_add_of_eq_add
    {m n r : ℕ}
    (A B C : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = B i j + C i j) :
    ∀ i a, columnSketch A Z i a = columnSketch B Z i a + columnSketch C Z i a := by
  intro i a
  unfold columnSketch preconditionColumns
  calc
    (∑ k : Fin n, A i k * Z k a)
        = ∑ k : Fin n, (B i k + C i k) * Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hA i k]
    _ = ∑ k : Fin n, (B i k * Z k a + C i k * Z k a) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ =
          (∑ k : Fin n, B i k * Z k a) +
            ∑ k : Fin n, C i k * Z k a := by
            rw [Finset.sum_add_distrib]

/-- Linearity of the exact coefficient-generated sketch head through a supplied
head/tail split of the underlying sketch. -/
theorem columnSketchHead_eq_add_of_columnSketch_eq_add
    {m n r : ℕ}
    (A B C : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ)
    (hAZ :
      ∀ i a, columnSketch A Z i a = columnSketch B Z i a + columnSketch C Z i a) :
    ∀ i j,
      columnSketchHead A Z W i j =
        columnSketchHead B Z W i j + columnSketchHead C Z W i j := by
  intro i j
  unfold columnSketchHead
  calc
    (∑ a : Fin r, columnSketch A Z i a * W a j)
        =
          ∑ a : Fin r,
            (columnSketch B Z i a + columnSketch C Z i a) * W a j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hAZ i a]
    _ =
          ∑ a : Fin r,
            (columnSketch B Z i a * W a j +
              columnSketch C Z i a * W a j) := by
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ =
          (∑ a : Fin r, columnSketch B Z i a * W a j) +
            ∑ a : Fin r, columnSketch C Z i a * W a j := by
            rw [Finset.sum_add_distrib]














































































































































































































































































































































/-- Rectangular cross factor `Vperpᵀ Z` for the source tail coordinates. -/
noncomputable def rightSketchCrossGramRect {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a b => ∑ j : Fin n, Vperp j a * Z j b









/-- Dot-product budget for computing one entry of `Vperpᵀ Z` by
`flRightSketchCrossGramRect`. -/
noncomputable def rightSketchCrossGramRectDotBudget (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a b => gamma fp n * ∑ j : Fin n, |Vperp j a| * |Z j b|















































/-- Dot-product budget for the computed square cross Gram `fl((Vᵀ)Z)`. -/
noncomputable def rightSketchCrossGramDotBudget (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  rightSketchCrossGramRectDotBudget fp V Z




























































































































































/-- Exact factor `(Vperpᵀ Z)(Vᵀ Z)^{-1}` used after right-multiplying the
coordinate residual by the head right basis. -/
noncomputable def rightSketchCrossGramRectInvFactor {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a c =>
    ∑ b : Fin r,
      rightSketchCrossGramRect Vperp Z a b *
        nonsingInv r (rightSketchCrossGram V Z) b c


















































































































































































































































































































































































































/-- A selected right-Gram head index is orthogonal to every complement-tail
right index. -/
theorem rectRightGramSelectedIndexSet_head_tail_cross_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (a : Fin k)
    (c : Fin (((rectRightGramSelectedIndexSet e)ᶜ).card)) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A j
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c) =
      0 := by
  classical
  let s : Finset (Fin n) := rectRightGramSelectedIndexSet e
  have hmem : e a ∈ s := by
    simp [s, rectRightGramSelectedIndexSet]
  have htail_mem :
      (sᶜ).orderEmbOfFin rfl c ∈ sᶜ :=
    Finset.orderEmbOfFin_mem (sᶜ) rfl c
  have htail_not : (sᶜ).orderEmbOfFin rfl c ∉ s :=
    Finset.mem_compl.mp htail_mem
  have hne : e a ≠ (sᶜ).orderEmbOfFin rfl c := by
    intro h
    exact htail_not (by simpa [h] using hmem)
  change
    ∑ j : Fin n,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A j ((sᶜ).orderEmbOfFin rfl c) =
      0
  calc
    ∑ j : Fin n,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A j ((sᶜ).orderEmbOfFin rfl c)
        =
      idMatrix n (e a) ((sᶜ).orderEmbOfFin rfl c) := by
        simpa using
          rectRightGramEigenbasis_col_orthonormal A
            (e a) ((sᶜ).orderEmbOfFin rfl c)
    _ = 0 := by
        simp [idMatrix, hne]

/-- The complement-tail right index is orthogonal to every selected right-Gram
head index. -/
theorem rectRightGramSelectedIndexSet_tail_head_cross_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (c : Fin (((rectRightGramSelectedIndexSet e)ᶜ).card))
    (a : Fin k) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c) *
          rectRightGramEigenbasis A j (e a) =
      0 := by
  simpa [mul_comm] using
    rectRightGramSelectedIndexSet_head_tail_cross_zero A e a c

/-- The selected head plus complement-tail right tables are row-complete because
they partition the exact right-Gram eigenbasis. -/
theorem rectRightGramSelectedIndexSet_tail_head_row_complete
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (j l : Fin n) :
    (∑ c : Fin (((rectRightGramSelectedIndexSet e)ᶜ).card),
        rectRightGramEigenbasis A j
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c) *
          rectRightGramEigenbasis A l
            (((rectRightGramSelectedIndexSet e)ᶜ).orderEmbOfFin rfl c)) +
      (∑ a : Fin k,
        rectRightGramEigenbasis A j (e a) *
          rectRightGramEigenbasis A l (e a)) =
      idMatrix n j l := by
  classical
  let s : Finset (Fin n) := rectRightGramSelectedIndexSet e
  let term : Fin n → ℝ :=
    fun a => rectRightGramEigenbasis A j a * rectRightGramEigenbasis A l a
  change
    (∑ c : Fin ((sᶜ).card), term ((sᶜ).orderEmbOfFin rfl c)) +
      (∑ a : Fin k, term (e a)) =
      idMatrix n j l
  have htail :
      (sᶜ).sum term =
        ∑ c : Fin ((sᶜ).card), term ((sᶜ).orderEmbOfFin rfl c) :=
    rectRightGramComplement_sum_orderEmbOfFin s term
  have hhead :
      s.sum term = ∑ a : Fin k, term (e a) := by
    simpa [s] using rectRightGramSelectedIndexSet_sum e term
  rw [← htail, ← hhead]
  have hpartition :
      (sᶜ).sum term + s.sum term = ∑ a : Fin n, term a := by
    have h :
        s.sum term + (sᶜ).sum term = ∑ a : Fin n, term a := by
      rw [← Finset.sum_union disjoint_compl_right]
      rw [Finset.union_compl]
    simpa [add_comm] using h
  rw [hpartition]
  exact rectRightGramEigenbasis_row_orthonormal A j l

/-- The constructed ordered right-tail/head block has exact column
orthonormality. -/
theorem rectRightGramOrderedRightBasisBlock_col_orthonormal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    ∀ bc bd :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
      (∑ j : Fin n,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bc *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bd) =
        if bc = bd then 1 else 0 := by
  exact
    rightBasisBlock_col_orthonormal_of_component_orthonormal_fields
      (rectRightGramOrderedTailRight A hk)
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailRight_col_orthonormal A hk)
      (by
        intro b c
        simpa [rectRightGramOrderedTailRight, rectRightGramOrderedHeadRight,
          rectRightGramBasisSVDTailRight] using
          rectRightGramSelectedIndexSet_head_tail_cross_zero A
            (rectRightGramOrderedTopEmbedding hk) b c)
      (by
        intro c b
        simpa [rectRightGramOrderedTailRight, rectRightGramOrderedHeadRight,
          rectRightGramBasisSVDTailRight] using
          rectRightGramSelectedIndexSet_tail_head_cross_zero A
            (rectRightGramOrderedTopEmbedding hk) c b)
      (rectRightGramOrderedHeadRight_col_orthonormal A hk)

/-- The constructed ordered right-tail/head block has exact row
orthonormality, equivalently row completeness. -/
theorem rectRightGramOrderedRightBasisBlock_row_orthonormal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    ∀ j l,
      (∑ bc :
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bc *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) l bc) =
        idMatrix n j l := by
  exact
    rightBasisBlock_row_orthonormal_of_sum
      (rectRightGramOrderedTailRight A hk)
      (rectRightGramOrderedHeadRight A hk)
      (by
        intro j l
        simpa [rectRightGramOrderedTailRight, rectRightGramOrderedHeadRight,
          rectRightGramBasisSVDTailRight] using
          rectRightGramSelectedIndexSet_tail_head_row_complete A
            (rectRightGramOrderedTopEmbedding hk) j l)

/-- The constructed ordered right-tail/head block packages exact column
orthonormality and row completeness together. -/
theorem rectRightGramOrderedRightBasisBlock_col_row_orthonormal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    (∀ bc bd :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
      (∑ j : Fin n,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bc *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j bd) =
        if bc = bd then 1 else 0) ∧
      (∀ j l,
        (∑ bc :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ⊕ Fin k,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) l bc) =
          idMatrix n j l) := by
  exact
    ⟨rectRightGramOrderedRightBasisBlock_col_orthonormal A hk,
      rectRightGramOrderedRightBasisBlock_row_orthonormal A hk⟩





































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Under a thin factorization `B=U R` with orthonormal columns in `U`, the
exact sketch Gram matrix is entrywise `RᵀR`. -/
theorem columnSketchGram_eq_factorGram_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    ∀ a b,
      columnSketchGram A Z a b = ∑ c : Fin r, R c a * R c b := by
  intro a b
  unfold columnSketchGram
  calc
    (∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b)
        = ∑ i : Fin m,
            (∑ c : Fin r, U i c * R c a) *
              (∑ d : Fin r, U i d * R d b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hthin.factorization i a, hthin.factorization i b]
    _ = ∑ i : Fin m, ∑ c : Fin r, ∑ d : Fin r,
            (U i c * R c a) * (U i d * R d b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
    _ = ∑ c : Fin r, ∑ d : Fin r, ∑ i : Fin m,
            (U i c * R c a) * (U i d * R d b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_comm]
    _ = ∑ c : Fin r, ∑ d : Fin r,
            (∑ i : Fin m, U i c * U i d) * (R c a * R d b) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro d _
            calc
              (∑ i : Fin m, (U i c * R c a) * (U i d * R d b))
                  = ∑ i : Fin m, (U i c * U i d) * (R c a * R d b) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
              _ = (∑ i : Fin m, U i c * U i d) * (R c a * R d b) := by
                  rw [Finset.sum_mul]
    _ = ∑ c : Fin r, ∑ d : Fin r,
            idMatrix r c d * (R c a * R d b) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro d _
            rw [hthin.orthonormal_columns c d]
    _ = ∑ c : Fin r, R c a * R c b := by
            apply Finset.sum_congr rfl
            intro c _
            simp [idMatrix, Finset.mem_univ]

/-- A thin factorization `B=U R` with orthonormal columns and nonsingular `R`
implies the exact sketch Gram determinant is nonzero. -/
theorem columnSketchGram_det_ne_zero_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hentry :=
    columnSketchGram_eq_factorGram_of_thinFactorCertificate A Z U R hthin
  let RM : Matrix (Fin r) (Fin r) ℝ := R
  have hmat :
      (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        RM.transpose * RM := by
    ext a b
    rw [hentry a b]
    simp [RM, Matrix.mul_apply]
  have hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        Matrix.det RM * Matrix.det RM := by
    calc
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ)
          = Matrix.det (RM.transpose * RM) := by
              rw [hmat]
      _ = Matrix.det RM.transpose * Matrix.det RM := by
              rw [Matrix.det_mul]
      _ = Matrix.det RM * Matrix.det RM := by
              rw [Matrix.det_transpose]
  intro hzero
  have hprod : Matrix.det RM * Matrix.det RM = 0 := by
    simpa [hdet] using hzero
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exact hthin.det_factor_ne_zero hleft
  · exact hthin.det_factor_ne_zero hright




































/-- A thin factorization `B=U R` with orthonormal columns and nonsingular `R`
upgrades the exact sketch Gram from merely nonsingular to positive definite. -/
theorem columnSketchGram_posDef_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    Matrix.PosDef (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) := by
  have hentry :=
    columnSketchGram_eq_factorGram_of_thinFactorCertificate A Z U R hthin
  let RM : Matrix (Fin r) (Fin r) ℝ := R
  have hmat :
      (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        RM.transpose * RM := by
    ext a b
    rw [hentry a b]
    simp [RM, Matrix.mul_apply]
  rw [hmat]
  exact matrix_transpose_mul_self_posDef_of_det_ne_zero RM
    (by simpa [RM] using hthin.det_factor_ne_zero)

/-- A thin factorization certificate supplies the concrete repository
`nonsingInv` Gram-inverse certificate. -/
theorem columnSketchGramInverseCertificate_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) :=
  columnSketchGramInverseCertificate_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_thinFactorCertificate A Z U R hthin)

/-- For `C = G^{-1}Bᵀ`, the exact right multiplier `C B` is the identity when
`Ginv` is a left inverse of the sketch Gram matrix `G = BᵀB`. -/
theorem columnSketchRightMultiplier_eq_id_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ∀ a b,
      columnSketchRightMultiplier A Z
          (columnSketchGramInverseCoefficient A Z Ginv) a b =
        idMatrix r a b := by
  intro a b
  have hleft := hG.inverse.1 a b
  unfold columnSketchGram at hleft
  unfold columnSketchRightMultiplier columnSketchGramInverseCoefficient
    preconditionRows
  calc
    (∑ k : Fin m,
        (∑ c : Fin r, Ginv a c * columnSketch A Z k c) *
          columnSketch A Z k b)
        = ∑ c : Fin r, Ginv a c *
            (∑ k : Fin m, columnSketch A Z k c * columnSketch A Z k b) := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = idMatrix r a b := by
            simpa [idMatrix] using hleft

/-- The coefficient-side Moore-Penrose equation `C B C = C` for the exact
Gram-inverse coefficient table. -/
theorem columnSketchGramInverseCoefficient_reproducesCoeff
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ∀ a i,
      preconditionRows
          (columnSketchRightMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv))
          (columnSketchGramInverseCoefficient A Z Ginv) a i =
        columnSketchGramInverseCoefficient A Z Ginv a i := by
  intro a i
  have hCB :=
    columnSketchRightMultiplier_eq_id_of_gramInverseCertificate A Z Ginv hG
  unfold preconditionRows
  calc
    (∑ b : Fin r,
        columnSketchRightMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv) a b *
          columnSketchGramInverseCoefficient A Z Ginv b i)
        = ∑ b : Fin r,
            idMatrix r a b *
              columnSketchGramInverseCoefficient A Z Ginv b i := by
            apply Finset.sum_congr rfl
            intro b _
            rw [hCB a b]
    _ = columnSketchGramInverseCoefficient A Z Ginv a i := by
            simp [idMatrix, Finset.mem_univ]

/-- The exact multiplier `P = B G^{-1} Bᵀ` is symmetric when `G^{-1}` is
symmetric. -/
theorem columnSketchLeftMultiplier_symmetric_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    IsSymmetricFiniteMatrix
      (columnSketchLeftMultiplier A Z
        (columnSketchGramInverseCoefficient A Z Ginv)) := by
  intro i j
  unfold columnSketchLeftMultiplier columnSketchGramInverseCoefficient
  calc
    (∑ a : Fin r,
        columnSketch A Z i a *
          (∑ b : Fin r, Ginv a b * columnSketch A Z j b))
        = ∑ a : Fin r, ∑ b : Fin r,
            columnSketch A Z i a * (Ginv a b * columnSketch A Z j b) := by
            simp_rw [Finset.mul_sum]
    _ = ∑ b : Fin r, ∑ a : Fin r,
            columnSketch A Z i a * (Ginv a b * columnSketch A Z j b) := by
            rw [Finset.sum_comm]
    _ = ∑ b : Fin r, ∑ a : Fin r,
            columnSketch A Z j b * (Ginv b a * columnSketch A Z i a) := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            rw [hG.symmetric_inverse a b]
            ring
    _ = ∑ b : Fin r,
            columnSketch A Z j b *
              (∑ a : Fin r, Ginv b a * columnSketch A Z i a) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.mul_sum]

/-- The exact right multiplier `C B` for `C=G^{-1}Bᵀ` is symmetric because it
is the identity under the Gram-inverse certificate. -/
theorem columnSketchRightMultiplier_symmetric_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    IsSymmetricFiniteMatrix
      (columnSketchRightMultiplier A Z
        (columnSketchGramInverseCoefficient A Z Ginv)) := by
  intro a b
  have hCB :=
    columnSketchRightMultiplier_eq_id_of_gramInverseCertificate A Z Ginv hG
  rw [hCB a b, hCB b a]
  simp [idMatrix, eq_comm]

/-- The explicit multiplier `(A Z) C` factors through the exact column sketch
with coefficient table `C`. -/
noncomputable def columnSketchLeftMultiplier_leftFactorThrough {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z) where
  coeff := C
  factorization := by
    intro i j
    rfl

/-- The explicit coefficient multiplier `(A Z) C` gives a rank-at-most-`r`
projected approximation `(A Z) C A`. -/
theorem columnSketchLeftMultiplier_rankAtMost {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) :
    RectRankAtMost m n r
      (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  sketchColumnProjectorApprox_rankAtMost A Z (columnSketchLeftMultiplier A Z C)
    (columnSketchLeftMultiplier_leftFactorThrough A Z C)




































/-- Exact generalized-inverse certificate for the column sketch `B = A Z` and
coefficient table `C`: the multiplier `P_C = B C` reproduces the sketch,
equivalently `B C B = B`.  This is the algebraic condition a future
pseudoinverse construction must supply before the source projector `P_{A Z}`
can be used as an actual projector. -/
structure ColumnSketchGeneralizedInverse {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) : Prop where
  reproducesSketch :
    ∀ i a,
      preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
        columnSketch A Z i a

/-- A generalized-inverse coefficient table makes the exact multiplier
`P_C = (A Z) C` reproduce the column sketch. -/
theorem columnSketchLeftMultiplier_reproducesSketch_of_generalizedInverse
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchGeneralizedInverse A Z C) :
    ∀ i a,
      preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
        columnSketch A Z i a :=
  hC.reproducesSketch

/-- The exact generalized-inverse equation `B C B = B` for the Gram-inverse
coefficient table. -/
theorem columnSketchGramInverseCoefficient_generalizedInverse
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ColumnSketchGeneralizedInverse A Z
      (columnSketchGramInverseCoefficient A Z Ginv) where
  reproducesSketch := by
    intro i a
    have hCB :=
      columnSketchRightMultiplier_eq_id_of_gramInverseCertificate A Z Ginv hG
    unfold preconditionRows columnSketchLeftMultiplier
    calc
      (∑ k : Fin m,
          (∑ b : Fin r,
              columnSketch A Z i b *
                columnSketchGramInverseCoefficient A Z Ginv b k) *
            columnSketch A Z k a)
          = ∑ k : Fin m, ∑ b : Fin r,
              (columnSketch A Z i b *
                  columnSketchGramInverseCoefficient A Z Ginv b k) *
                columnSketch A Z k a := by
              simp_rw [Finset.sum_mul]
      _ = ∑ b : Fin r, ∑ k : Fin m,
              (columnSketch A Z i b *
                  columnSketchGramInverseCoefficient A Z Ginv b k) *
                columnSketch A Z k a := by
              rw [Finset.sum_comm]
      _ = ∑ b : Fin r,
              columnSketch A Z i b *
                (∑ k : Fin m,
                  columnSketchGramInverseCoefficient A Z Ginv b k *
                    columnSketch A Z k a) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = ∑ b : Fin r,
              columnSketch A Z i b *
                columnSketchRightMultiplier A Z
                  (columnSketchGramInverseCoefficient A Z Ginv) b a := by
              rfl
      _ = ∑ b : Fin r, columnSketch A Z i b * idMatrix r b a := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hCB b a]
      _ = columnSketch A Z i a := by
              simp [idMatrix, Finset.sum_ite_eq', Finset.mem_univ]

/-- A generalized-inverse coefficient table makes `P_C = (A Z) C` idempotent:
`P_C^2 = P_C`.  This is the exact projector algebra that will be needed once a
pseudoinverse or full-rank construction instantiates the certificate. -/
theorem columnSketchLeftMultiplier_idempotent_of_generalizedInverse {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchGeneralizedInverse A Z C) :
    ∀ i j,
      preconditionRows (columnSketchLeftMultiplier A Z C)
          (columnSketchLeftMultiplier A Z C) i j =
        columnSketchLeftMultiplier A Z C i j := by
  intro i j
  unfold preconditionRows columnSketchLeftMultiplier
  calc
    (∑ k : Fin m,
        (∑ a : Fin r, columnSketch A Z i a * C a k) *
          (∑ b : Fin r, columnSketch A Z k b * C b j))
        = ∑ k : Fin m, ∑ b : Fin r,
            ((∑ a : Fin r, columnSketch A Z i a * C a k) *
                columnSketch A Z k b) * C b j := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
    _ = ∑ b : Fin r, ∑ k : Fin m,
            ((∑ a : Fin r, columnSketch A Z i a * C a k) *
                columnSketch A Z k b) * C b j := by
              rw [Finset.sum_comm]
    _ = ∑ b : Fin r,
            (∑ k : Fin m,
              (∑ a : Fin r, columnSketch A Z i a * C a k) *
                columnSketch A Z k b) * C b j := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
    _ = ∑ b : Fin r, columnSketch A Z i b * C b j := by
              apply Finset.sum_congr rfl
              intro b _
              have hb := hC.reproducesSketch i b
              unfold preconditionRows columnSketchLeftMultiplier at hb
              rw [hb]

/-- Packaged exact projector surface for the coefficient multiplier
`P_C = (A Z) C`: it factors through the sketch, reproduces the sketch columns,
is idempotent, and gives a rank-at-most-`r` approximation `P_C A`.  Orthogonal
projector and pseudoinverse instantiations remain separate obligations. -/
theorem columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchGeneralizedInverse A Z C) :
    Nonempty (LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  ⟨⟨columnSketchLeftMultiplier_leftFactorThrough A Z C⟩,
    columnSketchLeftMultiplier_reproducesSketch_of_generalizedInverse A Z C hC,
    columnSketchLeftMultiplier_idempotent_of_generalizedInverse A Z C hC,
    columnSketchLeftMultiplier_rankAtMost A Z C⟩

/-- Exact orthogonal-projector certificate for the column sketch.  It combines
the generalized-inverse condition `B C B = B`, which gives reproduction and
idempotence for `P_C = B C`, with symmetry of the displayed multiplier.  This
is still a certificate surface: future pseudoinverse/full-rank infrastructure
must instantiate these fields for the particular `C = (A Z)^+`. -/
structure ColumnSketchOrthogonalProjectorCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) : Prop where
  generalizedInverse : ColumnSketchGeneralizedInverse A Z C
  symmetric :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C)

/-- The symmetry field of an exact column-sketch orthogonal-projector
certificate. -/
theorem columnSketchLeftMultiplier_symmetric_of_orthogonalProjectorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) :=
  hC.symmetric

/-- An exact column-sketch orthogonal-projector certificate makes
`P_C = (A Z) C` idempotent. -/
theorem columnSketchLeftMultiplier_idempotent_of_orthogonalProjectorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    ∀ i j,
      preconditionRows (columnSketchLeftMultiplier A Z C)
          (columnSketchLeftMultiplier A Z C) i j =
        columnSketchLeftMultiplier A Z C i j :=
  columnSketchLeftMultiplier_idempotent_of_generalizedInverse A Z C
    hC.generalizedInverse

/-- Packaged exact symmetric-idempotent projector surface for
`P_C = (A Z) C`: the multiplier is symmetric, reproduces the sketch, is
idempotent, factors through the sketch, and gives a rank-at-most-`r`
approximation `P_C A`. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty (LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  ⟨hC.symmetric,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).1,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).2.1,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).2.2.1,
    (columnSketchLeftMultiplier_projectorSurface_of_generalizedInverse A Z C
      hC.generalizedInverse).2.2.2⟩

/-- A symmetric idempotent row multiplier is Frobenius-nonexpansive on
rectangular matrices.  This is the row-wise orthogonal-projector contraction
needed for the CACM equation-(9) coupling term. -/
theorem frobNormSqRect_preconditionRows_le_of_symmetric_idempotent {m n : ℕ}
    (P : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : ∀ i j, preconditionRows P P i j = P i j) :
    frobNormSqRect (preconditionRows P A) ≤ frobNormSqRect A := by
  have hIdemFinite : ∀ i j, finiteMatMul P P i j = P i j := by
    intro i j
    simpa [finiteMatMul, preconditionRows] using hIdem i j
  unfold frobNormSqRect
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun i j => A i j ^ 2)]
  apply Finset.sum_le_sum
  intro j _
  have hcol :=
    finiteVecNorm2Sq_finiteMatVec_le_of_symmetric_idempotent
      P hSym hIdemFinite (fun i : Fin m => A i j)
  simpa [finiteVecNorm2Sq, finiteMatVec, preconditionRows] using hcol

/-- Norm form of row Frobenius nonexpansiveness for a symmetric idempotent
multiplier. -/
theorem frobNormRect_preconditionRows_le_of_symmetric_idempotent {m n : ℕ}
    (P : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : ∀ i j, preconditionRows P P i j = P i j) :
    frobNormRect (preconditionRows P A) ≤ frobNormRect A := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt
    (frobNormSqRect_preconditionRows_le_of_symmetric_idempotent
      P A hSym hIdem)

/-- Exact column-sketch orthogonal-projector certificates make the displayed
multiplier `(A Z) C` Frobenius-nonexpansive on every rectangular tail matrix.
This closes the projector-contractivity part of the equation-(9) coupling
term, while construction of the certificate remains a separate exact or
floating-point obligation. -/
theorem frobNormRect_preconditionRows_columnSketchLeftMultiplier_le_of_orthogonalProjectorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) (Tail : Fin m → Fin n → ℝ)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C) :
    frobNormRect (preconditionRows (columnSketchLeftMultiplier A Z C) Tail) ≤
      frobNormRect Tail :=
  frobNormRect_preconditionRows_le_of_symmetric_idempotent
    (columnSketchLeftMultiplier A Z C) Tail
    (columnSketchLeftMultiplier_symmetric_of_orthogonalProjectorCertificate
      A Z C hC)
    (columnSketchLeftMultiplier_idempotent_of_orthogonalProjectorCertificate
      A Z C hC)


























































/-- Certificate-shaped Moore-Penrose surface for a column sketch `B = A Z` and
a coefficient table `C`.  The fields are the four usual exact equations:
`B C B = B`, `C B C = C`, symmetry of `B C`, and symmetry of `C B`.

This is still not a construction or an existence theorem for `(A Z)^+`; it is
the exact certificate a future pseudoinverse/full-rank theorem or computed
routine may instantiate. -/
structure ColumnSketchMoorePenroseCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) : Prop where
  sketch_reproduction :
    ∀ i a,
      preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
        columnSketch A Z i a
  coefficient_reproduction :
    ∀ a i,
      preconditionRows (columnSketchRightMultiplier A Z C) C a i = C a i
  left_symmetric :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C)
  right_symmetric :
    IsSymmetricFiniteMatrix (columnSketchRightMultiplier A Z C)

/-- The `B C B = B` Moore-Penrose field is exactly the generalized-inverse
certificate already used by the equation (9) projector surface. -/
theorem ColumnSketchMoorePenroseCertificate.to_generalizedInverse {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {C : Fin r → Fin m → ℝ}
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    ColumnSketchGeneralizedInverse A Z C where
  reproducesSketch := hC.sketch_reproduction

/-- A Moore-Penrose certificate supplies the exact symmetric generalized-inverse
projector certificate for `P_C = (A Z) C`. -/
theorem ColumnSketchMoorePenroseCertificate.to_orthogonalProjectorCertificate
    {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {C : Fin r → Fin m → ℝ}
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    ColumnSketchOrthogonalProjectorCertificate A Z C where
  generalizedInverse := hC.to_generalizedInverse
  symmetric := hC.left_symmetric













































/-- The right-acting spectral certificate for the CACM source cross term.  If
the transpose action of
`(V_perp^T Z)(V_k^T Z)^{-1}` has operator-2 radius `eps`, then the Frobenius
cross term consumed by LR.1y/LR.1z/LR.1aa follows.

This is still exact-object: the operator certificate is supplied for the exact
rectangular cross factor.  Proving equivalence with an ordinary spectral-norm
certificate for the non-transposed factor remains a separate transpose-norm
foundation. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (rightSketchCrossGramRectInvFactor Vperp Z V))
        eps) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      eps * frobNorm Sigma :=
  frobNormRect_matMulRectLeft_le_of_transpose_rectOpNorm2Le
    Sigma (rightSketchCrossGramRectInvFactor Vperp Z V) heps hOp














































/-- Ordinary rectangular operator-2 certificate for the CACM source cross term.
This is the non-transposed form of the LR.1ab handoff: if the exact factor
`(V_perp^T Z)(V_k^T Z)^{-1}` has operator-2 radius `eps`, then the Frobenius
cross term consumed by LR.1y/LR.1z/LR.1aa follows. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_rectOpNorm2Le
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hOp :
      rectOpNorm2Le
        (rightSketchCrossGramRectInvFactor Vperp Z V)
        eps) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      eps * frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le
    Sigma Vperp Z V heps
    (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rightSketchCrossGramRectInvFactor Vperp Z V) heps hOp)













































/-- Computed-cross-factor perturbation certificate for the source cross term.

If an implementation supplies a computed non-probability cross factor `Mhat`
with an ordinary rectangular operator certificate and a Frobenius perturbation
radius to the exact analysis factor `M`, then the exact Frobenius cross term
has the enlarged radius `eps + tau`.  This is the local D5 transfer used when
cross products, inverses, and products are computed approximately while the
sampling law itself remains exact by convention. -/
theorem frobNormRect_sigma_exactFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (M Mhat : Fin q → Fin r → ℝ)
    {eps tau : ℝ}
    (heps : 0 ≤ eps)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hErr : frobNormRect (fun a b => M a b - Mhat a b) ≤ tau) :
    frobNormRect (matMulRectLeft Sigma M) ≤
      (eps + tau) * frobNorm Sigma := by
  let E : Fin q → Fin r → ℝ := fun a b => M a b - Mhat a b
  have hsplit :
      matMulRectLeft Sigma M =
        fun a b => matMulRectLeft Sigma Mhat a b + matMulRectLeft Sigma E a b := by
    ext a b
    unfold matMulRectLeft E
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hMhatCross :
      frobNormRect (matMulRectLeft Sigma Mhat) ≤ eps * frobNorm Sigma :=
    frobNormRect_matMulRectLeft_le_of_transpose_rectOpNorm2Le
      Sigma Mhat heps
      (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Mhat heps hMhat)
  have hE :
      frobNormRect (matMulRectLeft Sigma E) ≤ frobNorm Sigma * tau := by
    calc
      frobNormRect (matMulRectLeft Sigma E)
          ≤ frobNorm Sigma * frobNormRect E :=
            frobNormRect_matMulRectLeft_le Sigma E
      _ ≤ frobNorm Sigma * tau :=
            mul_le_mul_of_nonneg_left (by simpa [E] using hErr)
              (frobNorm_nonneg Sigma)
  calc
    frobNormRect (matMulRectLeft Sigma M)
        =
          frobNormRect
            (fun a b =>
              matMulRectLeft Sigma Mhat a b + matMulRectLeft Sigma E a b) := by
          rw [hsplit]
    _ ≤
        frobNormRect (matMulRectLeft Sigma Mhat) +
          frobNormRect (matMulRectLeft Sigma E) :=
        frobNormRect_add_le (matMulRectLeft Sigma Mhat) (matMulRectLeft Sigma E)
    _ ≤ eps * frobNorm Sigma + frobNorm Sigma * tau :=
        add_le_add hMhatCross hE
    _ = (eps + tau) * frobNorm Sigma := by ring

/-- CACM equation-(9) cross-term transfer from a computed non-probability cross
factor.  The exact factor is still
`(V_perp^T Z)(V_k^T Z)^{-1}`, but the implementation-facing hypotheses are an
operator certificate for the computed `Mhat` and a Frobenius perturbation
certificate comparing `Mhat` with that exact factor. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps tau : ℝ}
    (heps : 0 ≤ eps)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hErr :
      frobNormRect
          (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b -
            Mhat a b) ≤ tau) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + tau) * frobNorm Sigma :=
  frobNormRect_sigma_exactFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    Sigma (rightSketchCrossGramRectInvFactor Vperp Z V) Mhat heps hMhat hErr



























































/-- Entrywise-error instantiation of the computed-cross-factor certificate.

If a concrete routine bounds every entry of the exact CACM cross factor minus
the computed factor `Mhat` by `eta`, then the Frobenius perturbation radius in
LR.1ad may be chosen as `sqrt(q*r) * eta`. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_entry_abs_error
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps eta : ℝ}
    (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hEntry :
      ∀ a b,
        |rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b| ≤ eta) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * eta) * frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
    Sigma Vperp Z V Mhat heps hMhat
    (frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b)
      heta hEntry)
















































/-- Entrywise cross-factor error from component certificates for the computed
rectangular cross product and computed inverse factor.

Here `Xhat` is the computed version of `Vperpᵀ Z`, `Yhat` is the computed
version of `(Vᵀ Z)^{-1}`, and `Mhat` is the rounded product `Xhat * Yhat`.
The three radii separately charge the left input, right input, and final
product rounding. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {alpha beta rho : ℝ}
    (hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b - Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c, |(∑ b : Fin r, Xhat a b * Yhat b c) - Mhat a c| ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c - Mhat a c| ≤
        alpha + beta + rho := by
  intro a c
  unfold rightSketchCrossGramRectInvFactor
  exact
    rectMatMul_entry_abs_sub_computed_le_of_component_sums
      (rightSketchCrossGramRect Vperp Z) Xhat
      (nonsingInv r (rightSketchCrossGram V Z)) Yhat Mhat
      hLeft hRight hRound a c

/-- Cross-term certificate when the computed cross factor is assembled from
componentwise-certified computed cross-gram, inverse, and product data. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_component_error
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b - Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c, |(∑ b : Fin r, Xhat a b * Yhat b c) - Mhat a c| ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + beta + rho)) *
        frobNorm Sigma := by
  have heta : 0 ≤ alpha + beta + rho := by linarith
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_entry_abs_error
      Sigma Vperp Z V Mhat heps heta hMhat
      (rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
        Vperp Z V Xhat Yhat Mhat hLeft hRight hRound)













































































































/-- Adapter from an entrywise computed-inverse certificate to the `beta`
component sum used by the computed cross-factor theorem.

This theorem does not claim that any particular inverse routine has produced
`Yhat`. It says that once such a routine supplies the visible entrywise
certificate for the exact analysis inverse, the remaining LR.1af/LR.1ag right
component budget follows from a row absolute-sum budget on the computed left
factor. Sampling probabilities and laws remain exact mathematical inputs. -/
theorem rightSketchCrossGramRectInvFactor_inverse_component_sum_le_of_entry_abs_error
    {n q r : ℕ}
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eta chi : ℝ}
    (heta : 0 ≤ eta)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs : ∀ a, ∑ b : Fin r, |Xhat a b| ≤ chi) :
    ∀ a c,
      ∑ b : Fin r,
        |Xhat a b| *
          |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤
        chi * eta := by
  intro a c
  calc
    ∑ b : Fin r,
        |Xhat a b| *
          |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c|
        ≤ ∑ b : Fin r, |Xhat a b| * eta := by
          apply Finset.sum_le_sum
          intro b _
          exact mul_le_mul_of_nonneg_left (hInvEntry b c) (abs_nonneg _)
    _ = (∑ b : Fin r, |Xhat a b|) * eta := by
          rw [Finset.sum_mul]
    _ ≤ chi * eta :=
          mul_le_mul_of_nonneg_right (hXRowAbs a) heta

















































































































































































































































































































/-- Floating-point product used to assemble the computed equation-(9) cross
factor from a computed rectangular cross Gram `Xhat` and computed inverse
factor `Yhat`.  Sampling probabilities remain exact mathematical inputs; this
is only the non-probability matrix-product computation. -/
noncomputable def flRightSketchCrossGramRectInvFactorProduct
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fl_matMul fp q r r Xhat Yhat

/-- Entrywise dot-product budget for the final rounded product
`fl(Xhat * Yhat)`. -/
noncomputable def rightSketchCrossGramRectInvFactorProductDotBudget
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fun a c => gamma fp r * ∑ b : Fin r, |Xhat a b| * |Yhat b c|

/-- Entrywise floating-point error for the final rounded product
`fl(Xhat * Yhat)`. -/
theorem rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (hγ : gammaValid fp r) :
    ∀ a c,
      |(∑ b : Fin r, Xhat a b * Yhat b c) -
          flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat a c| ≤
        rightSketchCrossGramRectInvFactorProductDotBudget fp Xhat Yhat a c := by
  intro a c
  have hdot := matMul_error_bound fp q r r Xhat Yhat hγ a c
  simpa [flRightSketchCrossGramRectInvFactorProduct,
    rightSketchCrossGramRectInvFactorProductDotBudget, abs_sub_comm] using hdot

















































































































































































































































































































































/-- Entry magnitude of the concrete rounded product from a visible absolute
product sum and the `fl_matMul` dot-product error budget.  This is a
non-probability certificate source for the computed product itself. -/
theorem rightSketchCrossGramRectInvFactorProduct_entry_abs_le_of_product_sum_budget
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ) (Yhat : Fin r → Fin r → ℝ)
    {kappa rho : ℝ}
    (hγ : gammaValid fp r)
    (hProductAbs :
      ∀ a c, ∑ b : Fin r, |Xhat a b| * |Yhat b c| ≤ kappa)
    (hProductBudget :
      ∀ a c, rightSketchCrossGramRectInvFactorProductDotBudget fp Xhat Yhat a c ≤
        rho) :
    ∀ a c,
      |flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat a c| ≤
        kappa + rho := by
  intro a c
  let exactDot : ℝ := ∑ b : Fin r, Xhat a b * Yhat b c
  let Mhat : Fin q → Fin r → ℝ :=
    flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat
  have hRound : |exactDot - Mhat a c| ≤ rho := by
    exact le_trans
      (by
        simpa [exactDot, Mhat] using
          rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
            fp Xhat Yhat hγ a c)
      (hProductBudget a c)
  have hDotAbs :
      |exactDot| ≤ ∑ b : Fin r, |Xhat a b| * |Yhat b c| := by
    unfold exactDot
    calc
      |∑ b : Fin r, Xhat a b * Yhat b c|
          ≤ ∑ b : Fin r, |Xhat a b * Yhat b c| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b : Fin r, |Xhat a b| * |Yhat b c| := by
            apply Finset.sum_congr rfl
            intro b _
            exact abs_mul (Xhat a b) (Yhat b c)
  have hTri : |Mhat a c| ≤ |exactDot| + |exactDot - Mhat a c| := by
    calc
      |Mhat a c| = |Mhat a c - 0| := by ring_nf
      _ ≤ |Mhat a c - exactDot| + |exactDot - 0| :=
          abs_sub_le (Mhat a c) exactDot 0
      _ = |exactDot - Mhat a c| + |exactDot| := by
          rw [abs_sub_comm, sub_zero]
      _ = |exactDot| + |exactDot - Mhat a c| := by rw [add_comm]
  calc
    |flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat a c|
        = |Mhat a c| := by rfl
    _ ≤ |exactDot| + |exactDot - Mhat a c| := hTri
    _ ≤ kappa + rho :=
        add_le_add (le_trans hDotAbs (hProductAbs a c)) hRound

/-- Uniform absolute-product sums give a Frobenius certificate for the concrete
rounded product `fl_matMul Xhat Yhat`. -/
theorem frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
    (fp : FPModel) {q r : ℕ}
    (Xhat : Fin q → Fin r → ℝ) (Yhat : Fin r → Fin r → ℝ)
    {kappa rho : ℝ}
    (hkappa : 0 ≤ kappa) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp r)
    (hProductAbs :
      ∀ a c, ∑ b : Fin r, |Xhat a b| * |Yhat b c| ≤ kappa)
    (hProductBudget :
      ∀ a c, rightSketchCrossGramRectInvFactorProductDotBudget fp Xhat Yhat a c ≤
        rho) :
    frobNormRect
        (flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat) ≤
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) :=
  frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
    (flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat)
    (add_nonneg hkappa hrho)
    (rightSketchCrossGramRectInvFactorProduct_entry_abs_le_of_product_sum_budget
      fp Xhat Yhat hγ hProductAbs hProductBudget)

























































































































































/-- A perturbed-inverse certificate supplies an entrywise error certificate for
the repository nonsingular inverse.  This is a deterministic Higham §13.1
adapter: the concrete inversion routine is represented by the displayed
perturbed inverse equation for `Yhat`. -/
theorem nonsingInv_entry_abs_sub_computed_inverse_le_of_perturbed_inverse_component_budget
    {r : ℕ}
    (A Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsInv eta : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hdet : Matrix.det (A : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ i j, |DeltaA i j| ≤ epsInv * |A i j|)
    (hYhat :
      ∀ i j,
        ∑ k : Fin r, (A i k + DeltaA i k) * Yhat k j =
          if i = j then 1 else 0)
    (hBudget :
      ∀ i j,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r A i k₁| *
                (∑ k₂ : Fin r, |A k₁ k₂| * |Yhat k₂ j|) ≤ eta) :
    ∀ i j, |nonsingInv r A i j - Yhat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse r A (nonsingInv r A) :=
    isInverse_nonsingInv_of_det_ne_zero r A hdet
  exact le_trans
    (ideal_forward_error r A (nonsingInv r A) Yhat DeltaA epsInv hepsInv
      hDelta hInv.1 hInv.2 hYhat i j)
    (hBudget i j)

/-- Specialization of the perturbed-inverse adapter to the square cross Gram
`V_kᵀ Z` used in equation (9). -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_perturbed_inverse_component_budget
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsInv eta : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ b c,
        |DeltaA b c| ≤ epsInv * |rightSketchCrossGram V Z b c|)
    (hYhat :
      ∀ b c,
        ∑ k : Fin r,
          (rightSketchCrossGram V Z b k + DeltaA b k) * Yhat k c =
          if b = c then 1 else 0)
    (hBudget :
      ∀ b c,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  |rightSketchCrossGram V Z k₁ k₂| * |Yhat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta :=
  nonsingInv_entry_abs_sub_computed_inverse_le_of_perturbed_inverse_component_budget
    (rightSketchCrossGram V Z) Yhat DeltaA hepsInv hdet hDelta hYhat hBudget






















































































































































/-- Method-A LU inversion supplies the entrywise inverse certificate for the
square cross Gram `V_kᵀ Z` used in equation (9). -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {eta : ℝ}
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (gamma fp r))
    (hγr : gammaValid fp r)
    (hBudget :
      ∀ b c,
        (3 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_budget
    r fp (rightSketchCrossGram V Z) L_hat U_hat hdet
    hL_diag hU_diag hLU hγr hBudget

/-- Transfer an LU backward-error certificate from a computed square cross Gram
to the exact square cross Gram `VᵀZ`, when the input perturbation is measured
against the same `|L_hat||U_hat|` weights used by the LU certificate. -/
theorem rightSketchCrossGram_LUBackwardError_of_input_abs_error_le_absLUProduct
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ahat L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU mu : ℝ}
    (hLU : LUBackwardError r Ahat L_hat U_hat epsLU)
    (hInput :
      ∀ b c : Fin r,
        |Ahat b c - rightSketchCrossGram V Z b c| ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|) :
    LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (epsLU + mu) :=
  LUBackwardError.of_input_abs_error_le_absLUProduct r
    (rightSketchCrossGram V Z) Ahat L_hat U_hat epsLU mu hLU hInput

























/-- Method-A LU inversion with an exposed LU factorization coefficient supplies
the entrywise inverse certificate for the square cross Gram `V_kᵀ Z`. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU eta : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU : LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat epsLU)
    (hγr : gammaValid fp r)
    (hBudget :
      ∀ b c,
        (epsLU + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_factor_budget
    r fp (rightSketchCrossGram V Z) L_hat U_hat hepsLU hdet
    hL_diag hU_diag hLU hγr hBudget





























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- The exact Gram-inverse coefficient table `C = G^{-1}Bᵀ`, with
`G = BᵀB`, satisfies the four Moore-Penrose certificate equations under the
explicit Gram-inverse certificate. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z Ginv) where
  sketch_reproduction :=
    (columnSketchGramInverseCoefficient_generalizedInverse A Z Ginv hG).reproducesSketch
  coefficient_reproduction :=
    columnSketchGramInverseCoefficient_reproducesCoeff A Z Ginv hG
  left_symmetric :=
    columnSketchLeftMultiplier_symmetric_of_gramInverseCertificate A Z Ginv hG
  right_symmetric :=
    columnSketchRightMultiplier_symmetric_of_gramInverseCertificate A Z Ginv hG

/-- Determinant-facing Moore-Penrose route for the concrete coefficient table
`C = nonsingInv(BᵀB) Bᵀ`. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_det_ne_zero A Z hdet)

/-- Thin-factor-facing Moore-Penrose route for the concrete coefficient table
`C = nonsingInv(BᵀB) Bᵀ`. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_thinFactorCertificate A Z U R hthin)


/-- The coefficient-side Moore-Penrose equation `C B C = C`, exposed for later
pseudoinverse algebra and computed-routine certificates. -/
theorem columnSketchRightMultiplier_reproducesCoeff_of_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    ∀ a i,
      preconditionRows (columnSketchRightMultiplier A Z C) C a i = C a i :=
  hC.coefficient_reproduction

/-- The right Moore-Penrose symmetry equation for `C (A Z)`. -/
theorem columnSketchRightMultiplier_symmetric_of_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchRightMultiplier A Z C) :=
  hC.right_symmetric

/-- Packaged equation (9) projector surface obtained from a supplied
Moore-Penrose certificate.  This connects the four pseudoinverse equations to
the existing symmetric-idempotent rank surface, while leaving construction of
`C = (A Z)^+` and all computed non-probability routines as separate
obligations. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_moorePenroseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty (LeftFactorThrough (columnSketchLeftMultiplier A Z C) (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows (columnSketchLeftMultiplier A Z C) (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface A Z C
    hC.to_orthogonalProjectorCertificate

/-- Packaged equation (9) projector surface for the concrete exact
Gram-inverse coefficient table `C = (BᵀB)^{-1}Bᵀ`, assuming the displayed
Gram-inverse certificate. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_gramInverseCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (Ginv : Fin r → Fin r → ℝ)
    (hG : ColumnSketchGramInverseCertificate A Z Ginv) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z Ginv)) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z Ginv))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z Ginv))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z Ginv)) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z Ginv)) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_moorePenroseCertificate
    A Z (columnSketchGramInverseCoefficient A Z Ginv)
    (columnSketchGramInverseCoefficient_moorePenroseCertificate A Z Ginv hG)

/-- Determinant-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table `C = nonsingInv(BᵀB)Bᵀ`. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_det_ne_zero
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_gramInverseCertificate
    A Z (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_det_ne_zero A Z hdet)

/-- Thin-factor-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table `C = nonsingInv(BᵀB)Bᵀ`. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_thinFactorCertificate
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (R : Fin r → Fin r → ℝ)
    (hthin : ColumnSketchThinFactorCertificate A Z U R) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_gramInverseCertificate
    A Z (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_thinFactorCertificate A Z U R hthin)






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace BlockDiagonalSourceSVDTailCertificate


































































































































































































































































































































































































































































end BlockDiagonalSourceSVDTailCertificate


































/-- Tail-index type for the constructed ordered top-`k` complement.  This
abbreviation keeps the nullspace-completion statements readable while reducing
definitionally to the complement-cardinality `Fin` type used elsewhere. -/
abbrev rectRightGramOrderedTailIndex {n k : ℕ} (hk : k ≤ n) : Type :=
  Fin (((rectRightGramSelectedIndexSet
    (rectRightGramOrderedTopEmbedding hk))ᶜ).card)

/-- The constructed ordered top block together with its complement-tail index
type has ambient right cardinality `n`.  This exact arithmetic bridge is one of
the remaining reindexing dependencies for transporting the q-dimensional
Eckart--Young lower-bound theorem to the constructed ordered source split. -/
theorem rectRightGramOrderedTailIndex_card_add {n k : ℕ} (hk : k ≤ n) :
    k + Fintype.card (rectRightGramOrderedTailIndex hk) = n := by
  simpa [rectRightGramOrderedTailIndex, Fintype.card_fin] using
    rectRightGramSelectedIndexSet_card_add_compl_card
      (rectRightGramOrderedTopEmbedding hk)

/-- The canonical exact column map from the constructed ordered top-`k` block
and its complement-tail enumeration into the original right-coordinate domain.
This is reindexing infrastructure only; it computes no floating-point object. -/
noncomputable def rectRightGramOrderedHeadTailColumnMap {n k : ℕ}
    (hk : k ≤ n) :
    Fin k ⊕ rectRightGramOrderedTailIndex hk → Fin n
  | Sum.inl a => rectRightGramOrderedTopEmbedding hk a
  | Sum.inr c =>
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)

@[simp] theorem rectRightGramOrderedHeadTailColumnMap_inl {n k : ℕ}
    (hk : k ≤ n) (a : Fin k) :
    rectRightGramOrderedHeadTailColumnMap hk (Sum.inl a) =
      rectRightGramOrderedTopEmbedding hk a := rfl

@[simp] theorem rectRightGramOrderedHeadTailColumnMap_inr {n k : ℕ}
    (hk : k ≤ n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailColumnMap hk (Sum.inr c) =
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := rfl

/-- The constructed head-plus-complement-tail column map is injective. -/
theorem rectRightGramOrderedHeadTailColumnMap_injective {n k : ℕ}
    (hk : k ≤ n) :
    Function.Injective (rectRightGramOrderedHeadTailColumnMap hk) := by
  classical
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          have hab : a = b :=
            (rectRightGramOrderedTopEmbedding hk).injective (by
              simpa [rectRightGramOrderedHeadTailColumnMap] using hxy)
          simp [hab]
      | inr c =>
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          have hhead : rectRightGramOrderedTopEmbedding hk a ∈ s := by
            simp [s, rectRightGramSelectedIndexSet]
          have htail_mem : (sᶜ).orderEmbOfFin rfl c ∈ sᶜ :=
            Finset.orderEmbOfFin_mem (sᶜ) rfl c
          have htail_not : (sᶜ).orderEmbOfFin rfl c ∉ s :=
            Finset.mem_compl.mp htail_mem
          have hraw :
              rectRightGramOrderedTopEmbedding hk a =
                (sᶜ).orderEmbOfFin rfl c := by
            simpa [rectRightGramOrderedHeadTailColumnMap, s] using hxy
          exfalso
          exact htail_not (by simpa [hraw] using hhead)
  | inr c =>
      cases y with
      | inl a =>
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          have hhead : rectRightGramOrderedTopEmbedding hk a ∈ s := by
            simp [s, rectRightGramSelectedIndexSet]
          have htail_mem : (sᶜ).orderEmbOfFin rfl c ∈ sᶜ :=
            Finset.orderEmbOfFin_mem (sᶜ) rfl c
          have htail_not : (sᶜ).orderEmbOfFin rfl c ∉ s :=
            Finset.mem_compl.mp htail_mem
          have hraw :
              (sᶜ).orderEmbOfFin rfl c =
                rectRightGramOrderedTopEmbedding hk a := by
            simpa [rectRightGramOrderedHeadTailColumnMap, s] using hxy
          exfalso
          exact htail_not (by simpa [← hraw] using hhead)
      | inr d =>
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          have hraw :
              (sᶜ).orderEmbOfFin rfl c =
                (sᶜ).orderEmbOfFin rfl d := by
            simpa [rectRightGramOrderedHeadTailColumnMap, s] using hxy
          have hcd : c = d := ((sᶜ).orderEmbOfFin rfl).injective hraw
          simp [hcd]

/-- The constructed head-plus-complement-tail column map is surjective. -/
theorem rectRightGramOrderedHeadTailColumnMap_surjective {n k : ℕ}
    (hk : k ≤ n) :
    Function.Surjective (rectRightGramOrderedHeadTailColumnMap hk) := by
  classical
  intro j
  let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
  by_cases hj : j ∈ s
  · have hpre :
        ∃ a : Fin k, rectRightGramOrderedTopEmbedding hk a = j := by
      simpa [s, rectRightGramSelectedIndexSet] using hj
    rcases hpre with ⟨a, ha⟩
    exact ⟨Sum.inl a, by simpa [rectRightGramOrderedHeadTailColumnMap] using ha⟩
  · have hjc : j ∈ sᶜ := Finset.mem_compl.mpr hj
    let c : Fin ((sᶜ).card) := ((sᶜ).orderIsoOfFin rfl).symm ⟨j, hjc⟩
    have hc_sub : (sᶜ).orderIsoOfFin rfl c = ⟨j, hjc⟩ := by
      simp [c]
    have hc : (sᶜ).orderEmbOfFin rfl c = j := by
      change (((sᶜ).orderIsoOfFin rfl c : {x // x ∈ sᶜ}) : Fin n) = j
      exact congrArg Subtype.val hc_sub
    exact ⟨Sum.inr c, by
      simpa [rectRightGramOrderedHeadTailColumnMap, s] using hc⟩

/-- Exact equivalence from the constructed ordered head plus complement-tail
index sum to the original right-coordinate domain. -/
noncomputable def rectRightGramOrderedHeadTailColumnSumEquiv {n k : ℕ}
    (hk : k ≤ n) :
    Fin k ⊕ rectRightGramOrderedTailIndex hk ≃ Fin n :=
  Equiv.ofBijective (rectRightGramOrderedHeadTailColumnMap hk)
    ⟨rectRightGramOrderedHeadTailColumnMap_injective hk,
      rectRightGramOrderedHeadTailColumnMap_surjective hk⟩

@[simp] theorem rectRightGramOrderedHeadTailColumnSumEquiv_inl {n k : ℕ}
    (hk : k ≤ n) (a : Fin k) :
    rectRightGramOrderedHeadTailColumnSumEquiv hk (Sum.inl a) =
      rectRightGramOrderedTopEmbedding hk a := rfl

@[simp] theorem rectRightGramOrderedHeadTailColumnSumEquiv_inr {n k : ℕ}
    (hk : k ≤ n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailColumnSumEquiv hk (Sum.inr c) =
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := rfl

/-- Exact `Fin (k+q) ≃ Fin n` version of the constructed ordered
head-plus-complement-tail column equivalence, where
`q = |{ordered top-k indices}ᶜ|`. -/
noncomputable def rectRightGramOrderedHeadTailColumnEquiv {n k : ℕ}
    (hk : k ≤ n) :
    Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ≃ Fin n :=
  finSumFinEquiv.symm.trans (rectRightGramOrderedHeadTailColumnSumEquiv hk)

@[simp] theorem rectRightGramOrderedHeadTailColumnEquiv_head {n k : ℕ}
    (hk : k ≤ n) (a : Fin k) :
    rectRightGramOrderedHeadTailColumnEquiv hk (finSumFinEquiv (Sum.inl a)) =
      rectRightGramOrderedTopEmbedding hk a := by
  simp [rectRightGramOrderedHeadTailColumnEquiv]

@[simp] theorem rectRightGramOrderedHeadTailColumnEquiv_tail {n k : ℕ}
    (hk : k ≤ n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailColumnEquiv hk (finSumFinEquiv (Sum.inr c)) =
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := by
  simp [rectRightGramOrderedHeadTailColumnEquiv]

/-- Rank-at-most transport through the constructed ordered head-plus-tail
column equivalence. -/
theorem RectRankAtMost.reindexCols_rectRightGramOrderedHeadTailColumnEquiv
    {m n k r : ℕ} (hk : k ≤ n) {A : Fin m → Fin n → ℝ}
    (hA : RectRankAtMost m n r A) :
    RectRankAtMost m
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) r
      (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A) :=
  RectRankAtMost.reindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) hA

/-- Rank-at-most transports back from the constructed ordered head-plus-tail
column equivalence. -/
theorem RectRankAtMost.of_reindexCols_rectRightGramOrderedHeadTailColumnEquiv
    {m n k r : ℕ} (hk : k ≤ n) {A : Fin m → Fin n → ℝ}
    (hA : RectRankAtMost m
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) r
      (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A)) :
    RectRankAtMost m n r A :=
  RectRankAtMost.of_reindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) hA

/-- Frobenius residual invariance through the constructed ordered
head-plus-tail column equivalence. -/
theorem lowRankResidualFrob_rectRightGramOrderedHeadTailColumnEquiv
    {m n k : ℕ} (hk : k ≤ n) (A B : Fin m → Fin n → ℝ) :
    lowRankResidualFrob
        (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A)
        (rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) B) =
      lowRankResidualFrob A B :=
  lowRankResidualFrob_reindexCols
    (rectRightGramOrderedHeadTailColumnEquiv hk) A B

/-- Constructed ordered head-tail square gap.

For a nonempty constructed top-`k` block, the last selected top singular square
separates every selected head singular square from every complement-tail
singular square.  This is the exact-object gap certificate needed by the
source-factor LR.1dw bridge when the complement-tail enumeration is not itself
sorted.  It does not build the original-column reindexing/equivalence
transport, prove tail optimality, derive randomness, or certify computed
non-probability SVD/projector/Gram/sketch routines. -/
theorem rectRightGramOrdered_head_tail_square_gap
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k) :
    ∃ eta : ℝ,
      (∀ a : Fin k,
        eta ≤
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a) ^ 2) ∧
      ∀ c : rectRightGramOrderedTailIndex hk,
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ^ 2 ≤
          eta := by
  classical
  let last : Fin k := rectTopLastIndex hk0
  refine
    ⟨rectRightGramBasisSingularValue A
        (rectRightGramOrderedTopEmbedding hk last) ^ 2, ?_, ?_⟩
  · intro a
    have hlast_sq :
        rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last) ^ 2 =
          rectSingularValueSq A (rectTopIndex hk last) :=
      rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq
        A hk (rectRightGramOrderedTopEmbedding hk)
        (rectRightGramOrderedTopEmbedding_certificate A hk) last
    have ha_sq :
        rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a) ^ 2 =
          rectSingularValueSq A (rectTopIndex hk a) :=
      rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq
        A hk (rectRightGramOrderedTopEmbedding hk)
        (rectRightGramOrderedTopEmbedding_certificate A hk) a
    rw [hlast_sq, ha_sq]
    exact rectSingularValueSq_antitone A (rectTopIndex_le_last hk hk0 a)
  · intro c
    let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
    let b : Fin n := (sᶜ).orderEmbOfFin rfl c
    have hbmem : b ∈ sᶜ := by
      simp [b, Finset.orderEmbOfFin_mem]
    have hbnot : b ∉ s := Finset.mem_compl.mp hbmem
    have hle :
        rectRightGramBasisSingularValue A b ≤
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last) := by
      simpa [s, b] using
        rectRightGramOrderedTopEmbedding_complement_singularValue_le_selected
          A hk hbnot last
    have htail_nonneg : 0 ≤ rectRightGramBasisSingularValue A b :=
      rectRightGramBasisSingularValue_nonneg A b
    have hhead_nonneg :
        0 ≤
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last) :=
      rectRightGramBasisSingularValue_nonneg A
        (rectRightGramOrderedTopEmbedding hk last)
    have habs :
        |rectRightGramBasisSingularValue A b| ≤
          |rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk last)| := by
      simpa [abs_of_nonneg htail_nonneg, abs_of_nonneg hhead_nonneg] using hle
    have hsq := (sq_le_sq).mpr habs
    simpa [s, b, last] using hsq

/-- Partial left-block index set for the ordered nullspace-completion route:
all head columns are specified, and exactly the complement-tail columns with
nonzero singular value are specified.  Zero tail singular directions are left
free for orthonormal completion. -/
def rectRightGramOrderedNonzeroTailPartialSet {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Set (Fin k ⊕ rectRightGramOrderedTailIndex hk) :=
  fun bc =>
    match bc with
    | Sum.inl _ => True
    | Sum.inr c =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ≠ 0

@[simp] theorem rectRightGramOrderedNonzeroTailPartialSet_head {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (a : Fin k) :
    Sum.inl a ∈ rectRightGramOrderedNonzeroTailPartialSet A hk := by
  change True
  trivial

@[simp] theorem rectRightGramOrderedNonzeroTailPartialSet_tail_iff {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (c : rectRightGramOrderedTailIndex hk) :
    Sum.inr c ∈ rectRightGramOrderedNonzeroTailPartialSet A hk ↔
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ≠ 0 := by
  rfl

/-- On the ordered partial set consisting of all head columns and only nonzero
tail singular directions, the zero-safe head/tail left candidates are already a
partial orthonormal family.  This is the concrete `S` instantiation needed by
the nullspace-completion theorem; zero tail directions are deliberately absent
from the specified set. -/
theorem rectRightGramOrderedNonzeroTailPartialSet_leftBasisBlock_col_orthonormal_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0))) :
    ∀ a b : rectRightGramOrderedNonzeroTailPartialSet A hk,
      (∑ i : Fin m,
        leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i a *
          leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i b) =
        if a = b then 1 else 0 := by
  classical
  intro a b
  rcases a with ⟨bc, hbc⟩
  rcases b with ⟨bd, hbd⟩
  cases bc with
  | inl ca =>
      cases bd with
      | inl db =>
          have hhead :=
            rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
              A hk hk0 hlast ca db
          have hite :
              idMatrix k ca db =
                if (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inl db, hbd⟩ then 1 else 0 := by
            by_cases hcd : ca = db
            · subst db
              simp [idMatrix]
            · have hsub :
                  (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                    ⟨Sum.inl db, hbd⟩ := by
                intro hEq
                have hval : (Sum.inl ca :
                    Fin k ⊕ rectRightGramOrderedTailIndex hk) = Sum.inl db :=
                  congrArg Subtype.val hEq
                exact hcd (Sum.inl.inj hval)
              simp [idMatrix, hcd, hsub]
          calc
            (∑ i : Fin m,
              leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl ca) *
                leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl db))
                = idMatrix k ca db := by
                  simpa [leftBasisBlock] using hhead
            _ = if (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inl db, hbd⟩ then 1 else 0 := hite
      | inr db =>
          have hcross :=
            rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
              A hk hk0 hlast ca db
          have hsub :
              (⟨Sum.inl ca, hbc⟩ :
                rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                ⟨Sum.inr db, hbd⟩ := by
            intro hEq
            cases congrArg Subtype.val hEq
          calc
            (∑ i : Fin m,
              leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl ca) *
                leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inr db))
                = 0 := by
                  simpa [leftBasisBlock] using hcross
            _ = if (⟨Sum.inl ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inr db, hbd⟩ then 1 else 0 := by
                  simp [hsub]
  | inr ca =>
      cases bd with
      | inl db =>
          have hcross :=
            rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
              A hk hk0 hlast db ca
          have hsub :
              (⟨Sum.inr ca, hbc⟩ :
                rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                ⟨Sum.inl db, hbd⟩ := by
            intro hEq
            cases congrArg Subtype.val hEq
          calc
            (∑ i : Fin m,
              leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inr ca) *
                leftBasisBlock
                  (rectRightGramOrderedHeadLeft A hk)
                  (rectRightGramOrderedTailLeft A hk) i (Sum.inl db))
                =
                  ∑ i : Fin m,
                    rectRightGramOrderedHeadLeft A hk i db *
                      rectRightGramOrderedTailLeft A hk i ca := by
                    apply Finset.sum_congr rfl
                    intro i _
                    simp [leftBasisBlock]
                    ring
            _ = 0 := hcross
            _ = if (⟨Sum.inr ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inl db, hbd⟩ then 1 else 0 := by
                  simp [hsub]
      | inr db =>
          have hca_ne :
              rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl ca) ≠
                0 := by
            simpa using
              (rectRightGramOrderedNonzeroTailPartialSet_tail_iff A hk ca).mp hbc
          have hdb_ne :
              rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl db) ≠
                0 := by
            simpa using
              (rectRightGramOrderedNonzeroTailPartialSet_tail_iff A hk db).mp hbd
          have hca_pos :
              0 < rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl ca) :=
            lt_of_le_of_ne
              (rectRightGramBasisSingularValue_nonneg A _)
              (Ne.symm hca_ne)
          have hdb_pos :
              0 < rectRightGramBasisSingularValue A
                (((rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl db) :=
            lt_of_le_of_ne
              (rectRightGramBasisSingularValue_nonneg A _)
              (Ne.symm hdb_ne)
          let s := rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)
          let ec : Fin n := (sᶜ).orderEmbOfFin rfl ca
          let ed : Fin n := (sᶜ).orderEmbOfFin rfl db
          have horth :
              ∑ i : Fin m,
                  rectRightGramLeftSingularZeroSafe A i ec *
                    rectRightGramLeftSingularZeroSafe A i ed =
                idMatrix n ec ed :=
            rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
              A hca_pos hdb_pos
          have htail :
              (∑ i : Fin m,
                leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr ca) *
                  leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr db)) =
                idMatrix
                  (((rectRightGramSelectedIndexSet
                    (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ca db := by
            calc
              (∑ i : Fin m,
                leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr ca) *
                  leftBasisBlock
                    (rectRightGramOrderedHeadLeft A hk)
                    (rectRightGramOrderedTailLeft A hk) i (Sum.inr db))
                  = idMatrix n ec ed := by
                    simpa [leftBasisBlock, rectRightGramOrderedTailLeft,
                      rectRightGramBasisSVDTailLeft, s, ec, ed] using horth
              _ = idMatrix
                    (((rectRightGramSelectedIndexSet
                      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ca db := by
                    by_cases hcd : ca = db
                    · subst db
                      simp [idMatrix, ec, ed]
                    · have hne : ec ≠ ed := by
                        intro hEq
                        exact hcd (((sᶜ).orderEmbOfFin rfl).injective hEq)
                      simp [idMatrix, hcd, hne]
          have hite :
              idMatrix
                  (((rectRightGramSelectedIndexSet
                    (rectRightGramOrderedTopEmbedding hk))ᶜ).card) ca db =
                if (⟨Sum.inr ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) =
                    ⟨Sum.inr db, hbd⟩ then 1 else 0 := by
            by_cases hcd : ca = db
            · subst db
              simp [idMatrix]
            · have hsub :
                  (⟨Sum.inr ca, hbc⟩ :
                    rectRightGramOrderedNonzeroTailPartialSet A hk) ≠
                    ⟨Sum.inr db, hbd⟩ := by
                intro hEq
                have hval : (Sum.inr ca :
                    Fin k ⊕ rectRightGramOrderedTailIndex hk) = Sum.inr db :=
                  congrArg Subtype.val hEq
                exact hcd (Sum.inr.inj hval)
              simp [idMatrix, hcd, hsub]
          exact htail.trans hite










































































































































































































































































































































































































































/-- Head left singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDHeadLeft {r q : ℕ}
    (Ufull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin r → ℝ :=
  fun i a => Ufull i (Fin.castAdd q a)

/-- Tail left singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDTailLeft {r q : ℕ}
    (Ufull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin q → ℝ :=
  fun i c => Ufull i (Fin.natAdd r c)

/-- Head right singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDHeadRight {r q : ℕ}
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin r → ℝ :=
  fun j a => Vfull j (Fin.castAdd q a)

/-- Tail right singular-vector block obtained by splitting a square SVD table. -/
noncomputable def squareSVDTailRight {r q : ℕ}
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ) :
    Fin (r + q) → Fin q → ℝ :=
  fun j c => Vfull j (Fin.natAdd r c)

/-- Head diagonal singular-value block obtained by splitting a square SVD
table. -/
noncomputable def squareSVDHeadDiagonal {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) : Fin r → Fin r → ℝ :=
  fun a b => if a = b then sigma (Fin.castAdd q a) else 0

/-- Tail diagonal singular-value block obtained by splitting a square SVD
table. -/
noncomputable def squareSVDTailDiagonal {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) : Fin q → Fin q → ℝ :=
  fun c d => if c = d then sigma (Fin.natAdd r c) else 0























/-- Squared Frobenius norm of the constructed ordered complement-tail
singular-value block.

This is the constructed ordered-tail specialization needed before discharging
LR.1dt's visible Eckart--Young tail-optimality hypothesis.  It is exact-object
diagonal algebra only; computed singular values or singular-vector tables
remain non-probability implementation obligations. -/
theorem frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    frobNormSq (rectRightGramOrderedTailSingularDiagonal A hk) =
      ∑ c : rectRightGramOrderedTailIndex hk,
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ^ 2 := by
  simpa [rectRightGramOrderedTailSingularDiagonal,
    rectRightGramBasisSVDTailSingularDiagonal] using
    (frobNormSq_diagonal_eq_sum
      (fun c : rectRightGramOrderedTailIndex hk =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)))

/-- Norm form of
`frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum`. -/
theorem frobNorm_rectRightGramOrderedTailSingularDiagonal_eq_sqrt_sum
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) =
      Real.sqrt
        (∑ c : rectRightGramOrderedTailIndex hk,
          rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) ^ 2) := by
  rw [frobNorm_eq_sqrt_frobNormSq,
    frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum]

/-- Head-first `Fin (k+q)` left block for the constructed ordered source split,
where `q` is the complement-tail cardinality.  This is exact reindexing of the
analysis object only. -/
noncomputable def rectRightGramOrderedHeadTailLeftFinBlock {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ) :
    Fin m →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun i t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a => rectRightGramOrderedHeadLeft A hk i a
    | Sum.inr c => Utail i c

/-- Head-first `Fin (k+q)` singular-value table for the constructed ordered
source split. -/
noncomputable def rectRightGramOrderedHeadTailSigmaFin {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a)
    | Sum.inr c =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)

/-- Head-first `Fin (k+q)` right block for the constructed ordered source split,
with rows pulled back along the exact ordered head-tail column equivalence. -/
noncomputable def rectRightGramOrderedHeadTailRightFinBlock {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card) →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun j t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a =>
        rectRightGramOrderedHeadRight A hk
          (rectRightGramOrderedHeadTailColumnEquiv hk j) a
    | Sum.inr c =>
        rectRightGramOrderedTailRight A hk
          (rectRightGramOrderedHeadTailColumnEquiv hk j) c

/-- The same head-first right block before pulling rows back from the original
`Fin n` column domain to `Fin (k+q)`. -/
noncomputable def rectRightGramOrderedHeadTailRightOriginalFinBlock {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) :
    Fin n →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
  fun j t =>
    match finSumFinEquiv.symm t with
    | Sum.inl a => rectRightGramOrderedHeadRight A hk j a
    | Sum.inr c => rectRightGramOrderedTailRight A hk j c

theorem rectRightGramOrderedHeadTailRightFinBlock_eq_original
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j t : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    rectRightGramOrderedHeadTailRightFinBlock A hk j t =
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk
        (rectRightGramOrderedHeadTailColumnEquiv hk j) t := by
  cases h : finSumFinEquiv.symm t with
  | inl a =>
      simp [rectRightGramOrderedHeadTailRightFinBlock,
        rectRightGramOrderedHeadTailRightOriginalFinBlock, h]
  | inr c =>
      simp [rectRightGramOrderedHeadTailRightFinBlock,
        rectRightGramOrderedHeadTailRightOriginalFinBlock, h]

@[simp] theorem rectRightGramOrderedHeadTailLeftFinBlock_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (i : Fin m) (a : Fin k) :
    rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramOrderedHeadLeft A hk i a := by
  simp [rectRightGramOrderedHeadTailLeftFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailLeftFinBlock_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (i : Fin m) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i
        (Fin.natAdd k c) =
      Utail i c := by
  simp [rectRightGramOrderedHeadTailLeftFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailSigmaFin_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (a : Fin k) :
    rectRightGramOrderedHeadTailSigmaFin A hk
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramBasisSingularValue A
        (rectRightGramOrderedTopEmbedding hk a) := by
  simp [rectRightGramOrderedHeadTailSigmaFin]

@[simp] theorem rectRightGramOrderedHeadTailSigmaFin_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailSigmaFin A hk (Fin.natAdd k c) =
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) := by
  simp [rectRightGramOrderedHeadTailSigmaFin]

@[simp] theorem rectRightGramOrderedHeadTailRightFinBlock_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) (a : Fin k) :
    rectRightGramOrderedHeadTailRightFinBlock A hk j
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramOrderedHeadRight A hk
        (rectRightGramOrderedHeadTailColumnEquiv hk j) a := by
  simp [rectRightGramOrderedHeadTailRightFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailRightFinBlock_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card))
    (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailRightFinBlock A hk j (Fin.natAdd k c) =
      rectRightGramOrderedTailRight A hk
        (rectRightGramOrderedHeadTailColumnEquiv hk j) c := by
  simp [rectRightGramOrderedHeadTailRightFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_head
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin n) (a : Fin k) :
    rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j
        (Fin.castAdd
          ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) =
      rectRightGramOrderedHeadRight A hk j a := by
  simp [rectRightGramOrderedHeadTailRightOriginalFinBlock]

@[simp] theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_tail
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (j : Fin n) (c : rectRightGramOrderedTailIndex hk) :
    rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j (Fin.natAdd k c) =
      rectRightGramOrderedTailRight A hk j c := by
  simp [rectRightGramOrderedHeadTailRightOriginalFinBlock]

/-- The head-first `Fin (k+q)` left block inherits column orthonormality from
the sum-indexed constructed block. -/
theorem rectRightGramOrderedHeadTailLeftFinBlock_col_orthonormal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (hcols :
      ∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0)
    (a b : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    (∑ i : Fin m,
      rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i a *
        rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i b) =
      idMatrix
        (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
  have h := hcols (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  have hif :
      (if finSumFinEquiv.symm a = finSumFinEquiv.symm b then (1 : ℝ) else 0) =
        (if a = b then (1 : ℝ) else 0) := by
    by_cases hab : a = b
    · simp [hab]
    · have hsum : finSumFinEquiv.symm a ≠ finSumFinEquiv.symm b := by
        intro hsymm
        exact hab (finSumFinEquiv.symm.injective hsymm)
      simp [hab, hsum]
  trans
      (∑ i : Fin m,
        leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i
            (finSumFinEquiv.symm a) *
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i
            (finSumFinEquiv.symm b))
  · apply Finset.sum_congr rfl
    intro i _
    cases ha : finSumFinEquiv.symm a <;>
      cases hb : finSumFinEquiv.symm b <;>
      simp [rectRightGramOrderedHeadTailLeftFinBlock, leftBasisBlock, ha, hb]
  · simpa [idMatrix] using h.trans hif

/-- The head-first original right block inherits column orthonormality from the
tail-first right-basis block certificate. -/
theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_col_orthonormal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hcols :
      ∀ bc bd : rectRightGramOrderedTailIndex hk ⊕ Fin k,
        (∑ j : Fin n,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bd) =
          if bc = bd then 1 else 0)
    (a b : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card)) :
    (∑ j : Fin n,
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j a *
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j b) =
      idMatrix
        (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
  classical
  let swap :
      Fin k ⊕ rectRightGramOrderedTailIndex hk →
        rectRightGramOrderedTailIndex hk ⊕ Fin k :=
    fun bc =>
      match bc with
      | Sum.inl a => Sum.inr a
      | Sum.inr c => Sum.inl c
  have h := hcols (swap (finSumFinEquiv.symm a))
    (swap (finSumFinEquiv.symm b))
  have hif :
      (if swap (finSumFinEquiv.symm a) =
          swap (finSumFinEquiv.symm b) then (1 : ℝ) else 0) =
        (if a = b then (1 : ℝ) else 0) := by
    by_cases hab : a = b
    · simp [hab]
    · have hsymm : finSumFinEquiv.symm a ≠ finSumFinEquiv.symm b := by
        intro hsymm
        exact hab (finSumFinEquiv.symm.injective hsymm)
      have hswap :
          swap (finSumFinEquiv.symm a) ≠
            swap (finSumFinEquiv.symm b) := by
        intro hs
        apply hsymm
        cases ha : finSumFinEquiv.symm a <;>
          cases hb : finSumFinEquiv.symm b <;>
          simp [swap, ha, hb] at hs ⊢ <;>
          assumption
      simp [hab, hswap]
  trans
      (∑ j : Fin n,
        rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j
            (swap (finSumFinEquiv.symm a)) *
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
            (rectRightGramOrderedHeadRight A hk) j
            (swap (finSumFinEquiv.symm b)))
  · apply Finset.sum_congr rfl
    intro j _
    cases ha : finSumFinEquiv.symm a <;>
      cases hb : finSumFinEquiv.symm b <;>
      simp [rectRightGramOrderedHeadTailRightOriginalFinBlock,
        rightBasisBlock, swap, ha, hb]
  · simpa [idMatrix] using h.trans hif

/-- The head-first original right block inherits row orthonormality from the
tail-first right-basis row-completeness certificate. -/
theorem rectRightGramOrderedHeadTailRightOriginalFinBlock_row_orthonormal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hrows :
      ∀ j l,
        (∑ bc : rectRightGramOrderedTailIndex hk ⊕ Fin k,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) l bc) =
          idMatrix n j l)
    (j l : Fin n) :
    (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
      (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j t *
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk l t) =
      idMatrix n j l := by
  classical
  let term :
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    fun t =>
      rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j t *
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk l t
  have hsum :
      (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t) =
        ∑ bc : Fin k ⊕ rectRightGramOrderedTailIndex hk,
          term (finSumFinEquiv bc) := by
    exact
      (Fintype.sum_equiv finSumFinEquiv
        (fun bc : Fin k ⊕ rectRightGramOrderedTailIndex hk =>
          term (finSumFinEquiv bc))
        term
        (fun _ => rfl)).symm
  change (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
    (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t) =
      idMatrix n j l
  rw [hsum]
  rw [Fintype.sum_sum_type]
  have h := hrows j l
  rw [Fintype.sum_sum_type] at h
  simpa [term, rectRightGramOrderedHeadTailRightOriginalFinBlock,
    rightBasisBlock, add_comm] using h

/-- Pulling the head-first right block back along the ordered head-tail column
equivalence gives an orthogonal square table on `Fin (k+q)`. -/
theorem rectRightGramOrderedHeadTailRightFinBlock_isOrthogonal
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hcols :
      ∀ bc bd : rectRightGramOrderedTailIndex hk ⊕ Fin k,
        (∑ j : Fin n,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bd) =
          if bc = bd then 1 else 0)
    (hrows :
      ∀ j l,
        (∑ bc : rectRightGramOrderedTailIndex hk ⊕ Fin k,
          rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) j bc *
            rightBasisBlock (rectRightGramOrderedTailRight A hk)
              (rectRightGramOrderedHeadRight A hk) l bc) =
          idMatrix n j l) :
    IsOrthogonal
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      (rectRightGramOrderedHeadTailRightFinBlock A hk) := by
  constructor
  · intro a b
    unfold matTranspose
    let π := rectRightGramOrderedHeadTailColumnEquiv hk
    let f :
        Fin (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
      fun j =>
        rectRightGramOrderedHeadTailRightFinBlock A hk j a *
          rectRightGramOrderedHeadTailRightFinBlock A hk j b
    let g : Fin n → ℝ :=
      fun j =>
        rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j a *
          rectRightGramOrderedHeadTailRightOriginalFinBlock A hk j b
    have hsum :
        (∑ j : Fin (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card), f j) =
          ∑ j : Fin n, g j := by
      exact
        Fintype.sum_equiv π
          (fun j : Fin (k + ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) => f j)
          g
          (fun j => by
            simp [f, g, π,
              rectRightGramOrderedHeadTailRightFinBlock_eq_original])
    rw [hsum]
    exact
      rectRightGramOrderedHeadTailRightOriginalFinBlock_col_orthonormal
        A hk hcols a b
  · intro a b
    unfold matTranspose
    let π := rectRightGramOrderedHeadTailColumnEquiv hk
    calc
      (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        rectRightGramOrderedHeadTailRightFinBlock A hk a t *
          rectRightGramOrderedHeadTailRightFinBlock A hk b t)
          =
        ∑ t : Fin (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
          rectRightGramOrderedHeadTailRightOriginalFinBlock A hk (π a) t *
            rectRightGramOrderedHeadTailRightOriginalFinBlock A hk (π b) t := by
              apply Finset.sum_congr rfl
              intro t _
              simp [π, rectRightGramOrderedHeadTailRightFinBlock_eq_original]
      _ = idMatrix n (π a) (π b) :=
          rectRightGramOrderedHeadTailRightOriginalFinBlock_row_orthonormal
            A hk hrows (π a) (π b)
      _ =
        idMatrix
          (k + ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
          by_cases h : a = b
          · simp [idMatrix, h]
          · have hp : π a ≠ π b := by
              intro hp
              exact h (π.injective hp)
            simp [idMatrix, h, hp]







































































































































































































































































































































































































theorem frobNormSq_squareSVDTailDiagonal_eq_sum {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) :
    frobNormSq (squareSVDTailDiagonal (r := r) (q := q) sigma) =
      ∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2 := by
  simpa [squareSVDTailDiagonal] using
    (frobNormSq_diagonal_eq_sum
      (fun c : Fin q => sigma (Fin.natAdd r c)))

/-- Norm form of `frobNormSq_squareSVDTailDiagonal_eq_sum`. -/
theorem frobNorm_squareSVDTailDiagonal_eq_sqrt_sum {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) :
    frobNorm (squareSVDTailDiagonal (r := r) (q := q) sigma) =
      Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) := by
  rw [frobNorm_eq_sqrt_frobNormSq,
    frobNormSq_squareSVDTailDiagonal_eq_sum]

/-- Head singular values obtained by splitting a square SVD table. -/
noncomputable def squareSVDHeadValues {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) : Fin r → ℝ :=
  fun a => sigma (Fin.castAdd q a)

/-- Strict positivity of the displayed head singular entries is inherited by
the split head-value table. -/
theorem squareSVDHeadValues_pos {r q : ℕ}
    {sigma : Fin (r + q) → ℝ}
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    ∀ a : Fin r, 0 < squareSVDHeadValues sigma a := by
  intro a
  simpa [squareSVDHeadValues] using hhead_pos a

/-- Source-style strict positivity of the displayed head singular entries
supplies the nonzero-head field used by the determinant/source-SVD
constructors. -/
theorem squareSVDHeadValues_nonzero_of_pos {r q : ℕ}
    {sigma : Fin (r + q) → ℝ}
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0 := by
  intro a
  exact ne_of_gt (hhead_pos a)






















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Head left singular-vector block obtained by splitting a thin rectangular
SVD table. -/
noncomputable def rectangularThinSVDHeadLeft {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ) : Fin m → Fin r → ℝ :=
  fun i a => Ufull i (Fin.castAdd q a)

/-- Tail left singular-vector block obtained by splitting a thin rectangular
SVD table. -/
noncomputable def rectangularThinSVDTailLeft {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ) : Fin m → Fin q → ℝ :=
  fun i c => Ufull i (Fin.natAdd r c)












































































































































































































































































































































































































































/-- A one-column tail diagonal has Frobenius norm equal to its single
nonnegative displayed singular value.

This is exact-object diagonal algebra for the equation-(9) one-step
coefficient block; it does not model a computed singular-value routine. -/
theorem frobNorm_squareSVDTailDiagonal_one {r : ℕ}
    (sigma : Fin (r + 1) → ℝ)
    (hsigma_tail : 0 ≤ sigma (Fin.natAdd r (0 : Fin 1))) :
    frobNorm (squareSVDTailDiagonal (r := r) (q := 1) sigma) =
      sigma (Fin.natAdd r (0 : Fin 1)) := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  unfold frobNormSq squareSVDTailDiagonal
  simp [hsigma_tail]










































































































































































































































































































































































































































































































































































































































































































end NumStability
