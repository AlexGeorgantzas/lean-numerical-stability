-- Analysis/MatrixSpectral.lean
--
-- Lightweight bridges from the repository's finite real matrix predicates to
-- mathlib's Hermitian spectral API.

import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Instances.Matrix

namespace LeanFpAnalysis.FP

open scoped BigOperators ComplexOrder

/-- Eigenvalues of a repository-native finite real symmetric matrix, routed
    through mathlib's Hermitian spectral API. -/
noncomputable def finiteHermitianEigenvalues {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) : ι → ℝ :=
  (IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).eigenvalues

/-- The locally named eigenvalues are members of mathlib's real matrix
    spectrum. -/
theorem finiteHermitianEigenvalues_mem_spectrum_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (i : ι) :
    finiteHermitianEigenvalues M hM i ∈
      @spectrum ℝ (Matrix ι ι ℝ) _ Matrix.instRing Matrix.instAlgebra M := by
  simpa [finiteHermitianEigenvalues] using
    Matrix.IsHermitian.eigenvalues_mem_spectrum_real
      (IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM) i

/-- Trace equals the sum of the locally named Hermitian eigenvalues. -/
theorem finiteTrace_eq_sum_finiteHermitianEigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    finiteTrace M = ∑ i : ι, finiteHermitianEigenvalues M hM i := by
  have htrace := Matrix.IsHermitian.trace_eq_sum_eigenvalues
    (A := (M : Matrix ι ι ℝ))
    (IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM)
  simpa [finiteTrace, finiteHermitianEigenvalues, Matrix.trace] using htrace

/-- Matrix exponential of a repository-native finite real matrix, routed through
    mathlib's matrix exponential.  This is the common interface for future
    trace-MGF / matrix concentration proofs. -/
noncomputable def finiteMatrixExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) : ι → ι → ℝ :=
  (@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
    (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
    (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
    (M : Matrix ι ι ℝ) : Matrix ι ι ℝ)

/-- The matrix exponential of `L I` is `exp(L) I`.  The statement is written
    in the repository's finite-matrix representation and with `Real.exp`, so it
    can be used directly in trace-MGF bounds. -/
theorem finiteMatrixExp_smul_finiteIdMatrix {ι : Type*}
    [Fintype ι] [DecidableEq ι] (L : ℝ) :
    finiteMatrixExp (fun i j : ι => L * finiteIdMatrix i j) =
      fun i j : ι => Real.exp L * finiteIdMatrix i j := by
  ext i j
  letI : IsTopologicalRing (Matrix ι ι ℝ) := Matrix.topologicalRing
  have h := Matrix.exp_diagonal (m := ι) (𝔸 := ℝ) (fun _ : ι => L)
  simpa [finiteMatrixExp, finiteIdMatrix, Matrix.diagonal, ← Real.exp_eq_exp_ℝ] using
    congrFun (congrFun h i) j

/-- The trace of the matrix exponential of `L I` is `d exp(L)`.  This is the
    scalar normalization term that appears in finite-dimensional
    trace-exponential tail bounds. -/
theorem finiteTrace_finiteMatrixExp_smul_finiteIdMatrix {ι : Type*}
    [Fintype ι] [DecidableEq ι] (L : ℝ) :
    finiteTrace (finiteMatrixExp (fun i j : ι => L * finiteIdMatrix i j)) =
      (Fintype.card ι : ℝ) * Real.exp L := by
  rw [finiteMatrixExp_smul_finiteIdMatrix (ι := ι) L]
  rw [finiteTrace_smul_finiteIdMatrix]
  ring

/-- The matrix exponential of a local finite real symmetric matrix is
    symmetric.  This keeps trace-exponential arguments inside the repository's
    finite-matrix predicate vocabulary after using mathlib's exponential API. -/
theorem finiteMatrixExp_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    IsSymmetricFiniteMatrix (finiteMatrixExp M) := by
  apply Matrix_isSymm.to_IsSymmetricFiniteMatrix
  letI : IsTopologicalRing (Matrix ι ι ℝ) := Matrix.topologicalRing
  have h := Matrix.IsSymm.exp (IsSymmetricFiniteMatrix.to_matrix_isSymm M hM)
  simpa [finiteMatrixExp] using h

/-- The matrix exponential of a finite diagonal matrix is the diagonal matrix
    of entrywise exponentials. -/
theorem finiteMatrixExp_finiteDiagonal {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    finiteMatrixExp (finiteDiagonal v) =
      finiteDiagonal (fun i => Real.exp (v i)) := by
  ext i j
  letI : IsTopologicalRing (Matrix ι ι ℝ) := Matrix.topologicalRing
  have h := Matrix.exp_diagonal (m := ι) (𝔸 := ℝ) v
  simpa [finiteMatrixExp, finiteDiagonal, Matrix.diagonal, ← Real.exp_eq_exp_ℝ] using
    congrFun (congrFun h i) j

/-- Trace of the matrix exponential of a finite diagonal matrix is the sum of
    the scalar exponentials on the diagonal. -/
theorem finiteTrace_finiteMatrixExp_finiteDiagonal {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    finiteTrace (finiteMatrixExp (finiteDiagonal v)) =
      ∑ i : ι, Real.exp (v i) := by
  rw [finiteMatrixExp_finiteDiagonal]
  unfold finiteTrace finiteDiagonal
  simp

/-- Hermitian continuous-functional-calculus exponential for a repository-native
    finite real symmetric matrix.  This is a spectral-calculus bridge for future
    trace-MGF arguments; the power-series matrix exponential is still exposed
    separately as `finiteMatrixExp`. -/
noncomputable def finiteHermitianCfcExp {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) : ι → ι → ℝ :=
  (IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).cfc Real.exp

/-- Trace of the Hermitian CFC exponential is the sum of scalar exponentials of
    the Hermitian eigenvalues.  This is the diagonalized trace identity needed
    before a trace-exponential MGF proof can be stated cleanly. -/
theorem finiteTrace_finiteHermitianCfcExp_eq_sum_exp_finiteHermitianEigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    finiteTrace (finiteHermitianCfcExp M hM) =
      ∑ i : ι, Real.exp (finiteHermitianEigenvalues M hM i) := by
  have hherm : Matrix.IsHermitian (M : Matrix ι ι ℝ) :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  change finiteTrace (hherm.cfc Real.exp) =
    ∑ i : ι, Real.exp (finiteHermitianEigenvalues M hM i)
  change Matrix.trace (hherm.cfc Real.exp) =
    ∑ i : ι, Real.exp (finiteHermitianEigenvalues M hM i)
  rw [Matrix.IsHermitian.cfc]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp [finiteHermitianEigenvalues]

/-- Trace of the repository-native power-series matrix exponential is the sum
    of scalar exponentials of the Hermitian eigenvalues.  The proof pins the
    exponential to mathlib's matrix ring instance, diagonalizes the symmetric
    matrix by the Hermitian spectral theorem, and then uses trace cyclicity.
    This is the trace-diagonalization foundation needed before a
    trace-exponential largest-eigenvalue proof can be formalized. -/
theorem finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    finiteTrace (finiteMatrixExp M) =
      ∑ i : ι, Real.exp (finiteHermitianEigenvalues M hM i) := by
  let hherm : Matrix.IsHermitian (M : Matrix ι ι ℝ) :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  let Uu := hherm.eigenvectorUnitary
  let U : (Matrix ι ι ℝ)ˣ := Unitary.toUnits Uu
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i : ι => hherm.eigenvalues i)
  have hstar : star (Uu : Matrix ι ι ℝ) =
      ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    change star (Uu : Matrix ι ι ℝ) = ↑(Uu⁻¹ : Matrix.unitaryGroup ι ℝ)
    rw [← Unitary.coe_star, Unitary.star_eq_inv]
  have hspectral :
      (M : Matrix ι ι ℝ) =
        (↑U : Matrix ι ι ℝ) * D *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    rw [hherm.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rw [hstar]
    rfl
  have hexp :
      (@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
          (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
          (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
          (M : Matrix ι ι ℝ) : Matrix ι ι ℝ) =
        (↑U : Matrix ι ι ℝ) *
          (@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
            (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
            (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
            D : Matrix ι ι ℝ) *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    rw [hspectral]
    exact Matrix.exp_units_conj U D
  unfold finiteMatrixExp finiteTrace
  change Matrix.trace
      ((@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
          (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
          (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
          (M : Matrix ι ι ℝ) : Matrix ι ι ℝ)) =
    ∑ i : ι, Real.exp (finiteHermitianEigenvalues M hM i)
  rw [hexp]
  rw [Matrix.trace_mul_cycle]
  simp [D, U, Uu, finiteHermitianEigenvalues, Matrix.exp_diagonal,
    ← Real.exp_eq_exp_ℝ]

/-- Trace of the matrix exponential of `-M`, diagonalized using the Hermitian
    eigenvalues of `M`.  This is the lower-tail companion to
    `finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues`. -/
theorem finiteTrace_finiteMatrixExp_neg_eq_sum_exp_neg_finiteHermitianEigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    finiteTrace (finiteMatrixExp (fun i j => -M i j)) =
      ∑ i : ι, Real.exp (-(finiteHermitianEigenvalues M hM i)) := by
  let hherm : Matrix.IsHermitian (M : Matrix ι ι ℝ) :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  let Uu := hherm.eigenvectorUnitary
  let U : (Matrix ι ι ℝ)ˣ := Unitary.toUnits Uu
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i : ι => hherm.eigenvalues i)
  have hstar : star (Uu : Matrix ι ι ℝ) =
      ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    change star (Uu : Matrix ι ι ℝ) = ↑(Uu⁻¹ : Matrix.unitaryGroup ι ℝ)
    rw [← Unitary.coe_star, Unitary.star_eq_inv]
  have hspectral :
      (M : Matrix ι ι ℝ) =
        (↑U : Matrix ι ι ℝ) * D *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    rw [hherm.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rw [hstar]
    rfl
  have hneg_spectral :
      ((fun i j : ι => -M i j) : Matrix ι ι ℝ) =
        (↑U : Matrix ι ι ℝ) * (-D) *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    have hneg :
        ((fun i j : ι => -M i j) : Matrix ι ι ℝ) = -(M : Matrix ι ι ℝ) := by
      ext i j
      rfl
    rw [hneg, hspectral]
    noncomm_ring
  have hexp :
      (@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
          (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
          (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
          ((fun i j : ι => -M i j) : Matrix ι ι ℝ) : Matrix ι ι ℝ) =
        (↑U : Matrix ι ι ℝ) *
          (@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
            (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
            (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
            (-D) : Matrix ι ι ℝ) *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    rw [hneg_spectral]
    exact Matrix.exp_units_conj U (-D)
  unfold finiteMatrixExp finiteTrace
  change Matrix.trace
      ((@NormedSpace.exp (Matrix ι ι ℝ) Matrix.instRing
          (inferInstance : TopologicalSpace (Matrix ι ι ℝ))
          (inferInstance : IsTopologicalRing (Matrix ι ι ℝ))
          ((fun i j : ι => -M i j) : Matrix ι ι ℝ) : Matrix ι ι ℝ)) =
    ∑ i : ι, Real.exp (-(finiteHermitianEigenvalues M hM i))
  rw [hexp]
  rw [Matrix.trace_mul_cycle]
  simp [D, U, Uu, finiteHermitianEigenvalues, Matrix.exp_diagonal,
    ← Real.exp_eq_exp_ℝ]

/-- The quadratic form of a symmetric matrix on one of its Hermitian
    eigenvectors is the corresponding eigenvalue times the squared vector
    norm. -/
theorem finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : ι) :
    finiteQuadraticForm M
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).eigenvectorBasis a)) =
      finiteHermitianEigenvalues M hM a *
        finiteVecNorm2Sq
          (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).eigenvectorBasis a)) := by
  let hherm : Matrix.IsHermitian (M : Matrix ι ι ℝ) :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  let v : ι → ℝ := ⇑(hherm.eigenvectorBasis a)
  have hmul := hherm.mulVec_eigenvectorBasis a
  change finiteQuadraticForm M v =
    finiteHermitianEigenvalues M hM a * finiteVecNorm2Sq v
  unfold finiteQuadraticForm finiteMatVec finiteVecNorm2Sq finiteHermitianEigenvalues
  change (∑ i : ι, v i * Matrix.mulVec (M : Matrix ι ι ℝ) v i) =
    hherm.eigenvalues a * ∑ i : ι, v i ^ 2
  rw [hmul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [v, pow_two, mul_left_comm]

/-- The locally named Hermitian eigenvectors are unit vectors in the
    repository's finite squared-norm convention. -/
theorem finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : ι) :
    finiteVecNorm2Sq
        (⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).eigenvectorBasis a)) =
      1 := by
  let hherm : Matrix.IsHermitian (M : Matrix ι ι ℝ) :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  let v : ι → ℝ := ⇑(hherm.eigenvectorBasis a)
  have hnorm := hherm.eigenvectorBasis.orthonormal.1 a
  have hsq : ‖hherm.eigenvectorBasis a‖ ^ 2 = (1 : ℝ) := by
    rw [hnorm]
    norm_num
  rw [EuclideanSpace.norm_sq_eq] at hsq
  change finiteVecNorm2Sq v = 1
  unfold finiteVecNorm2Sq
  simpa [v, sq_abs] using hsq

/-- A scalar-identity Loewner upper bound controls every locally named
    Hermitian eigenvalue. -/
theorem finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) {c : ℝ}
    (hLe : finiteLoewnerLe M (fun i j => c * finiteIdMatrix i j)) (a : ι) :
    finiteHermitianEigenvalues M hM a ≤ c := by
  let v : ι → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).eigenvectorBasis a)
  have hq := hLe v
  have heig :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      M hM a
  have hnorm :=
    finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one M hM a
  change finiteQuadraticForm M v ≤
    finiteQuadraticForm (fun i j => c * finiteIdMatrix i j) v at hq
  rw [heig, finiteQuadraticForm_smul_finiteIdMatrix, hnorm] at hq
  simpa using hq

/-- Conversely, a pointwise upper bound on all locally named Hermitian
    eigenvalues gives the scalar-identity Loewner upper bound.  This is the
    deterministic spectral adapter used after a largest-eigenvalue tail event:
    it converts the event `lambda_max(M) <= L`, stated with
    `finiteHermitianEigenvalues`, into the repository-native quadratic-form
    Loewner predicate. -/
theorem finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) {L : ℝ}
    (hEig : ∀ a : ι, finiteHermitianEigenvalues M hM a ≤ L) :
    finiteLoewnerLe M (fun i j => L * finiteIdMatrix i j) := by
  let Mmat : Matrix ι ι ℝ := M
  let hherm : Matrix.IsHermitian Mmat :=
    IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
  let Uu := hherm.eigenvectorUnitary
  let U : (Matrix ι ι ℝ)ˣ := Unitary.toUnits Uu
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i : ι => hherm.eigenvalues i)
  let S : Matrix ι ι ℝ := Matrix.diagonal (fun _ : ι => L)
  let Ddiff : Matrix ι ι ℝ :=
    Matrix.diagonal (fun i : ι => L - hherm.eigenvalues i)
  have hstar : star (Uu : Matrix ι ι ℝ) =
      ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    change star (Uu : Matrix ι ι ℝ) = ↑(Uu⁻¹ : Matrix.unitaryGroup ι ℝ)
    rw [← Unitary.coe_star, Unitary.star_eq_inv]
  have hspectral :
      Mmat = (↑U : Matrix ι ι ℝ) * D *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    rw [hherm.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rw [hstar]
    rfl
  have hposdiag : Matrix.PosSemidef Ddiff := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr
      (by simpa [finiteHermitianEigenvalues, hherm, Mmat] using hEig i)
  have hconj_pos :
      Matrix.PosSemidef
        ((↑U : Matrix ι ι ℝ) * Ddiff * star (↑U : Matrix ι ι ℝ)) := by
    exact
      (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
        (Units.isUnit U)).mpr hposdiag
  have hstarU : star (↑U : Matrix ι ι ℝ) =
      ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    exact hstar
  have hS_eq :
      (↑U : Matrix ι ι ℝ) * S *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) = S := by
    have hdiag_scalar : S = L • (1 : Matrix ι ι ℝ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [S, Matrix.diagonal]
      · simp [S, Matrix.diagonal, hij]
    rw [hdiag_scalar]
    simp
  have hDdiff_eq : Ddiff = S - D := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Ddiff, S, D, Matrix.diagonal]
    · simp [Ddiff, S, D, Matrix.diagonal, hij]
  have hscalar_entries :
      ((fun i j : ι => L * finiteIdMatrix i j) : Matrix ι ι ℝ) = S := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [S, finiteIdMatrix, Matrix.diagonal]
    · simp [S, finiteIdMatrix, Matrix.diagonal, hij]
  have hentrydiff :
      ((fun i j : ι => L * finiteIdMatrix i j - M i j) : Matrix ι ι ℝ) =
        S - Mmat := by
    ext i j
    have hsij := congrFun (congrFun hscalar_entries i) j
    change L * finiteIdMatrix i j - M i j = S i j - Mmat i j
    rw [hsij]
  have hdiff :
      ((fun i j : ι => L * finiteIdMatrix i j - M i j) : Matrix ι ι ℝ) =
        (↑U : Matrix ι ι ℝ) * Ddiff * star (↑U : Matrix ι ι ℝ) := by
    calc
      ((fun i j : ι => L * finiteIdMatrix i j - M i j) : Matrix ι ι ℝ)
          = S - Mmat := hentrydiff
      _ = S - ((↑U : Matrix ι ι ℝ) * D *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ)) := by
            rw [hspectral]
      _ = (↑U : Matrix ι ι ℝ) * (S - D) *
          ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
            calc
              S - ((↑U : Matrix ι ι ℝ) * D *
                    ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ))
                  = ((↑U : Matrix ι ι ℝ) * S *
                      ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ)) -
                    ((↑U : Matrix ι ι ℝ) * D *
                      ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ)) := by
                        rw [hS_eq]
              _ = (↑U : Matrix ι ι ℝ) * (S - D) *
                    ((U⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
                      noncomm_ring
      _ = (↑U : Matrix ι ι ℝ) * Ddiff *
            star (↑U : Matrix ι ι ℝ) := by
              rw [hDdiff_eq, hstarU]
  have hpsd :
      Matrix.PosSemidef
        ((fun i j : ι => L * finiteIdMatrix i j - M i j) : Matrix ι ι ℝ) := by
    rw [hdiff]
    exact hconj_pos
  exact Matrix_posSemidef_sub.to_finiteLoewnerLe
    M (fun i j => L * finiteIdMatrix i j) hpsd

/-- A symmetric positive-semidefinite finite matrix whose Hermitian
    eigenvalues are bounded above by `L` has finite operator-2 norm at most
    `L`.

    This packages the spectral upper-bound route through the repository's
    Loewner-to-operator bridge. -/
theorem finiteOpNorm2Le_of_finitePSD_of_finiteHermitianEigenvalues_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hM : IsSymmetricFiniteMatrix M)
    (hPSD : finitePSD M)
    (hEig : ∀ a : ι, finiteHermitianEigenvalues M hM a ≤ L) :
    finiteOpNorm2Le M L :=
  finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
    M hL hM hPSD
    (finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le M hM hEig)

/-- Square-matrix `Fin n` wrapper for
    `finiteOpNorm2Le_of_finitePSD_of_finiteHermitianEigenvalues_le`. -/
theorem opNorm2Le_of_finitePSD_of_finiteHermitianEigenvalues_le
    {n : ℕ} (M : Fin n → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hM : IsSymmetricFiniteMatrix M)
    (hPSD : finitePSD M)
    (hEig : ∀ a : Fin n, finiteHermitianEigenvalues M hM a ≤ L) :
    opNorm2Le M L :=
  opNorm2Le_of_finiteOpNorm2Le M
    (finiteOpNorm2Le_of_finitePSD_of_finiteHermitianEigenvalues_le
      M hL hM hPSD hEig)

/-- A scalar-identity Loewner upper bound gives the corresponding
    trace-exponential scalar bound.  This is the deterministic final step that
    converts a future matrix-CGF Loewner estimate into a scalar trace-MGF
    estimate. -/
theorem finiteTrace_finiteMatrixExp_le_card_mul_exp_of_finiteLoewnerLe_smul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) {c : ℝ}
    (hLe : finiteLoewnerLe M (fun i j => c * finiteIdMatrix i j)) :
    finiteTrace (finiteMatrixExp M) ≤ (Fintype.card ι : ℝ) * Real.exp c := by
  rw [finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues M hM]
  calc
    (∑ i : ι, Real.exp (finiteHermitianEigenvalues M hM i))
        ≤ ∑ _i : ι, Real.exp c := by
          apply Finset.sum_le_sum
          intro i _
          exact Real.exp_le_exp.mpr
            (finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id M hM hLe i)
    _ = (Fintype.card ι : ℝ) * Real.exp c := by
          simp

/-- Negative trace-exponential scalar bound from the lower Loewner side
    `-M <= c I`. -/
theorem finiteTrace_finiteMatrixExp_neg_le_card_mul_exp_of_neg_finiteLoewnerLe_smul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) {c : ℝ}
    (hLe : finiteLoewnerLe (fun i j => -M i j)
      (fun i j => c * finiteIdMatrix i j)) :
    finiteTrace (finiteMatrixExp (fun i j => -M i j)) ≤
      (Fintype.card ι : ℝ) * Real.exp c := by
  have hNegSym : IsSymmetricFiniteMatrix (fun i j => -M i j) := by
    intro i j
    change -M i j = -M j i
    rw [hM i j]
  exact
    finiteTrace_finiteMatrixExp_le_card_mul_exp_of_finiteLoewnerLe_smul_id
      (fun i j => -M i j) hNegSym hLe

/-- The local quadratic-form PSD predicate is equivalent, for a symmetric real
    finite matrix, to nonnegativity of all Hermitian eigenvalues. -/
theorem finitePSD_iff_finiteHermitianEigenvalues_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    finitePSD M ↔ ∀ i : ι, 0 ≤ finiteHermitianEigenvalues M hM i := by
  constructor
  · intro hpsd i
    have hmat : Matrix.PosSemidef (M : Matrix ι ι ℝ) :=
      finitePSD.to_matrix_posSemidef M hM hpsd
    simpa [finiteHermitianEigenvalues] using hmat.eigenvalues_nonneg i
  · intro heigs
    apply Matrix_posSemidef.to_finitePSD M
    have hherm := IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM
    exact hherm.posSemidef_iff_eigenvalues_nonneg.mpr
      (by simpa [finiteHermitianEigenvalues] using heigs)

/-- A local finite Loewner inequality is equivalent to nonnegativity of the
    Hermitian eigenvalues of the difference matrix `N - M`. -/
theorem finiteLoewnerLe_iff_sub_finiteHermitianEigenvalues_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : ι → ι → ℝ)
    (hM : IsSymmetricFiniteMatrix M) (hN : IsSymmetricFiniteMatrix N) :
    finiteLoewnerLe M N ↔
      ∀ i : ι,
        0 ≤ finiteHermitianEigenvalues (fun r c => N r c - M r c)
          (by
            intro r c
            change N r c - M r c = N c r - M c r
            rw [hN r c, hM r c]) i := by
  let D : ι → ι → ℝ := fun r c => N r c - M r c
  have hD : IsSymmetricFiniteMatrix D := by
    intro r c
    change N r c - M r c = N c r - M c r
    rw [hN r c, hM r c]
  rw [finiteLoewnerLe_iff_sub_finitePSD M N]
  exact finitePSD_iff_finiteHermitianEigenvalues_nonneg D hD

/-- The scalar multiple `L I` of the finite identity matrix is symmetric. -/
theorem smulFiniteIdMatrix_symmetric {ι : Type*} [DecidableEq ι]
    (L : ℝ) : IsSymmetricFiniteMatrix (fun i j : ι => L * finiteIdMatrix i j) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [finiteIdMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [finiteIdMatrix, hij, hji]

/-- The difference `L I - M` is symmetric whenever `M` is symmetric. -/
theorem finiteScalarUpperDiff_symmetric {ι : Type*} [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (L : ℝ) :
    IsSymmetricFiniteMatrix (fun i j : ι => L * finiteIdMatrix i j - M i j) := by
  intro i j
  have hid := smulFiniteIdMatrix_symmetric (ι := ι) L i j
  change L * finiteIdMatrix i j = L * finiteIdMatrix j i at hid
  change L * finiteIdMatrix i j - M i j = L * finiteIdMatrix j i - M j i
  rw [hid, hM i j]

/-- Hermitian eigenvalues of the scalar upper-bound difference `L I - M`. -/
noncomputable def finiteScalarUpperDiffEigenvalues {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (L : ℝ) : ι → ℝ :=
  finiteHermitianEigenvalues (fun i j => L * finiteIdMatrix i j - M i j)
    (finiteScalarUpperDiff_symmetric M hM L)

/-- Named scalar-identity upper-bound version of the finite Loewner/eigenvalue
    bridge: `M <= L I` iff every eigenvalue of `L I - M` is nonnegative. -/
theorem finiteLoewnerLe_smul_id_iff_finiteScalarUpperDiffEigenvalues_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (L : ℝ) :
    finiteLoewnerLe M (fun i j => L * finiteIdMatrix i j) ↔
      ∀ a : ι, 0 ≤ finiteScalarUpperDiffEigenvalues M hM L a := by
  let N : ι → ι → ℝ := fun i j => L * finiteIdMatrix i j
  have hN : IsSymmetricFiniteMatrix N := smulFiniteIdMatrix_symmetric L
  simpa [N, finiteScalarUpperDiffEigenvalues,
    finiteScalarUpperDiff_symmetric] using
    (finiteLoewnerLe_iff_sub_finiteHermitianEigenvalues_nonneg M N hM hN)

/-- A scalar-identity upper Loewner bound is equivalent to nonnegativity of the
    Hermitian eigenvalues of `L I - M`.  This is the deterministic spectral
    bridge needed by future largest-eigenvalue tail bounds. -/
theorem finiteLoewnerLe_smul_id_iff_sub_finiteHermitianEigenvalues_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (L : ℝ) :
    finiteLoewnerLe M (fun i j => L * finiteIdMatrix i j) ↔
      ∀ a : ι,
        0 ≤ finiteHermitianEigenvalues
          (fun i j => L * finiteIdMatrix i j - M i j)
          (finiteScalarUpperDiff_symmetric M hM L) a := by
  simpa [finiteScalarUpperDiffEigenvalues] using
    finiteLoewnerLe_smul_id_iff_finiteScalarUpperDiffEigenvalues_nonneg
      M hM L

end LeanFpAnalysis.FP
