import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.RandNLA.LowRankApprox
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Basic

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Rectangular normal-equation Gram matrix `Aᵀ A`.  This duplicate of the
    RandNLA-facing `lsNormalMatrix` is kept in the least-squares module so QR
    solver facts do not depend on the RandNLA algorithm files. -/
noncomputable def rectLSGram {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k
/-- Rectangular normal-equation right-hand side `Aᵀ b`. -/
noncomputable def rectLSRhs {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, A i j * b i
/-- Least-squares residual vector `A x - b` for a rectangular matrix.

    Higham, 2nd ed., Chapter 20 uses the opposite sign `b - A x` for residuals
    in some displays; the squared objective is unchanged by this convention. -/
noncomputable def lsResidual {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => rectMatMulVec A x i - b i
/-- Squared least-squares objective `||A x - b||₂²`. -/
noncomputable def lsObjective {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  vecNorm2Sq (lsResidual A b x)
/-- Row permutations preserve the least-squares residual, up to the same
    permutation of residual coordinates. -/
theorem lsResidual_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (rectPermuteRows σ A) (vecPermute σ b) x =
      vecPermute σ (lsResidual A b x) := by
  ext i
  rfl
/-- Row sorting/pivoting does not change the least-squares objective when the
    right-hand side is permuted by the same row map. -/
theorem lsObjective_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsObjective (rectPermuteRows σ A) (vecPermute σ b) x =
      lsObjective A b x := by
  unfold lsObjective
  rw [lsResidual_permuteRows, vecNorm2Sq_permute]
/-- Column permutations preserve the residual after pulling the coefficient
    vector back by the inverse column permutation. -/
theorem lsResidual_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (rectPermuteCols π A) b x =
      lsResidual A b (vecPermute π.symm x) := by
  unfold lsResidual
  rw [rectMatMulVec_permuteCols]
/-- Column pivoting does not change the least-squares objective after pulling
    the coefficient vector back by the inverse column permutation. -/
theorem lsObjective_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsObjective (rectPermuteCols π A) b x =
      lsObjective A b (vecPermute π.symm x) := by
  unfold lsObjective
  rw [lsResidual_permuteCols]
/-- Combined row sorting and column pivoting preserve residuals up to row
    permutation, after pulling coefficients back by the inverse column
    permutation. -/
theorem lsResidual_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) x =
      vecPermute σ (lsResidual A b (vecPermute π.symm x)) := by
  rw [lsResidual_permuteRows, lsResidual_permuteCols]
/-- Row sorting plus column pivoting does not change the least-squares
    objective after pulling coefficients back by the inverse column
    permutation. -/
theorem lsObjective_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsObjective (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) x =
      lsObjective A b (vecPermute π.symm x) := by
  unfold lsObjective
  rw [lsResidual_permuteRowsCols, vecNorm2Sq_permute]
/-- Rectangular matrix-vector multiplication after a square left factor:
    `(U A) x = U (A x)`. -/
theorem rectMatMulVec_matMulRectLeft {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (matMulRectLeft U A) x =
      matMulVec m U (rectMatMulVec A x) := by
  ext i
  unfold rectMatMulVec matMulRectLeft matMulVec
  calc
    ∑ j : Fin n, (∑ k : Fin m, U i k * A k j) * x j
        = ∑ j : Fin n, ∑ k : Fin m, (U i k * A k j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ k : Fin m, ∑ j : Fin n, (U i k * A k j) * x j := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, U i k * ∑ j : Fin n, A k j * x j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
/-- Residuals transform equivariantly under a common square left factor:
    `(U A)x - U b = U(Ax - b)`. -/
theorem lsResidual_matMulRectLeft {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (matMulRectLeft U A) (matMulVec m U b) x =
      matMulVec m U (lsResidual A b x) := by
  ext i
  unfold lsResidual
  rw [congrFun (rectMatMulVec_matMulRectLeft U A x) i]
  unfold matMulVec
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
/-- Orthogonal row transformations preserve the squared least-squares
    objective when applied to both the matrix and the right-hand side. -/
theorem lsObjective_matMulRectLeft_orthogonal {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    lsObjective (matMulRectLeft U A) (matMulVec m U b) x =
      lsObjective A b x := by
  unfold lsObjective
  rw [lsResidual_matMulRectLeft]
  exact vecNorm2Sq_orthogonal U (lsResidual A b x) hU
/-- Residuals commute with a right change of variables:
    `(A C)y - b = A(C y) - b`. -/
theorem lsResidual_rectMatMul_right {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (C : Fin n → Fin p → ℝ)
    (b : Fin m → ℝ) (y : Fin p → ℝ) :
    lsResidual (rectMatMul A C) b y =
      lsResidual A b (rectMatMulVec C y) := by
  ext i
  unfold lsResidual
  rw [congrFun (rectMatMulVec_rectMatMul A C y) i]
/-- The squared least-squares objective commutes with a right change of
    variables. -/
theorem lsObjective_rectMatMul_right {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (C : Fin n → Fin p → ℝ)
    (b : Fin m → ℝ) (y : Fin p → ℝ) :
    lsObjective (rectMatMul A C) b y =
      lsObjective A b (rectMatMulVec C y) := by
  unfold lsObjective
  rw [lsResidual_rectMatMul_right]
/-- Explicit-arity version of `lsObjective_rectMatMul_right`. -/
theorem lsObjective_matMulRect_right (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (C : Fin n → Fin p → ℝ)
    (b : Fin m → ℝ) (y : Fin p → ℝ) :
    lsObjective (matMulRect m n p A C) b y =
      lsObjective A b (rectMatMulVec C y) := by
  exact lsObjective_rectMatMul_right A C b y
/-- Normal-equation Gram matrix `A^T A` for a rectangular least-squares
    instance.  This source-facing name is shared with the RandNLA layer. -/
noncomputable def lsNormalMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectLSGram A
/-- Normal-equation right-hand side `A^T b` for a rectangular least-squares
    instance.  This source-facing name is shared with the RandNLA layer. -/
noncomputable def lsNormalRhs {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  rectLSRhs A b
/-- A vector is an exact minimizer of the least-squares objective. -/
def IsLeastSquaresMinimizer {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, lsObjective A b x ≤ lsObjective A b y
/-- An exact minimizer for a row-permuted least-squares problem is an exact
    minimizer for the original problem. -/
theorem IsLeastSquaresMinimizer.of_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (h : IsLeastSquaresMinimizer (rectPermuteRows σ A) (vecPermute σ b) x) :
    IsLeastSquaresMinimizer A b x := by
  intro y
  have hy := h y
  rw [lsObjective_permuteRows] at hy
  rw [lsObjective_permuteRows] at hy
  exact hy
/-- An exact minimizer for a column-permuted least-squares problem maps back
    to an exact minimizer of the original problem. -/
theorem IsLeastSquaresMinimizer.of_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (h : IsLeastSquaresMinimizer (rectPermuteCols π A) b x) :
    IsLeastSquaresMinimizer A b (vecPermute π.symm x) := by
  intro y
  have hy := h (vecPermute π y)
  rw [lsObjective_permuteCols] at hy
  rw [lsObjective_permuteCols] at hy
  simpa [vecPermute_symm_vecPermute] using hy
/-- An exact minimizer for a row-sorted and column-pivoted least-squares
    problem maps back to an exact minimizer of the original problem by undoing
    the column permutation. -/
theorem IsLeastSquaresMinimizer.of_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (h : IsLeastSquaresMinimizer
      (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) x) :
    IsLeastSquaresMinimizer A b (vecPermute π.symm x) := by
  intro y
  have hy := h (vecPermute π y)
  rw [lsObjective_permuteRowsCols] at hy
  rw [lsObjective_permuteRowsCols] at hy
  simpa [vecPermute_symm_vecPermute] using hy
/-- Row permutations preserve the rectangular normal-equation Gram matrix. -/
theorem rectLSGram_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) :
    rectLSGram (rectPermuteRows σ A) = rectLSGram A := by
  ext j k
  unfold rectLSGram rectPermuteRows
  exact
    Fintype.sum_equiv σ
      (fun i : Fin m => A (σ i) j * A (σ i) k)
      (fun i : Fin m => A i j * A i k)
      (fun _ => rfl)
/-- Row permutations preserve the rectangular normal-equation right-hand side,
    provided the right-hand side vector is permuted by the same row map. -/
theorem rectLSRhs_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    rectLSRhs (rectPermuteRows σ A) (vecPermute σ b) = rectLSRhs A b := by
  ext j
  unfold rectLSRhs rectPermuteRows vecPermute
  exact
    Fintype.sum_equiv σ
      (fun i : Fin m => A (σ i) j * b (σ i))
      (fun i : Fin m => A i j * b i)
      (fun _ => rfl)
/-- Column permutations relabel both coordinates of the rectangular
    normal-equation Gram matrix. -/
theorem rectLSGram_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) :
    rectLSGram (rectPermuteCols π A) =
      fun j k => rectLSGram A (π j) (π k) := by
  ext j k
  rfl
/-- Column permutations relabel the rectangular normal-equation right-hand
    side. -/
theorem rectLSRhs_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    rectLSRhs (rectPermuteCols π A) b = vecPermute π (rectLSRhs A b) := by
  ext j
  rfl
/-- Combined row sorting and column pivoting relabel the rectangular
    normal-equation Gram matrix only by the column permutation. -/
theorem rectLSGram_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) :
    rectLSGram (rectPermuteRows σ (rectPermuteCols π A)) =
      fun j k => rectLSGram A (π j) (π k) := by
  rw [rectLSGram_permuteRows]
  exact rectLSGram_permuteCols π A
/-- Combined row sorting and column pivoting relabel the rectangular
    normal-equation right-hand side only by the column permutation, provided
    the data vector follows the row permutation. -/
theorem rectLSRhs_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    rectLSRhs (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) =
      vecPermute π (rectLSRhs A b) := by
  rw [rectLSRhs_permuteRows]
  exact rectLSRhs_permuteCols π A b
theorem rectLSNormalEquations_residual_sum_eq_diff {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (j : Fin n) :
    ∑ i : Fin m, A i j * lsResidual A b x i =
      (∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k) -
        ∑ i : Fin m, A i j * b i := by
  calc
    ∑ i : Fin m, A i j * lsResidual A b x i
        = ∑ i : Fin m, A i j * rectMatMulVec A x i -
            ∑ i : Fin m, A i j * b i := by
          simp_rw [lsResidual, mul_sub]
          rw [Finset.sum_sub_distrib]
    _ = (∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k) -
        ∑ i : Fin m, A i j * b i := by
          congr 1
          calc
            ∑ i : Fin m, A i j * rectMatMulVec A x i
                = ∑ i : Fin m, ∑ k : Fin n, A i j * (A i k * x k) := by
                  unfold rectMatMulVec
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
            _ = ∑ k : Fin n, ∑ i : Fin m, A i j * (A i k * x k) := by
                  rw [Finset.sum_comm]
            _ = ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k := by
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
/-- Higham's signed least-squares residual `b - A x`.  The shared objective API
    uses `A x - b`; this source-facing alias records the sign convention in
    Chapter 20's augmented system. -/
noncomputable def lsResidualHigham {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => b i - rectMatMulVec A x i
theorem lsResidualHigham_eq_neg_lsResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidualHigham A b x = fun i => -lsResidual A b x i := by
  ext i
  unfold lsResidualHigham lsResidual
  ring
/-- A zero Higham-signed residual is an exact solution of the data equations,
    hence an exact least-squares minimizer.  This is the zero-residual branch
    used by the normwise backward-error formula (20.20)-(20.21). -/
theorem IsLeastSquaresMinimizer.of_lsResidualHigham_eq_zero {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (hres : lsResidualHigham A b x = 0) :
    IsLeastSquaresMinimizer A b x := by
  intro y
  have hres0 : lsResidual A b x = 0 := by
    ext i
    change lsResidual A b x i = (0 : ℝ)
    have hi : lsResidualHigham A b x i = 0 := by
      simpa using congrFun hres i
    unfold lsResidualHigham at hi
    unfold lsResidual
    linarith
  have hx_obj : lsObjective A b x = 0 := by
    unfold lsObjective
    rw [hres0]
    unfold vecNorm2Sq
    simp
  have hy_nonneg : 0 ≤ lsObjective A b y := by
    unfold lsObjective
    exact vecNorm2Sq_nonneg (lsResidual A b y)
  linarith
theorem lsResidualHigham_column_sum_eq_neg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (j : Fin n) :
    ∑ i : Fin m, A i j * lsResidualHigham A b x i =
      -∑ i : Fin m, A i j * lsResidual A b x i := by
  rw [lsResidualHigham_eq_neg_lsResidual A b x]
  simp_rw [mul_neg]
  rw [← Finset.sum_neg_distrib]
/-- Real symmetric-matrix orthogonality for distinct eigenvalues, stated in the
    repository's finite-matrix/vector-action language.  This is spectral
    infrastructure for equation (20.18): once two vectors are eigenvectors of
    the same symmetric matrix for different eigenvalues, their Euclidean dot
    product is zero. -/
theorem isSymmetricFiniteMatrix_eigenvectors_sum_mul_eq_zero {n : ℕ}
    {M : Fin n → Fin n → ℝ} (hM : IsSymmetricFiniteMatrix M)
    {lambda mu : ℝ} {x y : Fin n → ℝ}
    (hx : rectMatMulVec M x = fun i => lambda * x i)
    (hy : rectMatMulVec M y = fun i => mu * y i)
    (hlambda_mu : lambda ≠ mu) :
    (∑ i : Fin n, x i * y i) = 0 := by
  have hleft_eval :
      (∑ i : Fin n, rectMatMulVec M x i * y i) =
        lambda * ∑ i : Fin n, x i * y i := by
    calc
      (∑ i : Fin n, rectMatMulVec M x i * y i) =
          ∑ i : Fin n, (lambda * x i) * y i := by
            rw [hx]
      _ = ∑ i : Fin n, lambda * (x i * y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = lambda * ∑ i : Fin n, x i * y i := by
            rw [Finset.mul_sum]
  have hright_eval :
      (∑ i : Fin n, x i * rectMatMulVec M y i) =
        mu * ∑ i : Fin n, x i * y i := by
    calc
      (∑ i : Fin n, x i * rectMatMulVec M y i) =
          ∑ i : Fin n, x i * (mu * y i) := by
            rw [hy]
      _ = ∑ i : Fin n, mu * (x i * y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = mu * ∑ i : Fin n, x i * y i := by
            rw [Finset.mul_sum]
  have htranspose :
      (∑ i : Fin n, rectMatMulVec M x i * y i) =
        ∑ j : Fin n, x j * rectMatMulVec M y j := by
    unfold rectMatMulVec
    calc
      (∑ i : Fin n, (∑ j : Fin n, M i j * x j) * y i) =
          ∑ i : Fin n, ∑ j : Fin n, (M i j * x j) * y i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ i : Fin n, (M i j * x j) * y i := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n, ∑ i : Fin n, x j * (M j i * y i) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            rw [hM i j]
            ring
      _ = ∑ j : Fin n, x j * ∑ i : Fin n, M j i * y i := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
  have hscalar :
      lambda * (∑ i : Fin n, x i * y i) =
        mu * (∑ i : Fin n, x i * y i) := by
    rw [← hleft_eval, htranspose, hright_eval]
  have hprod :
      (lambda - mu) * (∑ i : Fin n, x i * y i) = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hlambda_mu)
/-- The top block in Higham, 2nd ed., Chapter 20, equation (20.6):
    `(I - A A^+) u + (A^+)^T v`.  This is the first component of the
    displayed inverse action for the augmented least-squares matrix
    `[I A; A^T 0]`. -/
noncomputable def lsAugmentedInverseActionTop {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Fin m → ℝ :=
  fun i =>
    u i - rectMatMulVec A (rectMatMulVec Aplus u) i +
      ∑ j : Fin n, Aplus j i * v j
/-- The bottom block in Higham, 2nd ed., Chapter 20, equation (20.6):
    `A^+ u - (A^T A)^{-1} v`. -/
noncomputable def lsAugmentedInverseActionBottom {m n : ℕ}
    (Aplus : Fin n → Fin m → ℝ) (gramInv : Fin n → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun j => rectMatMulVec Aplus u j - matMulVec n gramInv v j
theorem lsAugmentedInverseAction_Aplus_mul_A {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (gramInv : Fin n → Fin n → ℝ)
    (hAplus : ∀ j i, Aplus j i = ∑ k : Fin n, gramInv j k * A i k)
    (hGramInv : IsInverse n (rectLSGram A) gramInv) :
    ∀ j k : Fin n, ∑ i : Fin m, Aplus j i * A i k =
      if j = k then 1 else 0 := by
  intro j k
  calc
    ∑ i : Fin m, Aplus j i * A i k
        = ∑ i : Fin m, (∑ p : Fin n, gramInv j p * A i p) * A i k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hAplus j i]
    _ = ∑ i : Fin m, ∑ p : Fin n, (gramInv j p * A i p) * A i k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
    _ = ∑ p : Fin n, ∑ i : Fin m, (gramInv j p * A i p) * A i k := by
            rw [Finset.sum_comm]
    _ = ∑ p : Fin n, gramInv j p * rectLSGram A p k := by
            apply Finset.sum_congr rfl
            intro p _
            unfold rectLSGram
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = if j = k then 1 else 0 := hGramInv.1 j k
theorem lsAugmentedInverseAction_gram_mul_Aplus {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (gramInv : Fin n → Fin n → ℝ)
    (hAplus : ∀ j i, Aplus j i = ∑ k : Fin n, gramInv j k * A i k)
    (hGramInv : IsInverse n (rectLSGram A) gramInv) :
    ∀ j : Fin n, ∀ i : Fin m,
      ∑ k : Fin n, rectLSGram A j k * Aplus k i = A i j := by
  intro j i
  calc
    ∑ k : Fin n, rectLSGram A j k * Aplus k i
        = ∑ k : Fin n, rectLSGram A j k *
            (∑ p : Fin n, gramInv k p * A i p) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hAplus k i]
    _ = ∑ p : Fin n, (∑ k : Fin n, rectLSGram A j k * gramInv k p) * A i p := by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = ∑ p : Fin n, (if j = p then 1 else 0) * A i p := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hGramInv.2 j p]
    _ = A i j := by
            simp
/-- The Gram matrix `A^T A` used in Chapter 20 is symmetric. -/
theorem rectLSGram_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectLSGram A) := by
  intro j k
  unfold rectLSGram
  apply Finset.sum_congr rfl
  intro i _
  ring
/-- Concrete Gram inverse candidate for the determinant-facing form of
    Higham's Chapter 20, equation (20.6). -/
noncomputable def lsGramNonsingInv {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  nonsingInv n (rectLSGram A)
/-- A nonzero determinant of `A^T A` supplies the concrete Gram-inverse
    certificate needed by the exact inverse action (20.6). -/
theorem lsGramNonsingInv_isInverse_of_det_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hdet : Matrix.det (rectLSGram A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    IsInverse n (rectLSGram A) (lsGramNonsingInv A) := by
  exact isInverse_nonsingInv_of_det_ne_zero n (rectLSGram A) hdet
/-- The concrete Gram inverse candidate preserves the symmetry of `A^T A`. -/
theorem lsGramNonsingInv_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (lsGramNonsingInv A) := by
  exact nonsingInv_symmetric_of_symmetric (rectLSGram A)
    (rectLSGram_symmetric A)
/-- Kernel inclusion for the Gram matrix: if `(Aᵀ A)x = 0`, then `Ax = 0`.

    This is the exact finite-dimensional bridge behind the source statement
    that full column rank of `A` makes the Gram matrix nonsingular. -/
theorem rectMatMulVec_eq_zero_of_rectLSGram_mulVec_eq_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {x : Fin n → ℝ}
    (hGx : rectMatMulVec (rectLSGram A) x = 0) :
    rectMatMulVec A x = 0 := by
  let M : Matrix (Fin m) (Fin n) ℝ := A
  have hker : x ∈ LinearMap.ker ((M.transpose * M).mulVecLin) := by
    change (M.transpose * M).mulVec x = 0
    ext j
    have hj := congrFun hGx j
    simpa [M, Matrix.mulVec, Matrix.mul_apply, rectMatMulVec, rectLSGram] using hj
  have hAx : x ∈ LinearMap.ker M.mulVecLin := by
    rw [← Matrix.ker_mulVecLin_transpose_mul_self M]
    exact hker
  ext i
  have hi := congrFun hAx i
  simpa [M, Matrix.mulVec, rectMatMulVec] using hi
/-- Full column rank of `A`, represented locally as injectivity of
    `x ↦ A x`, transfers to injectivity of the Gram action
    `x ↦ (Aᵀ A)x`. -/
theorem rectLSGram_rectMatMulVec_injective_of_rectMatMulVec_injective
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    Function.Injective (rectMatMulVec (rectLSGram A)) := by
  intro x y hxy
  apply hA
  have hdiffG : rectMatMulVec (rectLSGram A) (fun j => x j - y j) = 0 := by
    rw [rectMatMulVec_sub]
    ext j
    have hj := congrFun hxy j
    exact sub_eq_zero.mpr hj
  have hAdiff :=
    rectMatMulVec_eq_zero_of_rectLSGram_mulVec_eq_zero A hdiffG
  rw [rectMatMulVec_sub] at hAdiff
  exact sub_eq_zero.mp hAdiff
/-- A square function-shaped matrix with injective vector action has nonzero
    determinant. -/
theorem det_ne_zero_of_square_rectMatMulVec_injective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec T)) :
    Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := T
  have hM_inj : Function.Injective M.mulVec := by
    intro x y hxy
    apply hinj
    ext i
    have hi := congrFun hxy i
    simpa [M, rectMatMulVec, Matrix.mulVec] using hi
  have hunitM : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  have hdetUnit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunitM
  have hdetNe : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  simpa [M] using hdetNe
/-- Source full-column-rank form of the nonsingular-Gram bridge:
    injectivity of `x ↦ A x` implies `det(AᵀA) ≠ 0`. -/
theorem rectLSGram_det_ne_zero_of_rectMatMulVec_injective {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    Matrix.det (rectLSGram A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  exact
    det_ne_zero_of_square_rectMatMulVec_injective
      (T := rectLSGram A)
      (rectLSGram_rectMatMulVec_injective_of_rectMatMulVec_injective A hA)
/-- The `I - A A^+` top-left block in Higham, 2nd ed., Chapter 20,
    equation (20.6). -/
noncomputable def lsAugmentedProjectionBlock {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i k => idMatrix m i k - rectMatMulVec A (fun j => Aplus j k) i
/-- Vector action of the `I - A A^+` block from (20.6). -/
theorem lsAugmentedProjectionBlock_mulVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (u : Fin m → ℝ) :
    rectMatMulVec (lsAugmentedProjectionBlock A Aplus) u =
      fun i => u i - rectMatMulVec A (rectMatMulVec Aplus u) i := by
  ext i
  have hid := congrFun (idMatrix_mulVec m u) i
  have hcomp :
      (∑ k : Fin m, rectMatMulVec A (fun j => Aplus j k) i * u k) =
        rectMatMulVec A (rectMatMulVec Aplus u) i := by
    unfold rectMatMulVec
    calc
      ∑ k : Fin m, (∑ j : Fin n, A i j * Aplus j k) * u k
          = ∑ k : Fin m, ∑ j : Fin n, (A i j * Aplus j k) * u k := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ k : Fin m, (A i j * Aplus j k) * u k := by
              rw [Finset.sum_comm]
      _ = ∑ j : Fin n, A i j * (∑ k : Fin m, Aplus j k * u k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
  unfold rectMatMulVec lsAugmentedProjectionBlock
  calc
    ∑ k : Fin m,
        (idMatrix m i k - rectMatMulVec A (fun j => Aplus j k) i) * u k
        = (∑ k : Fin m, idMatrix m i k * u k) -
            ∑ k : Fin m, rectMatMulVec A (fun j => Aplus j k) i * u k := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = u i - rectMatMulVec A (rectMatMulVec Aplus u) i := by
            rw [hid, hcomp]
/-- Source-shaped first right-hand-side block in (20.6):
    `Delta b - Delta A y`. -/
noncomputable def lsEq20_6RhsTop {m n : ℕ}
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (y : Fin n → ℝ) : Fin m → ℝ :=
  fun i => Deltab i - rectMatMulVec DeltaA y i
/-- Source-shaped second right-hand-side block in (20.6):
    `-Delta A^T s`. -/
noncomputable def lsEq20_6RhsBottom {m n : ℕ}
    (DeltaA : Fin m → Fin n → ℝ) (s : Fin m → ℝ) : Fin n → ℝ :=
  fun j => -∑ i : Fin m, DeltaA i j * s i
/-- The Gram action `Aᵀ A x` is the transpose action applied to `A x`.

    This is the algebraic identity used to turn uniqueness of the augmented
    system into invertibility of `Aᵀ A`. -/
theorem rectLSGram_mulVec_eq_transpose_rectMatMulVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    matMulVec n (rectLSGram A) x =
      fun j => ∑ i : Fin m, A i j * rectMatMulVec A x i := by
  ext j
  unfold matMulVec rectLSGram rectMatMulVec
  calc
    ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k
        = ∑ k : Fin n, ∑ i : Fin m, (A i j * A i k) * x k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ k : Fin n, (A i j * A i k) * x k := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, A i j * ∑ k : Fin n, A i k * x k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
theorem matMulVec_eq_zero_of_inverse {n : ℕ}
    (T Tinv : Fin n → Fin n → ℝ) (hInv : IsInverse n T Tinv)
    {x : Fin n → ℝ} (hx : ∀ i : Fin n, matMulVec n T x i = 0) :
    x = 0 := by
  ext i
  calc
    x i = matMulVec n (idMatrix n) x i := by rw [matMulVec_id]
    _ = matMulVec n (matMul n Tinv T) x i := by
          have hmat : matMul n Tinv T = idMatrix n := by
            ext a b
            exact hInv.1 a b
          rw [hmat]
    _ = matMulVec n Tinv (matMulVec n T x) i := by
          exact matMulVec_matMul n Tinv T x i
    _ = matMulVec n Tinv 0 i := by
          congr 1
          ext j
          exact hx j
    _ = 0 := by
          unfold matMulVec
          simp
theorem rectMatMulVec_absMatrixRect_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {x : Fin n → ℝ}
    (hx : ∀ j, 0 ≤ x j) :
    ∀ i : Fin m, 0 ≤ rectMatMulVec (absMatrixRect A) x i := by
  intro i
  unfold rectMatMulVec absMatrixRect
  exact Finset.sum_nonneg (by
    intro j _
    exact mul_nonneg (abs_nonneg (A i j)) (hx j))
theorem matMulVec_absMatrix_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) {x : Fin n → ℝ}
    (hx : ∀ j, 0 ≤ x j) :
    ∀ i : Fin n, 0 ≤ matMulVec n (absMatrix n A) x i := by
  intro i
  unfold matMulVec absMatrix
  exact Finset.sum_nonneg (by
    intro j _
    exact mul_nonneg (abs_nonneg (A i j)) (hx j))
/-- Dot product of two appended real vectors, split over the source row and
    column blocks used in the scaled augmented matrix `C(alpha)`. -/
theorem finAppend_sum_mul_eq {m n : ℕ}
    (x y : Fin m → ℝ) (z w : Fin n → ℝ) :
    (∑ k : Fin (m + n), Fin.append x z k * Fin.append y w k) =
      (∑ i : Fin m, x i * y i) + (∑ j : Fin n, z j * w j) := by
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Dot product of source-normalized appended branch vectors, with arbitrary
    right-block scale factors.  This is the algebraic reduction used when
    building an orthogonal basis from singular-vector data in (20.18). -/
theorem finAppend_sum_mul_smul_eq {m n : ℕ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ) (beta gamma : ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u (fun j => beta * v j) k *
        Fin.append w (fun j => gamma * z j) k) =
      (∑ i : Fin m, u i * w i) +
        beta * gamma * (∑ j : Fin n, v j * z j) := by
  rw [finAppend_sum_mul_eq]
  have hright :
      (∑ j : Fin n, (beta * v j) * (gamma * z j)) =
        beta * gamma * (∑ j : Fin n, v j * z j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hright]
/-- Rescaling two real vectors by the inverse of their Euclidean norms preserves
    a zero Euclidean dot product. -/
theorem vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero {n : ℕ}
    (x y : Fin n → ℝ)
    (hxy : (∑ i : Fin n, x i * y i) = 0) :
    (∑ i : Fin n,
      ((vecNorm2 x)⁻¹ * x i) * ((vecNorm2 y)⁻¹ * y i)) = 0 := by
  calc
    (∑ i : Fin n,
      ((vecNorm2 x)⁻¹ * x i) * ((vecNorm2 y)⁻¹ * y i))
        = (vecNorm2 x)⁻¹ * (vecNorm2 y)⁻¹ *
            (∑ i : Fin n, x i * y i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 0 := by rw [hxy, mul_zero]
/-- Rescaling a real eigenvector by the inverse of its Euclidean norm preserves
    the same eigenvector equation. -/
theorem rectMatMulVec_vecNorm2_inv_smul_eigenvector {n : ℕ}
    (M : Fin n → Fin n → ℝ) (lambda : ℝ) (x : Fin n → ℝ)
    (hx : rectMatMulVec M x = fun i => lambda * x i) :
    rectMatMulVec M (fun i => (vecNorm2 x)⁻¹ * x i) =
      fun i => lambda * ((vecNorm2 x)⁻¹ * x i) := by
  calc
    rectMatMulVec M (fun i => (vecNorm2 x)⁻¹ * x i)
        = fun i => (vecNorm2 x)⁻¹ * rectMatMulVec M x i := by
          exact rectMatMulVec_smul M (vecNorm2 x)⁻¹ x
    _ = fun i => lambda * ((vecNorm2 x)⁻¹ * x i) := by
          ext i
          rw [congrFun hx i]
          ring
/-- A Euclidean unit vector is nonzero. -/
theorem vecNorm2_eq_one_ne_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : vecNorm2 x = 1) : x ≠ 0 := by
  intro hzero
  have hnorm : vecNorm2 x = 0 := by
    simpa [hzero] using (vecNorm2_zero (n := n))
  linarith
/-- Source-dimension embedding for completing `n` left singular columns by
    `m-n` left-null columns.  The two summands occupy the first `n` and last
    `m-n` coordinates of `Fin m`. -/
def lsSourceLeftCompletionEmbedding {m n : ℕ} (hmn : n ≤ m) :
    Fin n ⊕ Fin (m - n) ↪ Fin m where
  toFun
    | Sum.inl a => Fin.castLE hmn a
    | Sum.inr c => ⟨n + c.val, by omega⟩
  inj' := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            have hval :
                (Fin.castLE hmn a).val = (Fin.castLE hmn b).val :=
              congrArg Fin.val hxy
            exact congrArg Sum.inl (Fin.ext (by simpa using hval))
        | inr c =>
            have hlt : a.val < n := a.isLt
            have hge : n ≤ (n + c.val) := Nat.le_add_right n c.val
            have hval : a.val = n + c.val := by
              simpa using congrArg Fin.val hxy
            omega
    | inr c =>
        cases y with
        | inl b =>
            have hlt : b.val < n := b.isLt
            have hge : n ≤ (n + c.val) := Nat.le_add_right n c.val
            have hval : n + c.val = b.val := by
              simpa using congrArg Fin.val hxy
            omega
        | inr d =>
            have hval : n + c.val = n + d.val :=
              congrArg Fin.val hxy
            have hcd : c.val = d.val := by omega
            exact congrArg Sum.inr (Fin.ext hcd)
theorem vecNorm2_pos_of_ne_zero_lsq {m : ℕ} {b : Fin m → ℝ}
    (hb : b ≠ 0) : 0 < vecNorm2 b := by
  have hbne : vecNorm2 b ≠ 0 := by
    intro hnorm
    apply hb
    ext i
    exact (vecNorm2_eq_zero_iff b).mp hnorm i
  exact lt_of_le_of_ne' (vecNorm2_nonneg b) hbne
theorem vecNorm2Sq_pos_of_ne_zero_lsq {m : ℕ} {b : Fin m → ℝ}
    (hb : b ≠ 0) : 0 < vecNorm2Sq b := by
  have hbpos := vecNorm2_pos_of_ne_zero_lsq hb
  rw [← vecNorm2_sq]
  exact sq_pos_of_pos hbpos
theorem frobNormSqRect_rankOne_real {m n : ℕ} (c : ℝ)
    (r : Fin m → ℝ) (y : Fin n → ℝ) :
    frobNormSqRect (fun i j => c * r i * y j) =
      c ^ 2 * vecNorm2Sq r * vecNorm2Sq y := by
  unfold frobNormSqRect vecNorm2Sq
  calc
    (∑ i : Fin m, ∑ j : Fin n, (c * r i * y j) ^ 2)
        = ∑ i : Fin m, ∑ j : Fin n, (c ^ 2 * r i ^ 2) * y j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = ∑ i : Fin m, (c ^ 2 * r i ^ 2) * ∑ j : Fin n, y j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = (∑ i : Fin m, c ^ 2 * r i ^ 2) * ∑ j : Fin n, y j ^ 2 := by
            rw [Finset.sum_mul]
    _ = c ^ 2 * (∑ i : Fin m, r i ^ 2) * ∑ j : Fin n, y j ^ 2 := by
            congr 1
            rw [Finset.mul_sum]
    _ = c ^ 2 * (∑ i : Fin m, r i ^ 2) * (∑ j : Fin n, y j ^ 2) := by
            ring
theorem rectMatMulVec_add_matrix_lsq {m n : ℕ}
    (M N : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (fun i j => M i j + N i j) x =
      fun i => rectMatMulVec M x i + rectMatMulVec N x i := by
  ext i
  unfold rectMatMulVec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring
/-- Generic row-Gram quadratic-form identity:
    `x^T (B B^T) x = ||B^T x||_2^2`. -/
theorem finiteQuadraticForm_rowGram_transpose_eq_vecNorm2Sq_rectMatMulVec_finiteTranspose
    {m n : ℕ} (B : Fin m → Fin n → ℝ) (p : Fin m → ℝ) :
    finiteQuadraticForm (fun i k : Fin m => ∑ q : Fin n, B i q * B k q) p =
      vecNorm2Sq (rectMatMulVec (finiteTranspose B) p) := by
  unfold finiteQuadraticForm finiteMatVec vecNorm2Sq rectMatMulVec finiteTranspose
  calc
    (∑ i : Fin m, p i * ∑ j : Fin m, (∑ q : Fin n, B i q * B j q) * p j)
        = ∑ i : Fin m, ∑ j : Fin m, ∑ q : Fin n,
            p i * (B i q * B j q) * p j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
    _ = ∑ q : Fin n, ∑ i : Fin m, ∑ j : Fin m,
            p i * (B i q * B j q) * p j := by
            calc
              (∑ i : Fin m, ∑ j : Fin m, ∑ q : Fin n,
                  p i * (B i q * B j q) * p j)
                  = ∑ i : Fin m, ∑ q : Fin n, ∑ j : Fin m,
                      p i * (B i q * B j q) * p j := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [Finset.sum_comm]
              _ = ∑ q : Fin n, ∑ i : Fin m, ∑ j : Fin m,
                      p i * (B i q * B j q) * p j := by
                      rw [Finset.sum_comm]
    _ = ∑ q : Fin n, (∑ i : Fin m, B i q * p i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q _
            rw [pow_two]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
/-- Splitting a finite vector into two coordinate blocks preserves squared
    Euclidean norm additively. -/
theorem lsVecNorm2Sq_append {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2Sq (Fin.append x z) = vecNorm2Sq x + vecNorm2Sq z := by
  unfold vecNorm2Sq
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Triangle inequality for an appended finite vector, viewed as the sum of
    its left and right coordinate embeddings. -/
theorem lsVecNorm2_append_le_add {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2 (Fin.append x z) ≤ vecNorm2 x + vecNorm2 z := by
  let x' : Fin (n + m) → ℝ := Fin.append x (0 : Fin m → ℝ)
  let z' : Fin (n + m) → ℝ := Fin.append (0 : Fin n → ℝ) z
  have happ :
      Fin.append x z = fun k : Fin (n + m) => x' k + z' k := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (n + m) =>
        Fin.append x z k = x' k + z' k)
      ?left ?right k
    · intro i
      simp [x', z', Fin.append_left]
    · intro i
      simp [x', z', Fin.append_right]
  have hx' : vecNorm2 x' = vecNorm2 x := by
    unfold x'
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  have hz' : vecNorm2 z' = vecNorm2 z := by
    unfold z'
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  calc
    vecNorm2 (Fin.append x z) = vecNorm2 (fun k : Fin (n + m) => x' k + z' k) := by
      rw [happ]
    _ ≤ vecNorm2 x' + vecNorm2 z' := vecNorm2_add_le x' z'
    _ = vecNorm2 x + vecNorm2 z := by rw [hx', hz']
/-- The left coordinate block of an appended vector has no larger Euclidean
    norm than the whole vector. -/
theorem lsVecNorm2_left_le_append {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2 x ≤ vecNorm2 (Fin.append x z) := by
  unfold vecNorm2
  apply Real.sqrt_le_sqrt
  rw [lsVecNorm2Sq_append]
  have hz := vecNorm2Sq_nonneg z
  linarith
/-- The right coordinate block of an appended vector has no larger Euclidean
    norm than the whole vector. -/
theorem lsVecNorm2_right_le_append {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2 z ≤ vecNorm2 (Fin.append x z) := by
  unfold vecNorm2
  apply Real.sqrt_le_sqrt
  rw [lsVecNorm2Sq_append]
  have hx := vecNorm2Sq_nonneg x
  linarith
/-- The first `n` coordinates of a vector over `Fin (n+m)` have no larger
    Euclidean norm than the whole vector. -/
theorem lsVecNorm2_left_le_of_sum_coords {n m : ℕ}
    (z : Fin (n + m) → ℝ) :
    vecNorm2 (fun j : Fin n => z (Fin.castAdd m j)) ≤ vecNorm2 z := by
  let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
  let w : Fin m → ℝ := fun j => z (Fin.natAdd n j)
  have hle := lsVecNorm2_left_le_append x w
  have hz : Fin.append x w = z := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (n + m) => Fin.append x w k = z k)
      ?left ?right k
    · intro i
      simp [x, w, Fin.append_left]
    · intro i
      simp [x, w, Fin.append_right]
  simpa [x, w, hz] using hle
/-- The last `m` coordinates of a vector over `Fin (n+m)` have no larger
    Euclidean norm than the whole vector. -/
theorem lsVecNorm2_right_le_of_sum_coords {n m : ℕ}
    (z : Fin (n + m) → ℝ) :
    vecNorm2 (fun j : Fin m => z (Fin.natAdd n j)) ≤ vecNorm2 z := by
  let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
  let w : Fin m → ℝ := fun j => z (Fin.natAdd n j)
  have hle := lsVecNorm2_right_le_append x w
  have hz : Fin.append x w = z := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (n + m) => Fin.append x w k = z k)
      ?left ?right k
    · intro i
      simp [x, w, Fin.append_left]
    · intro i
      simp [x, w, Fin.append_right]
  simpa [x, w, hz] using hle
theorem realVecToEuclidean_ne_zero_of_vecNorm2Sq_ne_zero {m : ℕ}
    {v : Fin m → ℝ} (hv : vecNorm2Sq v ≠ 0) :
    realVecToEuclidean v ≠ 0 := by
  intro hvzero
  have hnorm : vecNorm2 v = 0 := by
    have hnormE : ‖realVecToEuclidean v‖ = 0 := by
      simp [hvzero]
    simpa [realVecToEuclidean_norm] using hnormE
  have hsq : vecNorm2Sq v = 0 := by
    rw [← vecNorm2_sq, hnorm]
    norm_num
  exact hv hsq
theorem complexMatrixRank_ne_card_of_euclideanLin_ker_nonzero
    {m n : ℕ} (A : CMatrix m n) {x : EuclideanSpace ℂ (Fin n)}
    (hxker : complexMatrixEuclideanLin A x = 0) (hxne : x ≠ 0) :
    complexMatrixRank A ≠ n := by
  intro hrank
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    complexMatrixEuclideanLin A
  have hrange :
      Module.finrank ℂ (LinearMap.range T) = n := by
    simpa [T, complexMatrixRank_eq_finrank_range_euclideanLin A] using hrank
  have hdomain :
      Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)
  have hsum :
      Module.finrank ℂ (LinearMap.range T) +
          Module.finrank ℂ (LinearMap.ker T) =
        Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.finrank_range_add_finrank_ker T
  have hker_finrank :
      Module.finrank ℂ (LinearMap.ker T) = 0 := by
    omega
  have hker_bot : LinearMap.ker T = ⊥ := by
    exact (Submodule.finrank_eq_zero).mp hker_finrank
  have hxmem : x ∈ LinearMap.ker T := by
    simpa [T, LinearMap.mem_ker] using hxker
  have hxzero : x = 0 := by
    have hxbot : x ∈ (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin n))) := by
      simpa [hker_bot] using hxmem
    simpa using hxbot
  exact hxne hxzero
theorem complexMatrixRank_eq_card_of_euclideanLin_ker_eq_bot
    {m n : ℕ} (A : CMatrix m n)
    (hker : LinearMap.ker (complexMatrixEuclideanLin A) = ⊥) :
    complexMatrixRank A = n := by
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    complexMatrixEuclideanLin A
  have hsum :
      Module.finrank ℂ (LinearMap.range T) +
          Module.finrank ℂ (LinearMap.ker T) =
        Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.finrank_range_add_finrank_ker T
  have hker0 : Module.finrank ℂ (LinearMap.ker T) = 0 := by
    change Module.finrank ℂ (LinearMap.ker (complexMatrixEuclideanLin A)) = 0
    simp [hker]
  have hdomain : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n :=
    finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)
  have hrange : Module.finrank ℂ (LinearMap.range T) = n := by
    omega
  simpa [T, complexMatrixRank_eq_finrank_range_euclideanLin A] using hrange
theorem complexMatrixEuclideanLin_ker_eq_bot_of_rank_eq_card
    {m n : ℕ} (A : CMatrix m n)
    (hrank : complexMatrixRank A = n) :
    LinearMap.ker (complexMatrixEuclideanLin A) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro z hz
  by_contra hz_ne
  exact complexMatrixRank_ne_card_of_euclideanLin_ker_nonzero A hz hz_ne hrank
theorem frobNormSqRect_add_eq_add_of_inner_eq_zero_lsq {m n : ℕ}
    (A B : Fin m → Fin n → ℝ)
    (hcross : ∑ i : Fin m, ∑ j : Fin n, A i j * B i j = 0) :
    frobNormSqRect (fun i j => A i j + B i j) =
      frobNormSqRect A + frobNormSqRect B := by
  have hexp : frobNormSqRect (fun i j => A i j + B i j) =
      frobNormSqRect A +
        2 * (∑ i : Fin m, ∑ j : Fin n, A i j * B i j) +
      frobNormSqRect B := by
    unfold frobNormSqRect
    simp_rw [show ∀ i : Fin m, ∀ j : Fin n, (A i j + B i j) ^ 2 =
        A i j ^ 2 + 2 * (A i j * B i j) + B i j ^ 2 from fun i j => by ring,
      Finset.sum_add_distrib]
    rw [show ∑ x : Fin m, ∑ x_1 : Fin n, 2 * (A x x_1 * B x x_1) =
        2 * ∑ x : Fin m, ∑ x_1 : Fin n, A x x_1 * B x x_1 from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]]
  rw [hexp, hcross]
  ring
theorem vecNorm2Sq_add_eq_add_of_inner_eq_zero_lsq {m : ℕ}
    (u v : Fin m → ℝ) (hcross : ∑ i : Fin m, u i * v i = 0) :
    vecNorm2Sq (fun i => u i + v i) = vecNorm2Sq u + vecNorm2Sq v := by
  have hexp : vecNorm2Sq (fun i => u i + v i) =
      vecNorm2Sq u + 2 * (∑ i : Fin m, u i * v i) + vecNorm2Sq v := by
    unfold vecNorm2Sq
    simp_rw [show ∀ i : Fin m, (u i + v i) ^ 2 =
        u i ^ 2 + 2 * (u i * v i) + v i ^ 2 from fun i => by ring,
      Finset.sum_add_distrib]
    rw [show ∑ i : Fin m, 2 * (u i * v i) =
        2 * ∑ i : Fin m, u i * v i from by rw [Finset.mul_sum]]
  rw [hexp, hcross]
  ring
theorem matMulVec_orthogonal_mul_transpose_lsq {m : ℕ}
    {Q : Fin m → Fin m → ℝ} (hQ : IsOrthogonal m Q)
    (f : Fin m → ℝ) :
    matMulVec m Q (matMulVec m (matTranspose Q) f) = f := by
  ext i
  calc
    matMulVec m Q (matMulVec m (matTranspose Q) f) i
        = matMulVec m (matMul m Q (matTranspose Q)) f i := by
            exact (matMulVec_matMul m Q (matTranspose Q) f i).symm
    _ = matMulVec m (idMatrix m) f i := by
            have hmat : matMul m Q (matTranspose Q) = idMatrix m := by
              ext a b
              exact hQ.right_inv a b
            rw [hmat]
    _ = f i := by
            exact congrFun (matMulVec_id m f) i
theorem matMulVec_orthogonal_transpose_mul_lsq {m : ℕ}
    {Q : Fin m → Fin m → ℝ} (hQ : IsOrthogonal m Q)
    (f : Fin m → ℝ) :
    matMulVec m (matTranspose Q) (matMulVec m Q f) = f := by
  ext i
  calc
    matMulVec m (matTranspose Q) (matMulVec m Q f) i
        = matMulVec m (matMul m (matTranspose Q) Q) f i := by
            exact (matMulVec_matMul m (matTranspose Q) Q f i).symm
    _ = matMulVec m (idMatrix m) f i := by
            have hmat : matMul m (matTranspose Q) Q = idMatrix m := by
              ext a b
              exact hQ.left_inv a b
            rw [hmat]
    _ = f i := by
            exact congrFun (matMulVec_id m f) i
theorem matMulRectLeft_transpose_action_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) (hQ : IsOrthogonal m Q) :
    (fun j : Fin n =>
      ∑ i : Fin m, matMulRectLeft Q B i j * matMulVec m Q y i) =
      fun j : Fin n => ∑ i : Fin m, B i j * y i := by
  ext j
  unfold matMulRectLeft matMulVec
  calc
    ∑ i : Fin m, (∑ k : Fin m, Q i k * B k j) *
        (∑ l : Fin m, Q i l * y l)
        = ∑ i : Fin m, ∑ k : Fin m, ∑ l : Fin m,
            (Q i k * B k j) * (Q i l * y l) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin m, ∑ l : Fin m, ∑ i : Fin m,
          (Q i k * B k j) * (Q i l * y l) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (∑ i : Fin m, Q i k * Q i l) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (if k = l then 1 else 0) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [hQ.col_orthonormal k l]
    _ = ∑ k : Fin m, B k j * y k := by
            simp [Finset.mem_univ]
/-- The global Householder QR gamma-validity assumption used in Theorem 20.4
    also supplies the triangular-solve gamma-validity assumption. -/
theorem gammaValid_n_of_householderConstructApplyGammaValid
    (fp : FPModel) (m n : ℕ)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    gammaValid fp n := by
  have hK_pos : 0 < householderConstructApplyGammaIndex m := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  exact gammaValid_mono fp (Nat.le_mul_of_pos_right n hK_pos) hvalid
/-- The conservative gamma-factor RHS index used in the current Theorem 20.4
    implementation-backed `Delta f` package is positive for every nonempty
    panel. -/
theorem theorem20_4GammaFactorRhsIndex_pos {n k : ℕ} (hn : 0 < n) :
    0 < householderQRRhsPanelGammaClosedGrowthIndex (n + k) n := by
  have hm : 0 < n + k := Nat.lt_of_lt_of_le hn (Nat.le_add_right n k)
  have hF :
      0 < householderQRRhsPanelGammaClosedGrowthFactor (n + k) n :=
    householderQRRhsPanelGammaClosedGrowthFactor_pos (m := n + k) (p := n) hm
  have hK : 0 < householderConstructApplyGammaIndex (n + k) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hprinted : 0 < n * householderConstructApplyGammaIndex (n + k) :=
    Nat.mul_pos hn hK
  rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
  exact Nat.mul_pos hF hprinted
private theorem vecNorm2Sq_add_eq {m : ℕ} (r e : Fin m → ℝ) :
    vecNorm2Sq (fun i => r i + e i) =
      vecNorm2Sq r + 2 * (∑ i : Fin m, r i * e i) + vecNorm2Sq e := by
  unfold vecNorm2Sq
  simp_rw [show ∀ i : Fin m, (r i + e i) ^ 2 =
      r i ^ 2 + 2 * (r i * e i) + e i ^ 2 from fun i => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
private theorem lsResidual_add_direction {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    lsResidual A b (fun j => x j + d j) =
      fun i => lsResidual A b x i + rectMatMulVec A d i := by
  ext i
  calc
    lsResidual A b (fun j => x j + d j) i
        = rectMatMulVec A (fun j => x j + d j) i - b i := rfl
    _ = (rectMatMulVec A x i + rectMatMulVec A d i) - b i := by
          rw [congrFun (rectMatMulVec_add A x d) i]
    _ = lsResidual A b x i + rectMatMulVec A d i := by
          unfold lsResidual
          ring
private theorem ls_cross_term_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    ∑ i : Fin m, lsResidual A b x i * rectMatMulVec A d i =
      ∑ j : Fin n, d j * (∑ i : Fin m, A i j * lsResidual A b x i) := by
  calc
    ∑ i : Fin m, lsResidual A b x i * rectMatMulVec A d i
        = ∑ i : Fin m, ∑ j : Fin n,
            lsResidual A b x i * (A i j * d j) := by
          unfold rectMatMulVec
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ i : Fin m,
            lsResidual A b x i * (A i j * d j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, d j *
            (∑ i : Fin m, A i j * lsResidual A b x i) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
/-- Squared residual objective after an additive coefficient perturbation. -/
theorem lsObjective_add_direction_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    lsObjective A b (fun j => x j + d j) =
      lsObjective A b x +
        2 * (∑ j : Fin n,
          d j * (∑ i : Fin m, A i j * lsResidual A b x i)) +
        vecNorm2Sq (rectMatMulVec A d) := by
  unfold lsObjective
  rw [lsResidual_add_direction, vecNorm2Sq_add_eq, ls_cross_term_eq]
theorem sum_smul_finiteBasisVec_mul {n : ℕ}
    (j : Fin n) (t : ℝ) (c : Fin n → ℝ) :
    (∑ k : Fin n, (t * finiteBasisVec j k) * c k) = t * c j := by
  unfold finiteBasisVec
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))
theorem linear_term_eq_zero_of_quadratic_nonneg
    {a c : ℝ} (ha : 0 ≤ a)
    (hquad : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * a) :
    c = 0 := by
  by_contra hc
  let t : ℝ := -c / (a + 1)
  have hden_pos : 0 < a + 1 := by linarith
  have hden_ne : a + 1 ≠ 0 := ne_of_gt hden_pos
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hcalc :
      2 * t * c + t ^ 2 * a =
        -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 := by
    dsimp [t]
    field_simp [hden_ne]
    ring
  have hnum_pos : 0 < c ^ 2 * (a + 2) := by nlinarith
  have hden_sq_pos : 0 < (a + 1) ^ 2 := sq_pos_of_pos hden_pos
  have hneg : -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hnum_pos) hden_sq_pos
  have ht := hquad t
  rw [hcalc] at ht
  linarith
/-- Perturbed-data expansion of Higham's signed residual:
    `(b + Delta b) - (A + Delta A)y = (b - A y) + Delta b - Delta A y`. -/
theorem lsResidualHigham_perturbed_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    lsResidualHigham
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y =
      fun i => lsResidualHigham A b y i + Deltab i -
        rectMatMulVec DeltaA y i := by
  ext i
  unfold lsResidualHigham rectMatMulVec
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring
/-- Pythagorean identity for rectangular Frobenius squares when the
    rectangular Frobenius inner product vanishes. -/
theorem frobNormSqRect_add_of_inner_eq_zero {m n : ℕ}
    (A B : Fin m → Fin n → ℝ)
    (hinner : (∑ i : Fin m, ∑ j : Fin n, A i j * B i j) = 0) :
    frobNormSqRect (fun i j => A i j + B i j) =
      frobNormSqRect A + frobNormSqRect B := by
  unfold frobNormSqRect
  calc
    (∑ i : Fin m, ∑ j : Fin n, (A i j + B i j) ^ 2)
        = ∑ i : Fin m, ∑ j : Fin n,
            (A i j ^ 2 + 2 * (A i j * B i j) + B i j ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ =
        (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) +
          2 * (∑ i : Fin m, ∑ j : Fin n, A i j * B i j) +
            ∑ i : Fin m, ∑ j : Fin n, B i j ^ 2 := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ =
        (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) +
          ∑ i : Fin m, ∑ j : Fin n, B i j ^ 2 := by
          rw [hinner]
          ring
/-- Exact top residual `R x - z` in Higham's Section 20.3 augmented
    modified-Gram-Schmidt least-squares factorization. -/
noncomputable def mgsAugmentedTopResidual {n : ℕ}
    (R : Fin n → Fin n → ℝ) (z x : Fin n → ℝ) : Fin n → ℝ :=
  fun k => matMulVec n R x k - z k
/-- Exact expanded residual `Q₁(Rx-z) - ρq` from Higham, 2nd ed.,
    Chapter 20, Section 20.3. -/
noncomputable def mgsAugmentedResidualExpansion {m n : ℕ}
    (Q1 : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (z x : Fin n → ℝ) (rho : ℝ) :
    Fin m → ℝ :=
  fun i => rectMatMulVec Q1 (mgsAugmentedTopResidual R z x) i - rho * q i
theorem mgsAugmented_matVec_eq {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {Q1 : Fin m → Fin n → ℝ}
    {R : Fin n → Fin n → ℝ} (x : Fin n → ℝ)
    (hA : ∀ i j, A i j = ∑ k : Fin n, Q1 i k * R k j)
    (i : Fin m) :
    rectMatMulVec A x i =
      ∑ k : Fin n, Q1 i k * matMulVec n R x k := by
  calc
    rectMatMulVec A x i
        = ∑ j : Fin n, A i j * x j := rfl
    _ = ∑ j : Fin n, (∑ k : Fin n, Q1 i k * R k j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hA i j]
    _ = ∑ j : Fin n, ∑ k : Fin n, (Q1 i k * R k j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ j : Fin n, (Q1 i k * R k j) * x j := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, Q1 i k * matMulVec n R x k := by
          apply Finset.sum_congr rfl
          intro k _
          unfold matMulVec
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
theorem mgsAugmented_sum_diff {m n : ℕ}
    (Q1 : Fin m → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (z x : Fin n → ℝ) (i : Fin m) :
    (∑ k : Fin n, Q1 i k * matMulVec n R x k) -
        ∑ k : Fin n, Q1 i k * z k =
      ∑ k : Fin n, Q1 i k * mgsAugmentedTopResidual R z x k := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold mgsAugmentedTopResidual
  ring
theorem vecNorm2Sq_mgsAugmentedResidualExpansion {m n : ℕ}
    (Q1 : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (z x : Fin n → ℝ) (rho : ℝ)
    (hQ1 : ∀ j k : Fin n, ∑ i : Fin m, Q1 i j * Q1 i k =
      if j = k then 1 else 0)
    (hqorth : ∀ j : Fin n, ∑ i : Fin m, Q1 i j * q i = 0)
    (hqnorm : vecNorm2Sq q = 1) :
    vecNorm2Sq (mgsAugmentedResidualExpansion Q1 q R z x rho) =
      vecNorm2Sq (mgsAugmentedTopResidual R z x) + rho ^ 2 := by
  let y : Fin n → ℝ := mgsAugmentedTopResidual R z x
  have hQnorm :
      (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) ^ 2) =
        vecNorm2Sq y := by
    unfold vecNorm2Sq
    have expand : ∀ i : Fin m,
        (∑ j : Fin n, Q1 i j * y j) ^ 2 =
          ∑ j : Fin n, ∑ k : Fin n,
            Q1 i j * Q1 i k * (y j * y k) := by
      intro i
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [expand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    have factor : ∀ k : Fin n,
        ∑ i : Fin m, Q1 i j * Q1 i k * (y j * y k) =
          (∑ i : Fin m, Q1 i j * Q1 i k) * (y j * y k) := by
      intro k
      rw [← Finset.sum_mul]
    simp_rw [factor, hQ1]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  have hcross :
      (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) * q i) = 0 := by
    calc
      (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) * q i)
          = ∑ i : Fin m, ∑ j : Fin n, (Q1 i j * y j) * q i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ i : Fin m, (Q1 i j * y j) * q i := by
              rw [Finset.sum_comm]
      _ = ∑ j : Fin n, y j * (∑ i : Fin m, Q1 i j * q i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 0 := by
              simp [hqorth]
  have hcrossTerm :
      (∑ i : Fin m, 2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i)) =
        2 * rho *
          (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) * q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hqnorm' : (∑ i : Fin m, (rho * q i) ^ 2) = rho ^ 2 := by
    calc
      (∑ i : Fin m, (rho * q i) ^ 2)
          = rho ^ 2 * ∑ i : Fin m, q i ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = rho ^ 2 := by
              have hqsum : (∑ i : Fin m, q i ^ 2) = 1 := by
                simpa [vecNorm2Sq] using hqnorm
              rw [hqsum, mul_one]
  have hmain :
      (∑ i : Fin m,
          ((∑ j : Fin n, Q1 i j * y j) - rho * q i) ^ 2) =
        (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) ^ 2) -
          (∑ i : Fin m, 2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i)) +
          ∑ i : Fin m, (rho * q i) ^ 2 := by
    calc
      (∑ i : Fin m,
          ((∑ j : Fin n, Q1 i j * y j) - rho * q i) ^ 2)
          = ∑ i : Fin m,
              ((∑ j : Fin n, Q1 i j * y j) ^ 2 -
                2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i) +
                (rho * q i) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
      _ = (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) ^ 2) -
          (∑ i : Fin m, 2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i)) +
          ∑ i : Fin m, (rho * q i) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold vecNorm2Sq mgsAugmentedResidualExpansion rectMatMulVec
  dsimp [y] at hQnorm hcross hcrossTerm
  rw [hmain, hQnorm, hcrossTerm, hcross, hqnorm']
  unfold vecNorm2Sq
  ring
/-- Orthogonal row transformations preserve the rectangular Gram matrix. -/
theorem rectLSGram_matMulRectLeft_orthogonal {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    rectLSGram (matMulRectLeft U A) = rectLSGram A := by
  ext j k
  unfold rectLSGram matMulRectLeft
  have expand : ∀ i : Fin m,
      (∑ p : Fin m, U i p * A p j) *
          (∑ q : Fin m, U i q * A q k) =
        ∑ p : Fin m, ∑ q : Fin m,
          U i p * U i q * (A p j * A q k) := by
    intro i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  have factor : ∀ q : Fin m,
      ∑ i : Fin m, U i p * U i q * (A p j * A q k) =
        (∑ i : Fin m, U i p * U i q) * (A p j * A q k) := by
    intro q
    rw [← Finset.sum_mul]
  simp_rw [factor, hU.col_orthonormal]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
/-- Orthogonal row transformations preserve the rectangular normal-equation
    right-hand side when applied to both `A` and `b`. -/
theorem rectLSRhs_matMulRectLeft_orthogonal {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hU : IsOrthogonal m U) :
    rectLSRhs (matMulRectLeft U A) (matMulVec m U b) = rectLSRhs A b := by
  ext j
  unfold rectLSRhs matMulRectLeft matMulVec
  have expand : ∀ i : Fin m,
      (∑ p : Fin m, U i p * A p j) *
          (∑ q : Fin m, U i q * b q) =
        ∑ p : Fin m, ∑ q : Fin m,
          U i p * U i q * (A p j * b q) := by
    intro i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  have factor : ∀ q : Fin m,
      ∑ i : Fin m, U i p * U i q * (A p j * b q) =
        (∑ i : Fin m, U i p * U i q) * (A p j * b q) := by
    intro q
    rw [← Finset.sum_mul]
  simp_rw [factor, hU.col_orthonormal]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
/-- Nonnegativity of the QR geometric accumulation factor. -/
theorem qrSolveGeometricFactor_nonneg {n : ℕ} {cStep : ℝ}
    (hcStep : 0 ≤ cStep) :
    0 ≤ (1 + cStep) ^ n - 1 := by
  have hbase : 1 ≤ 1 + cStep := by linarith
  exact sub_nonneg.mpr (one_le_pow₀ hbase)
/-- Universal-form route elimination: upper-triangular nonsingular leading
    blocks together with positive active-block mass still do not imply the
    off-diagonal domination field required by
    `StoredQRSourceOffDiagonalControl`.

    This prevents the rectangular QR bottleneck from silently replacing the
    explicit off-diagonal-control hypothesis by the weaker nonbreakdown data
    available from rank/determinant arguments. -/
theorem not_forall_leadingBlock_upper_det_activeBlockPos_implies_offdiag_le_diag :
    ¬ (∀ (A_hat : ℕ → Fin 2 → Fin 2 → ℝ),
      (∀ k (hk : k < 2), ∀ i j : Fin (k + 1), j.val < i.val →
        qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i j = 0) →
      (∀ k (hk : k < 2),
        Matrix.det
          (qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0) →
      (∀ k (hk : k < 2),
        0 < householderActiveBlockNorm2Sq
          ⟨k, hk⟩ ⟨k, hk⟩ (A_hat k)) →
      (∀ k (hk : k < 2), ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i j| ≤
          |qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i i|)) := by
  intro h
  let A_hat : ℕ → Fin 2 → Fin 2 → ℝ := fun _ => diagDominanceCounterexample2
  have hupper : ∀ k (hk : k < 2), ∀ i j : Fin (k + 1), j.val < i.val →
      qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i j = 0 := by
    intro k hk i j hji
    interval_cases k
    · fin_cases i
      fin_cases j
      omega
    · simpa [A_hat, qrLeadingBlock, qrLeadingRow, qrLeadingColumn] using
        diagDominanceCounterexample2_upper
          (qrLeadingRow 2 1 (Nat.succ_le_iff.mpr hk) i)
          (qrLeadingColumn 2 1 hk j)
          (by simpa [qrLeadingRow, qrLeadingColumn] using hji)
  have hdetLead : ∀ k (hk : k < 2),
      Matrix.det
        (qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro k hk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · have hblock :
          (qrLeadingBlock diagDominanceCounterexample2
              (Nat.succ_le_iff.mpr hk) hk :
            Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ) =
            (fun _ _ => (1 : ℝ)) := by
        ext i j
        fin_cases i
        fin_cases j
        norm_num [qrLeadingBlock, qrLeadingRow, qrLeadingColumn,
          diagDominanceCounterexample2]
      rw [hblock, Matrix.det_fin_one]
      norm_num
    · have hblock :
          (qrLeadingBlock diagDominanceCounterexample2
              (Nat.succ_le_iff.mpr hk) hk :
            Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ) =
            (diagDominanceCounterexample2 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [qrLeadingBlock, qrLeadingRow, qrLeadingColumn]
      simpa [hblock] using diagDominanceCounterexample2_det_ne_zero
  have hactive : ∀ k (hk : k < 2),
      0 < householderActiveBlockNorm2Sq ⟨k, hk⟩ ⟨k, hk⟩ (A_hat k) := by
    intro k hk
    interval_cases k
    · simpa [A_hat] using
        householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
          (p := (⟨0, by norm_num⟩ : Fin 2))
          (k := (⟨0, by norm_num⟩ : Fin 2))
          (A := diagDominanceCounterexample2)
          ⟨⟨0, by norm_num⟩, by norm_num,
            ⟨0, by norm_num⟩, by norm_num,
            by norm_num [diagDominanceCounterexample2]⟩
    · simpa [A_hat] using
        householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
          (p := (⟨1, by norm_num⟩ : Fin 2))
          (k := (⟨1, by norm_num⟩ : Fin 2))
          (A := diagDominanceCounterexample2)
          ⟨⟨1, by norm_num⟩, by norm_num,
            ⟨1, by norm_num⟩, by norm_num,
            by norm_num [diagDominanceCounterexample2]⟩
  have hoffdiag := h A_hat hupper hdetLead hactive
  have hbad :=
    hoffdiag 1 (by norm_num)
      (⟨0, by norm_num⟩ : Fin (1 + 1))
      (⟨1, by norm_num⟩ : Fin (1 + 1))
      (by norm_num)
  norm_num [A_hat, qrLeadingBlock, qrLeadingRow, qrLeadingColumn,
    diagDominanceCounterexample2] at hbad
/-- The previous transposed leading block is nonsingular when the current
    leading block satisfies the repository's local diagonal-dominance predicate.

    The previous block is the transpose orientation of the top-left `k x k`
    part of the current `(k+1) x (k+1)` leading block.  Thus the
    upper-triangular/nonzero-diagonal fields inside `IsDiagDominantUpper`
    provide exactly the local lower-triangular/nonzero-diagonal certificate
    required by the QR determinant bridge. -/
theorem qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hkmPrev : k ≤ m) (hkmLead : k + 1 ≤ m) (hk : k < n)
    (hDD : IsDiagDominantUpper (k + 1) (qrLeadingBlock A hkmLead hk)) :
    Matrix.det
      (qrPreviousLeadingBlockTranspose A hkmPrev hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
  classical
  apply
    qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero
      A hkmPrev hk
  · intro i j hij
    have hzero := hDD.1 (Fin.castSucc j) (Fin.castSucc i) (by simpa using hij)
    simpa [qrPreviousLeadingBlockTranspose, qrLeadingBlock, qrPrefixRow,
      qrLeadingRow, qrPreviousColumn, qrLeadingColumn] using hzero
  · intro r
    have hdiag := hDD.2.1 (Fin.castSucc r)
    simpa [qrPreviousLeadingBlockTranspose, qrLeadingBlock, qrPrefixRow,
      qrLeadingRow, qrPreviousColumn, qrLeadingColumn] using hdiag

/-- Equivalence from a right-Gram basis index to the ordered singular-value
    coordinate selected by the same mathlib Hermitian reindexing. -/
noncomputable def rectRightGramBasisOrderedEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := rectRightGramBasisOrderedIndex n
  invFun i := rectRightGramOrderedEigenbasisEquiv n (finCardIndex n i)
  left_inv := by
    intro b
    change rectRightGramOrderedEigenbasisEquiv n
        (finCardIndex n (rectRightGramBasisOrderedIndex n b)) = b
    rw [finCardIndex_rectRightGramBasisOrderedIndex]
    exact (rectRightGramOrderedEigenbasisEquiv n).apply_symm_apply b
  right_inv := by
    intro i
    apply Fin.ext
    have h :=
      finCardIndex_rectRightGramBasisOrderedIndex n
        (rectRightGramOrderedEigenbasisEquiv n (finCardIndex n i))
    rw [(rectRightGramOrderedEigenbasisEquiv n).symm_apply_apply] at h
    simpa [finCardIndex] using congrArg Fin.val h
/-- Positive right-Gram singular branches give the transpose-side singular-pair
    equation for the real basis-indexed SVD candidates.  This is the missing
    algebraic half of `u_a = A v_a / sigma_a`, specialized to the finite
    real-Gram infrastructure already used elsewhere in the repository. -/
theorem rectRightGramLeftSingularFromEigenbasis_transpose_action_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (a : Fin n) :
    (fun j : Fin n => ∑ i : Fin m,
      A i j * rectRightGramLeftSingularFromEigenbasis A i a) =
        fun j => rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  ext j
  let τ := rectRightGramBasisSingularValue A a
  have hτ : τ ≠ 0 := ne_of_gt (hpos a)
  have heig := rectRightGramEigenbasis_eigenvector A a j
  have hsq := rectRightGramBasisSingularValue_sq_eq A a
  calc
    ∑ i : Fin m, A i j * rectRightGramLeftSingularFromEigenbasis A i a
        = (1 / τ) * ∑ i : Fin m,
            A i j * rectRightGramProjectedColumn A i a := by
          unfold rectRightGramLeftSingularFromEigenbasis
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (1 / τ) * ∑ k : Fin n,
          rectRightGram A j k * rectRightGramEigenbasis A k a := by
          congr 1
          unfold rectRightGramProjectedColumn rectRightGram
          calc
            ∑ i : Fin m,
                A i j * (∑ k : Fin n,
                  A i k * rectRightGramEigenbasis A k a)
                = ∑ i : Fin m, ∑ k : Fin n,
                    A i j * (A i k * rectRightGramEigenbasis A k a) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.mul_sum]
            _ = ∑ k : Fin n, ∑ i : Fin m,
                    A i j * (A i k * rectRightGramEigenbasis A k a) := by
                    rw [Finset.sum_comm]
            _ = ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) *
                    rectRightGramEigenbasis A k a := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
    _ = (1 / τ) *
          (rectRightGramEigenvalue A a * rectRightGramEigenbasis A j a) := by
          rw [heig]
    _ = τ * rectRightGramEigenbasis A j a := by
          have hτsq : τ ^ 2 = rectRightGramEigenvalue A a := by
            simpa [τ] using hsq
          rw [← hτsq]
          field_simp [hτ]
/-- Full column rank in the real column-map sense forces every basis-indexed
    right-Gram singular value to be positive.  A zero branch would make the
    corresponding orthonormal right-Gram eigenvector lie in the kernel of `A`. -/
theorem rectRightGramBasisSingularValue_pos_of_rectMatMulVec_injective
    {m n : ℕ} {A : Fin m → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec A)) (a : Fin n) :
    0 < rectRightGramBasisSingularValue A a := by
  refine lt_of_le_of_ne' (rectRightGramBasisSingularValue_nonneg A a) ?_
  intro hzero
  let v : Fin n → ℝ := fun j => rectRightGramEigenbasis A j a
  have hAv_zero : rectMatMulVec A v = 0 := by
    ext i
    have hp :=
      rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero
        A a hzero i
    simpa [v, rectMatMulVec, rectRightGramProjectedColumn] using hp
  have hv_zero : v = 0 := by
    apply hinj
    rw [hAv_zero]
    ext i
    simp [rectMatMulVec]
  have hnorm_one : (∑ j : Fin n, v j * v j) = 1 := by
    have h := rectRightGramEigenbasis_col_orthonormal A a a
    simpa [v, idMatrix] using h
  have hnorm_zero : (∑ j : Fin n, v j * v j) = 0 := by
    simp [hv_zero]
  linarith
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    construction of the `m-n` left-nullspace branch family for the real
    right-Gram route.  Under `n <= m` and real full-column-rank injectivity,
    the constructed left singular vectors can be completed to an orthonormal
    `m`-column table; the added tail columns are orthonormal and annihilated by
    `A^T`. -/
theorem exists_rightGram_leftNull_branch_data_of_rectMatMulVec_injective
    {m n : ℕ} (hmn : n ≤ m) {A : Fin m → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec A)) :
    ∃ w : Fin (m - n) → Fin m → ℝ,
      (∀ k : Fin (m - n), vecNorm2Sq (w k) = 1) ∧
        (∀ k l : Fin (m - n),
          k ≠ l → (∑ r : Fin m, w k r * w l r) = 0) ∧
        (∀ k : Fin (m - n), ∀ j : Fin n,
          ∑ r : Fin m, A r j * w k r = 0) := by
  classical
  let U : Fin m → Fin n → ℝ :=
    fun r a => rectRightGramLeftSingularFromEigenbasis A r a
  let Utail₀ : Fin m → Fin (m - n) → ℝ := fun _ _ => 0
  let s : Set (Fin n ⊕ Fin (m - n)) := fun bc =>
    match bc with
    | Sum.inl _ => True
    | Sum.inr _ => False
  have hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a :=
    fun a => rectRightGramBasisSingularValue_pos_of_rectMatMulVec_injective
      (A := A) hinj a
  have hhead : ∀ a : Fin n, Sum.inl a ∈ s := by
    intro a
    exact True.intro
  have hpartial : ∀ a b : s,
      (∑ i : Fin m,
        leftBasisBlock U Utail₀ i a *
          leftBasisBlock U Utail₀ i b) =
        if a = b then 1 else 0 := by
    intro a b
    rcases a with ⟨bc, hbc⟩
    rcases b with ⟨bd, hbd⟩
    cases bc with
    | inl ca =>
        cases bd with
        | inl db =>
            have horth :=
              rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
                A hpos ca db
            have hite :
                idMatrix n ca db =
                  if (⟨Sum.inl ca, hbc⟩ : s) = ⟨Sum.inl db, hbd⟩ then
                    1
                  else
                    0 := by
              by_cases hcd : ca = db
              · subst db
                simp [idMatrix]
              · have hsub :
                    (⟨Sum.inl ca, hbc⟩ : s) ≠ ⟨Sum.inl db, hbd⟩ := by
                  intro hEq
                  have hval :
                      (Sum.inl ca : Fin n ⊕ Fin (m - n)) = Sum.inl db :=
                    congrArg Subtype.val hEq
                  exact hcd (Sum.inl.inj hval)
                simp [idMatrix, hcd, hsub]
            calc
              (∑ i : Fin m,
                leftBasisBlock U Utail₀ i (Sum.inl ca) *
                  leftBasisBlock U Utail₀ i (Sum.inl db))
                  = idMatrix n ca db := by
                    simpa [U, Utail₀, leftBasisBlock] using horth
              _ = if (⟨Sum.inl ca, hbc⟩ : s) = ⟨Sum.inl db, hbd⟩ then
                    1
                  else
                    0 := hite
        | inr db =>
            cases hbd
    | inr ca =>
        cases hbc
  obtain ⟨Utail, _hpreserve, hcols⟩ :=
    partialLeftBasisBlock_exists_replacement_tail
      (lsSourceLeftCompletionEmbedding hmn) U Utail₀ s hhead hpartial
  let w : Fin (m - n) → Fin m → ℝ := fun k r => Utail r k
  have hfields :=
    leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
      U Utail hcols
  have hw : ∀ k : Fin (m - n), vecNorm2Sq (w k) = 1 := by
    intro k
    have h := hfields.2.2 k k
    simpa [w, vecNorm2Sq, idMatrix, pow_two] using h
  have hnull : ∀ k l : Fin (m - n),
      k ≠ l → (∑ r : Fin m, w k r * w l r) = 0 := by
    intro k l hkl
    have h := hfields.2.2 k l
    simpa [w, idMatrix, hkl] using h
  have hATw : ∀ k : Fin (m - n), ∀ j : Fin n,
      ∑ r : Fin m, A r j * w k r = 0 := by
    intro k j
    have hcross := hfields.2.1
    calc
      ∑ r : Fin m, A r j * w k r
          = ∑ r : Fin m,
              (∑ a : Fin n,
                U r a * rectRightGramBasisSingularValue A a *
                  rectRightGramEigenbasis A j a) * w k r := by
              apply Finset.sum_congr rfl
              intro r _
              rw [rectRightGram_fullPositive_basisSVD_representation A hpos r j]
      _ = ∑ r : Fin m, ∑ a : Fin n,
              (U r a * w k r) *
                (rectRightGramBasisSingularValue A a *
                  rectRightGramEigenbasis A j a) := by
              apply Finset.sum_congr rfl
              intro r _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a _
              ring
      _ = ∑ a : Fin n, ∑ r : Fin m,
              (U r a * w k r) *
                (rectRightGramBasisSingularValue A a *
                  rectRightGramEigenbasis A j a) := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fin n,
              (rectRightGramBasisSingularValue A a *
                rectRightGramEigenbasis A j a) *
                (∑ r : Fin m, U r a * w k r) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              ring
      _ = 0 := by
              apply Finset.sum_eq_zero
              intro a _
              rw [hcross a k]
              ring
  exact ⟨w, hw, hnull, hATw⟩

/-- The entrywise-absolute inverse block displayed after Theorem 20.2:
`[[|I-AA^+|, |A^+|^T], [|A^+|, |(A^T A)^-1|]]`. -/
noncomputable def higham20AlternativeAbsInverseBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append
        (fun k : Fin m => |lsAugmentedProjectionBlock A Aplus i k|)
        (fun j : Fin n => |Aplus j i|))
    (fun j : Fin n =>
      Fin.append
        (fun i : Fin m => |Aplus j i|)
        (fun k : Fin n => |gramInv j k|))

/-- The off-diagonal componentwise data block
`[[0,E],[E^T,0]]` displayed after Theorem 20.2. -/
noncomputable def higham20AlternativeOffDiagonalBlock {m n : Nat}
    (E : Fin m -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append (fun _ : Fin m => 0) (fun j : Fin n => E i j))
    (fun j : Fin n =>
      Fin.append (fun i : Fin m => E i j) (fun _ : Fin n => 0))

/-- The exact matrix product occurring inside the alternative-bound norm. -/
noncomputable def higham20AlternativeCouplingMatrix {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) (E : Fin m -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  rectMatMul (higham20AlternativeAbsInverseBlock A Aplus gramInv)
    (higham20AlternativeOffDiagonalBlock E)

theorem higham20AlternativeOffDiagonalBlock_mulVec {m n : Nat}
    (E : Fin m -> Fin n -> Real) (u : Fin m -> Real) (v : Fin n -> Real) :
    rectMatMulVec (higham20AlternativeOffDiagonalBlock E) (Fin.append u v) =
      Fin.append (rectMatMulVec E v)
        (fun j => Finset.univ.sum (fun i : Fin m => E i j * u i)) := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [higham20AlternativeOffDiagonalBlock, rectMatMulVec,
      Fin.sum_univ_add]
  · intro j
    simp [higham20AlternativeOffDiagonalBlock, rectMatMulVec,
      Fin.sum_univ_add]

theorem higham20AlternativeAbsInverseBlock_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) :
    forall i j, 0 <= higham20AlternativeAbsInverseBlock A Aplus gramInv i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj <;>
      simp [higham20AlternativeAbsInverseBlock]
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj <;>
      simp [higham20AlternativeAbsInverseBlock]

theorem higham20AlternativeOffDiagonalBlock_nonneg {m n : Nat}
    {E : Fin m -> Fin n -> Real} (hE : forall i j, 0 <= E i j) :
    forall i j, 0 <= higham20AlternativeOffDiagonalBlock E i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simp [higham20AlternativeOffDiagonalBlock]
    · simpa [higham20AlternativeOffDiagonalBlock] using hE ii jj
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simpa [higham20AlternativeOffDiagonalBlock] using hE jj ii
    · simp [higham20AlternativeOffDiagonalBlock]

theorem higham20AlternativeCouplingMatrix_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real)
    {E : Fin m -> Fin n -> Real} (hE : forall i j, 0 <= E i j) :
    forall i j, 0 <= higham20AlternativeCouplingMatrix A Aplus gramInv E i j := by
  intro i j
  unfold higham20AlternativeCouplingMatrix rectMatMul
  exact Finset.sum_nonneg (fun k _ => mul_nonneg
    (higham20AlternativeAbsInverseBlock_nonneg A Aplus gramInv i k)
    (higham20AlternativeOffDiagonalBlock_nonneg hE k j))

/-- Euclidean norm is bounded by the sum of coordinate absolute values. -/
theorem higham20_vecNorm2_le_sum_abs {d : Nat} (v : Fin d → Real) :
    vecNorm2 v ≤ ∑ i : Fin d, |v i| := by
  have hsq : vecNorm2 v ^ 2 ≤ (∑ i : Fin d, |v i|) ^ 2 := by
    rw [vecNorm2_sq]
    exact vecNorm2Sq_le_sum_abs_sq v
  have hv : 0 ≤ vecNorm2 v := vecNorm2_nonneg v
  have hs : 0 ≤ ∑ i : Fin d, |v i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  nlinarith

/-- The repository's complex `L²` norm agrees with `vecNorm2` on embedded
real vectors. -/
theorem higham20_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2
    {d : Nat} (v : Fin d → Real) :
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex v) =
      vecNorm2 v := by
  calc
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex v) =
        norm (WithLp.toLp (2 : ENNReal) (realVecToComplex v)) :=
      complexVecLpNorm_two_eq_toLp (realVecToComplex v)
    _ = norm (realVecToEuclidean v) := by rfl
    _ = vecNorm2 v := realVecToEuclidean_norm v

theorem higham20Theorem20_4_frobNorm_smul_nonneg {m : ℕ}
    (a : ℝ) (M : Fin m → Fin m → ℝ) (ha : 0 ≤ a) :
    frobNorm (fun i j => a * M i j) = a * frobNorm M := by
  rw [← frobNormRect_eq_frobNormFn, frobNormRect_smul,
    frobNormRect_eq_frobNormFn, abs_of_nonneg ha]

theorem higham20Theorem20_4_abs_matMulRectLeft_le {m n : ℕ}
    (L : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    |matMulRectLeft L B i j| ≤
      matMulRect m m n (fun r s => |L r s|) (fun r s => |B r s|) i j := by
  unfold matMulRectLeft matMulRect
  calc
    |∑ k : Fin m, L i k * B k j| ≤
        ∑ k : Fin m, |L i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin m, |L i k| * |B k j| := by simp [abs_mul]

theorem higham20Theorem20_4_matMulRect_mono_right {m n : ℕ}
    (L : Fin m → Fin m → ℝ) (B C : Fin m → Fin n → ℝ)
    (hL : ∀ i j, 0 ≤ L i j) (hBC : ∀ i j, B i j ≤ C i j)
    (i : Fin m) (j : Fin n) :
    matMulRect m m n L B i j ≤ matMulRect m m n L C i j := by
  unfold matMulRect
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_left (hBC k j) (hL i k)

theorem higham20Theorem20_4_matMulRect_mono_left {m n : ℕ}
    (L M : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (hLM : ∀ i j, L i j ≤ M i j) (hB : ∀ i j, 0 ≤ B i j)
    (i : Fin m) (j : Fin n) :
    matMulRect m m n L B i j ≤ matMulRect m m n M B i j := by
  unfold matMulRect
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_right (hLM i k) (hB k j)

end NumStability
