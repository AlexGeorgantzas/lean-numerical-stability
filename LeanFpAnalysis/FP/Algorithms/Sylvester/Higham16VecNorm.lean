-- Algorithms/Sylvester/Higham16VecNorm.lean
--
-- Vec/Frobenius norm bridges for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.

import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16PerturbationSigmaMin
import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16PsiSigmaMin
import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16LyapunovSigmaMin

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    vectorization is an isometry from the Frobenius squared norm to the
    Euclidean squared norm over the product index used by `Matrix.vec`. -/
theorem finiteVecNorm2Sq_vec_eq_frobNormSq (m n : Nat)
    (A : Matrix (Fin m) (Fin n) Real) :
    finiteVecNorm2Sq (Matrix.vec A) = frobNormSq A := by
  unfold finiteVecNorm2Sq frobNormSq
  calc
    (Finset.univ.sum fun p : Prod (Fin n) (Fin m) => Matrix.vec A p ^ 2)
        = Finset.univ.sum
            (fun j : Fin n => Finset.univ.sum (fun i : Fin m => A i j ^ 2)) := by
            change
              (Finset.univ.sum fun p : Prod (Fin n) (Fin m) =>
                A p.2 p.1 ^ 2) =
              Finset.univ.sum
                (fun j : Fin n => Finset.univ.sum (fun i : Fin m => A i j ^ 2))
            rw [Fintype.sum_prod_type' (fun j i => A i j ^ 2)]
    _ = Finset.univ.sum
            (fun i : Fin m => Finset.univ.sum (fun j : Fin n => A i j ^ 2)) := by
            rw [Finset.sum_comm]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    vectorization is an isometry from the Frobenius norm to the Euclidean norm
    over the product index used by `Matrix.vec`. -/
theorem finiteVecNorm2_vec_eq_frobNorm (m n : Nat)
    (A : Matrix (Fin m) (Fin n) Real) :
    finiteVecNorm2 (Matrix.vec A) = frobNorm A := by
  unfold finiteVecNorm2
  rw [finiteVecNorm2Sq_vec_eq_frobNormSq m n A,
    frobNorm_eq_sqrt_frobNormSq]

/-- Finite Gram matrix `P^T P` for an arbitrary finite index type.  This local
    Chapter 16 helper keeps the printed product-index vec coefficient without
    reindexing it through `Fin (n*n)`. -/
noncomputable def finiteMatrixGram {ι : Type*} [Fintype ι]
    (P : Matrix ι ι Real) : ι -> ι -> Real :=
  fun i j => Finset.sum Finset.univ fun k : ι => P k i * P k j

/-- The finite Gram matrix `P^T P` is symmetric. -/
theorem isSymmetricFiniteMatrix_finiteMatrixGram
    {ι : Type*} [Fintype ι] (P : Matrix ι ι Real) :
    IsSymmetricFiniteMatrix (finiteMatrixGram P) := by
  intro i j
  unfold finiteMatrixGram
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Gram quadratic-form identity over an arbitrary finite index type:
    `x^T P^T P x = ||P x||_2^2`. -/
theorem finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec
    {ι : Type*} [Fintype ι] (P : Matrix ι ι Real) (x : ι -> Real) :
    finiteQuadraticForm (finiteMatrixGram P) x =
      finiteVecNorm2Sq (Matrix.mulVec P x) := by
  have hmv : forall i : ι,
      finiteMatVec (finiteMatrixGram P) x i =
        Finset.sum Finset.univ
          (fun k : ι => P k i * Matrix.mulVec P x k) := by
    intro i
    unfold finiteMatVec finiteMatrixGram Matrix.mulVec dotProduct
    calc
      (Finset.univ.sum fun j : ι =>
          (Finset.univ.sum fun k : ι => P k i * P k j) * x j)
          = Finset.univ.sum fun j : ι =>
              Finset.univ.sum fun k : ι => (P k i * P k j) * x j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
      _ = Finset.univ.sum fun k : ι =>
              Finset.univ.sum fun j : ι => (P k i * P k j) * x j := by
              rw [Finset.sum_comm]
      _ = Finset.univ.sum fun k : ι =>
              P k i * Finset.univ.sum fun j : ι => P k j * x j := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
  unfold finiteQuadraticForm finiteVecNorm2Sq
  calc
    (Finset.univ.sum fun i : ι => x i * finiteMatVec (finiteMatrixGram P) x i)
        = Finset.univ.sum fun i : ι =>
            x i *
              Finset.univ.sum
                (fun k : ι => P k i * Matrix.mulVec P x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hmv i]
    _ = Finset.univ.sum fun i : ι =>
          Finset.univ.sum fun k : ι =>
            x i * (P k i * Matrix.mulVec P x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = Finset.univ.sum fun k : ι =>
          Finset.univ.sum fun i : ι =>
            x i * (P k i * Matrix.mulVec P x k) := by
            rw [Finset.sum_comm]
    _ = Finset.univ.sum fun k : ι =>
          Matrix.mulVec P x k *
            Finset.univ.sum fun i : ι => P k i * x i := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = Finset.univ.sum fun k : ι =>
          Matrix.mulVec P x k * Matrix.mulVec P x k := by
            apply Finset.sum_congr rfl
            intro k _
            unfold Matrix.mulVec dotProduct
            rw [mul_comm]
    _ = Finset.univ.sum fun k : ι => Matrix.mulVec P x k ^ 2 := by
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- Singular-value lower-bound certificate for an arbitrary finite-index real
    matrix, stated with the repository's generic finite Euclidean norm. -/
theorem finiteMatrixGram_sigmaMin_mul_finiteVecNorm2_le_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall a : ι,
      lam <= finiteHermitianEigenvalues (finiteMatrixGram P)
        (isSymmetricFiniteMatrix_finiteMatrixGram P) a)
    (x : ι -> Real) :
    Real.sqrt lam * finiteVecNorm2 x <=
      finiteVecNorm2 (Matrix.mulVec P x) := by
  have hray :=
    rayleigh_lower_bound_of_le_finiteHermitianEigenvalues
      (finiteMatrixGram P) (isSymmetricFiniteMatrix_finiteMatrixGram P)
      hEig x
  have hleft_sq :
      (Real.sqrt lam * finiteVecNorm2 x) ^ 2 =
        lam * finiteVecNorm2Sq x := by
    rw [mul_pow, Real.sq_sqrt hlam, finiteVecNorm2_sq]
  have hright_sq :
      finiteVecNorm2 (Matrix.mulVec P x) ^ 2 =
        finiteVecNorm2Sq (Matrix.mulVec P x) :=
    finiteVecNorm2_sq _
  have hsq :
      (Real.sqrt lam * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2 (Matrix.mulVec P x) ^ 2 := by
    rw [hleft_sq, hright_sq,
      <- finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec P x]
    exact hray
  exact le_of_sq_le_sq_of_nonneg (finiteVecNorm2_nonneg _) hsq

/-- A scalar-identity Loewner lower bound controls every locally named
    Hermitian eigenvalue from below.  This is the lower-side companion to
    `finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id`. -/
theorem le_finiteHermitianEigenvalues_of_finiteLoewnerLe_smul_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι -> ι -> Real) (hM : IsSymmetricFiniteMatrix M) {c : Real}
    (hLe : finiteLoewnerLe (fun i j => c * finiteIdMatrix i j) M) (a : ι) :
    c <= finiteHermitianEigenvalues M hM a := by
  let v : ι -> Real :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian M hM).eigenvectorBasis a)
  have hq := hLe v
  have heig :=
    finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq
      M hM a
  have hnorm :=
    finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one M hM a
  change finiteQuadraticForm (fun i j => c * finiteIdMatrix i j) v <=
    finiteQuadraticForm M v at hq
  rw [finiteQuadraticForm_smul_finiteIdMatrix, heig, hnorm] at hq
  simpa using hq

/-- A concrete sigma-min norm lower bound for `P` implies the corresponding
    lower bound on every eigenvalue of its finite Gram matrix `P^T P`. -/
theorem finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι Real) {sigma : Real} (hsigma : 0 <= sigma)
    (hCoeff : forall x : ι -> Real,
      sigma * finiteVecNorm2 x <= finiteVecNorm2 (Matrix.mulVec P x)) :
    forall a : ι,
      sigma ^ 2 <= finiteHermitianEigenvalues (finiteMatrixGram P)
        (isSymmetricFiniteMatrix_finiteMatrixGram P) a := by
  intro a
  refine
    le_finiteHermitianEigenvalues_of_finiteLoewnerLe_smul_id
      (finiteMatrixGram P) (isSymmetricFiniteMatrix_finiteMatrixGram P) ?_ a
  intro x
  have hcoeff := hCoeff x
  have hleft_nonneg : 0 <= sigma * finiteVecNorm2 x :=
    mul_nonneg hsigma (finiteVecNorm2_nonneg x)
  have hright_nonneg : 0 <= finiteVecNorm2 (Matrix.mulVec P x) :=
    finiteVecNorm2_nonneg _
  have habs :
      |sigma * finiteVecNorm2 x| <=
        |finiteVecNorm2 (Matrix.mulVec P x)| := by
    simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using hcoeff
  have hsq :
      (sigma * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2 (Matrix.mulVec P x) ^ 2 :=
    (sq_le_sq).mpr habs
  have hsq_bound :
      sigma ^ 2 * finiteVecNorm2Sq x <=
        finiteVecNorm2Sq (Matrix.mulVec P x) := by
    simpa [mul_pow, finiteVecNorm2_sq] using hsq
  change finiteQuadraticForm
      (fun i j : ι => sigma ^ 2 * finiteIdMatrix i j) x <=
    finiteQuadraticForm (finiteMatrixGram P) x
  rw [finiteQuadraticForm_smul_finiteIdMatrix,
    finiteQuadraticForm_finiteMatrixGram_eq_finiteVecNorm2Sq_mulVec]
  exact hsq_bound

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient gives the coefficient lower bound used by the Chapter 16
    sigma-min wrappers. -/
theorem sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      Real.sqrt lam * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  intro x
  exact
    finiteMatrixGram_sigmaMin_mul_finiteVecNorm2_le_mulVec
      (sylvesterVecCoeff n n A B) hlam hEig x

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient gives the coefficient lower bound used by the Chapter 16
    Lyapunov sigma-min wrappers. -/
theorem lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues (n : Nat)
    (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      Real.sqrt lam * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  intro x
  exact
    finiteMatrixGram_sigmaMin_mul_finiteVecNorm2_le_mulVec
      (lyapunovVecCoeff n A) hlam hEig x

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a positive lower bound for the concrete vectorized Sylvester coefficient
    gives the operator lower bound consumed by the sigma-min Chapter 16
    perturbation and condition-number wrappers. -/
theorem sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  intro Y
  have h := hCoeff (Matrix.vec Y)
  rw [sylvesterVecCoeff_mulVec_vec n n A B Y] at h
  rwa [finiteVecNorm2_vec_eq_frobNorm n n Y,
    sylvesterOpRect_square_eq_sylvesterOp n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n (sylvesterOp n A B Y)] at h

/-- Higham, 2nd ed., Chapter 16.1 and (16.23)-(16.26):
    a Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient gives the Frobenius lower bound for the Sylvester operator. -/
theorem sylvesterOp_sigmaMin_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    forall Y : Fin n -> Fin n -> Real,
      Real.sqrt lam * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  exact
    sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B (Real.sqrt lam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B hlam hEig)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    in the diagonal case, a uniform lower bound on the coefficient magnitudes
    `|a_i - b_j|` gives the concrete vectorized coefficient lower bound. -/
theorem sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) := by
  classical
  intro x
  let d : Prod (Fin n) (Fin n) -> Real := fun p => a p.2 - b p.1
  have hmul :
      Matrix.mulVec
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x =
        fun p => d p * x p := by
    rw [sylvesterVecCoeff_diagonal]
    ext p
    simp [d, Matrix.mulVec, dotProduct, Matrix.diagonal]
  have hsquares :
      sigma ^ 2 * finiteVecNorm2Sq x <=
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    unfold finiteVecNorm2Sq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _hp
    have hleft : -|d p| <= sigma := by
      linarith [abs_nonneg (d p), hsigma]
    have hsq_abs : sigma ^ 2 <= |d p| ^ 2 := by
      exact sq_le_sq' hleft (by simpa [d] using hgap p.2 p.1)
    calc
      sigma ^ 2 * x p ^ 2 <= |d p| ^ 2 * x p ^ 2 :=
        mul_le_mul_of_nonneg_right hsq_abs (sq_nonneg (x p))
      _ = (d p * x p) ^ 2 := by
        rw [sq_abs]
        ring
  have hleft_sq :
      (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2Sq x := by
    rw [show (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2 x ^ 2 by ring,
      finiteVecNorm2_sq]
  have hright_sq :
      finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) ^ 2 =
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    rw [hmul, finiteVecNorm2_sq]
  have hsq :
      (sigma * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) ^ 2 := by
    simpa [hleft_sq, hright_sq] using hsquares
  have hleft_nonneg : 0 <= sigma * finiteVecNorm2 x :=
    mul_nonneg hsigma (finiteVecNorm2_nonneg x)
  have hright_nonneg :
      0 <= finiteVecNorm2
        (Matrix.mulVec
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) x) :=
    finiteVecNorm2_nonneg _
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3),
    diagonal case: a uniform lower bound on `|a_i - b_j|` gives a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvesterVecCoeff_diagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b))) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)) hsigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.1 and equation (16.26), diagonal case:
    the concrete diagonal vec/Kronecker lower bound transfers to the
    Frobenius lower bound for the Sylvester operator. -/
theorem sylvesterOp_sigmaMin_diagonal_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) Y) := by
  exact
    sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b) sigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hsigma) hgap)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a positive lower bound for the concrete vectorized Lyapunov coefficient
    gives the Lyapunov operator lower bound consumed by the sigma-min
    condition-number wrapper. -/
theorem lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  intro Y
  have h := hCoeff (Matrix.vec Y)
  rw [lyapunovVecCoeff_mulVec_vec n A Y] at h
  let Amat : Matrix (Fin n) (Fin n) Real := A
  let Ymat : Matrix (Fin n) (Fin n) Real := Y
  have hLY :
      Amat * Ymat + Ymat * Matrix.transpose Amat =
        lyapunovOp n A Y := by
    ext i j
    simp [Amat, Ymat, lyapunovOp, matMul, matTranspose, Matrix.mul_apply]
  rwa [finiteVecNorm2_vec_eq_frobNorm n n Y, hLY,
    finiteVecNorm2_vec_eq_frobNorm n n (lyapunovOp n A Y)] at h

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient gives the Frobenius lower bound for the Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 <= lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    forall Y : Fin n -> Fin n -> Real,
      Real.sqrt lam * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  exact
    lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A (Real.sqrt lam)
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A hlam hEig)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    a uniform lower bound on the diagonal Lyapunov coefficient magnitudes
    `|a_i + a_j|` gives the concrete vectorized coefficient lower bound. -/
theorem lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge (n : Nat)
    (a : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) := by
  classical
  intro x
  let d : Prod (Fin n) (Fin n) -> Real := fun p => a p.2 + a p.1
  let Y : Matrix (Fin n) (Fin n) Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have hLY :
      Matrix.diagonal a * Y + Y * Matrix.transpose (Matrix.diagonal a) =
        fun i j => (a i + a j) * x (j, i) := by
    ext i j
    simp [Y, Matrix.mul_apply, Matrix.diagonal]
    ring
  have hmul :
      Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x =
        fun p => d p * x p := by
    have h := lyapunovVecCoeff_mulVec_vec n (Matrix.diagonal a) Y
    rw [hvecY, hLY] at h
    ext p
    simpa [d, Matrix.vec] using congrFun h p
  have hsquares :
      sigma ^ 2 * finiteVecNorm2Sq x <=
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    unfold finiteVecNorm2Sq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _hp
    have hleft : -|d p| <= sigma := by
      linarith [abs_nonneg (d p), hsigma]
    have hsq_abs : sigma ^ 2 <= |d p| ^ 2 := by
      exact sq_le_sq' hleft (by simpa [d] using hgap p.2 p.1)
    calc
      sigma ^ 2 * x p ^ 2 <= |d p| ^ 2 * x p ^ 2 :=
        mul_le_mul_of_nonneg_right hsq_abs (sq_nonneg (x p))
      _ = (d p * x p) ^ 2 := by
        rw [sq_abs]
        ring
  have hleft_sq :
      (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2Sq x := by
    rw [show (sigma * finiteVecNorm2 x) ^ 2 =
        sigma ^ 2 * finiteVecNorm2 x ^ 2 by ring,
      finiteVecNorm2_sq]
  have hright_sq :
      finiteVecNorm2
          (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) ^ 2 =
        finiteVecNorm2Sq (fun p : Prod (Fin n) (Fin n) => d p * x p) := by
    rw [hmul, finiteVecNorm2_sq]
  have hsq :
      (sigma * finiteVecNorm2 x) ^ 2 <=
        finiteVecNorm2
          (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) ^ 2 := by
    simpa [hleft_sq, hright_sq] using hsquares
  have hleft_nonneg : 0 <= sigma * finiteVecNorm2 x :=
    mul_nonneg hsigma (finiteVecNorm2_nonneg x)
  have hright_nonneg :
      0 <= finiteVecNorm2
        (Matrix.mulVec (lyapunovVecCoeff n (Matrix.diagonal a)) x) :=
    finiteVecNorm2_nonneg _
  have habs := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    a uniform lower bound on `|a_i + a_j|` gives a finite Gram-eigenvalue
    lower bound for the concrete vectorized Lyapunov coefficient. -/
theorem lyapunovVecCoeff_diagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real) (sigma : Real)
    (hsigma : 0 <= sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n (Matrix.diagonal a)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n (Matrix.diagonal a))) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (lyapunovVecCoeff n (Matrix.diagonal a)) hsigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    the concrete diagonal Lyapunov vec/Kronecker lower bound transfers to the
    Frobenius lower bound for the Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_diagonal_of_entrywise_abs_ge (n : Nat)
    (a : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (lyapunovOp n (Matrix.diagonal a) Y) := by
  exact
    lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n (Matrix.diagonal a) sigma
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    the structured `Psi` certificate follows from a positive lower bound on the
    printed Kronecker/vectorized Sylvester coefficient. -/
theorem sylvesterPsi_of_vecCoeff_sigmaMin_isPsiFirstOrderBound (n : Nat)
    (A B X : Fin n -> Fin n -> Real) (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x)) :
    SylvesterPsiFirstOrderBound n A B X alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma)) := by
  exact
    sylvesterPsi_of_sigmaMin_isPsiFirstOrderBound n
      A B X alpha beta gamma sigma halpha hbeta hgamma hsigma hX
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a positive
    lower bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_gram_eigenvalues
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma lam eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma
      (Real.sqrt lam) eps halpha hbeta hgamma
      (Real.sqrt_pos.mpr hlam) heps hX
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hlam) hEig)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    diagonal case: source-shaped first-order relative perturbation bound from
    the concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_24_structured_condition_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hsigma) hgap)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    Frobenius first-order Sylvester perturbation bound from a positive lower
    bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    relative Sylvester perturbation bound from a positive lower bound on the
    concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_sigmaMin (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    Frobenius first-order Sylvester perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / Real.sqrt lam) *
        ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    relative Sylvester perturbation bound from a finite Gram-eigenvalue lower
    bound for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (Real.sqrt lam) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    diagonal case: Frobenius first-order Sylvester perturbation bound from the
    concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    diagonal case: relative Sylvester perturbation bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n (Matrix.diagonal a) (Matrix.diagonal b)
        X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a posteriori error-residual bound from a positive lower bound on the
    concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    relative a posteriori error-residual bound from a positive lower bound on
    the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a posteriori error-residual bound from a finite Gram-eigenvalue lower bound
    for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    relative a posteriori error-residual bound from a finite Gram-eigenvalue
    lower bound for the concrete vectorized Sylvester coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / Real.sqrt lam) *
        frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hLam) hEig)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: a posteriori error-residual bound from the concrete diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      C X Xhat sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: relative a posteriori error-residual bound from the concrete
    diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_aposteriori_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      C X Xhat sigma hSigma
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hSigma) hgap)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    the Lyapunov condition-number certificate follows from a positive lower
    bound on the printed vectorized Lyapunov coefficient. -/
theorem lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
    (n : Nat) (A X : Fin n -> Fin n -> Real) (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x)) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) := by
  exact
    lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX
      (lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma lam eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma (Real.sqrt lam) eps
      halpha hgamma (Real.sqrt_pos.mpr hlam) heps hX
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A
        (le_of_lt hlam) hEig)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-shaped Lyapunov first-order perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_27_lyapunov_condition_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)
      hDeltaA hDeltaC hLin

end LeanFpAnalysis.FP
