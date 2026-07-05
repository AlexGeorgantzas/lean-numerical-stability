-- Algorithms/Sylvester/Higham16VecNorm.lean
--
-- Vec/Frobenius norm bridges for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.

import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16PerturbationSigmaMin
import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16PsiSigmaMin
import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16LyapunovSigmaMin
import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16

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

/-- A concrete left inverse with a finite operator-2 bound gives the inverse
    action bound on the original product-index matrix.  This is a reusable
    bridge from exact inverse certificates to the `P`-coefficient route, without
    assuming a sigma-min theorem as a hypothesis. -/
theorem finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Pinv : Matrix ι ι Real) {M : Real}
    (hLeft : Pinv * P = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : ι -> Real,
      finiteVecNorm2 x <= M * finiteVecNorm2 (Matrix.mulVec P x) := by
  classical
  have hLeftFinite : finiteMatMul Pinv P = finiteIdMatrix := by
    ext i j
    have hentry :=
      congrArg (fun Q : Matrix ι ι Real => Q i j) hLeft
    simpa [finiteMatMul, finiteIdMatrix, Matrix.mul_apply] using hentry
  intro x
  have hPx : Matrix.mulVec P x = finiteMatVec P x := by
    ext i
    rfl
  have hrecover :
      finiteMatVec Pinv (Matrix.mulVec P x) = x := by
    calc
      finiteMatVec Pinv (Matrix.mulVec P x)
          = finiteMatVec Pinv (finiteMatVec P x) := by rw [hPx]
      _ = finiteMatVec (finiteMatMul Pinv P) x := by
          rw [finiteMatVec_finiteMatMul]
      _ = finiteMatVec finiteIdMatrix x := by rw [hLeftFinite]
      _ = x := finiteMatVec_finiteIdMatrix x
  have hbound := hPinv (Matrix.mulVec P x)
  simpa [hrecover] using hbound

/-- A concrete left inverse with operator-2 radius `M` gives the coefficient
    sigma-min lower bound with `sigma = 1 / M`.  This is the product-index
    route needed once an arbitrary nondiagonal vec/Kronecker inverse has been
    constructed and norm-bounded. -/
theorem finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Pinv : Matrix ι ι Real) {M : Real} (hM : 0 < M)
    (hLeft : Pinv * P = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : ι -> Real,
      (1 / M) * finiteVecNorm2 x <= finiteVecNorm2 (Matrix.mulVec P x) := by
  intro x
  have hinvBound :=
    finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
      P Pinv hLeft hPinv x
  have hcomm :
      finiteVecNorm2 x <= finiteVecNorm2 (Matrix.mulVec P x) * M := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hinvBound
  have hdiv : finiteVecNorm2 x / M <= finiteVecNorm2 (Matrix.mulVec P x) :=
    (div_le_iff₀ hM).mpr hcomm
  simpa [one_div, div_eq_inv_mul] using hdiv

/-- A concrete left inverse with operator-2 radius `M` gives a lower bound
    `(1 / M)^2` on every eigenvalue of the finite Gram matrix `P^T P`. -/
theorem finiteMatrixGram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Pinv : Matrix ι ι Real) {M : Real} (hM : 0 < M)
    (hLeft : Pinv * P = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall a : ι,
      (1 / M) ^ 2 <= finiteHermitianEigenvalues (finiteMatrixGram P)
        (isSymmetricFiniteMatrix_finiteMatrixGram P) a := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound P
      (by positivity)
      (finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
        P Pinv hM hLeft hPinv)

/-- A concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient gives its sigma-min lower-bound route directly,
    without assuming the target coefficient lower-bound theorem. -/
theorem sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      (1 / M) * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  exact
    finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
      (sylvesterVecCoeff n n A B) Pinv hM hLeft hPinv

/-- A concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient gives the corresponding finite Gram eigenvalue
    lower bound. -/
theorem sylvesterVecCoeff_gram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall p : Prod (Fin n) (Fin n),
      (1 / M) ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
      (sylvesterVecCoeff n n A B) Pinv hM hLeft hPinv

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives its sigma-min lower-bound route directly,
    without assuming the target coefficient lower-bound theorem. -/
theorem lyapunovVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      (1 / M) * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  exact
    finiteMatrix_sigmaMin_of_left_inverse_finiteOpNorm2Le
      (lyapunovVecCoeff n A) Pinv hM hLeft hPinv

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives the corresponding finite Gram eigenvalue
    lower bound. -/
theorem lyapunovVecCoeff_gram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall p : Prod (Fin n) (Fin n),
      (1 / M) ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_left_inverse_finiteOpNorm2Le
      (lyapunovVecCoeff n A) Pinv hM hLeft hPinv

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

/-- A concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient gives the inverse-operator bound used by the
    structured condition-number surface. -/
theorem sylvesterInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real}
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SylvesterInverseOpBound n A B M := by
  intro Y
  have h :=
    finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
      (sylvesterVecCoeff n n A B) Pinv hLeft hPinv (Matrix.vec Y)
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

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    a positive Gram-eigenvalue lower bound for the concrete vectorized
    Sylvester coefficient gives a `SepLowerBound` certificate. -/
theorem SepLowerBound_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    SepLowerBound n A B (Real.sqrt lam) := by
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B (Real.sqrt lam)
      (Real.sqrt_pos.mpr hlam)
      (sylvesterOp_sigmaMin_of_vecCoeff_gram_eigenvalues n A B
        (le_of_lt hlam) hEig)

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a positive Gram-eigenvalue lower bound for the
    concrete vectorized Sylvester coefficient lower-bounds the exact `sep`
    infimum. -/
theorem sylvesterSepInf_ge_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A B : Fin n -> Fin n -> Real) {lam : Real}
    (hn : 0 < n) (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p) :
    Real.sqrt lam <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B (Real.sqrt lam)
      (SepLowerBound_of_vecCoeff_gram_eigenvalues n A B hlam hEig) hn

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    a supplied concrete left inverse for the printed vec/Kronecker Sylvester
    coefficient gives a `SepLowerBound` certificate. -/
theorem SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SepLowerBound n A B (1 / M) := by
  have hCoeff :=
    sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv
  have hOp :
      forall Y : Fin n -> Fin n -> Real,
        (1 / M) * frobNorm Y <= frobNorm (sylvesterOp n A B Y) :=
    sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B (1 / M) hCoeff
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B (1 / M)
      (one_div_pos.mpr hM) hOp

/-- Higham, 2nd ed., Chapter 16.1 and equations (16.23)-(16.26):
    in positive dimension, a supplied concrete left inverse for the printed
    vec/Kronecker Sylvester coefficient lower-bounds the exact `sep` infimum. -/
theorem sylvesterSepInf_ge_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hn : 0 < n) (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    (1 / M) <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B (1 / M)
      (SepLowerBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hn

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

/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    a uniform lower bound on the diagonal coordinate gaps `|a_i - b_j|`
    gives the same Frobenius lower bound for the original Sylvester operator
    after the supplied orthogonal coordinate transformations. -/
theorem sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  intro Y
  let Yc : Fin n -> Fin n -> Real :=
    rectMatMul (matTranspose U) (rectMatMul Y V)
  have hYnorm : frobNorm Yc = frobNorm Y := by
    dsimp [Yc]
    calc
      frobNorm (rectMatMul (matTranspose U) (rectMatMul Y V))
          = frobNorm (rectMatMul Y V) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_left (matTranspose U)
                (rectMatMul Y V) hU.transpose)
      _ = frobNorm Y := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_right Y V hV)
  have hYexpand :
      rectMatMul U (rectMatMul Yc (matTranspose V)) = Y := by
    dsimp [Yc]
    exact rectMatMul_schur_coords_expand U V Y hU hV
  have htrans :
      sylvesterOpRect n n A B Y =
        rectMatMul U
          (rectMatMul
            (sylvesterOpRect n n (Matrix.diagonal a)
              (Matrix.diagonal b) Yc)
            (matTranspose V)) := by
    have h :=
      sylvester_schur_transform_identity n n
        U (Matrix.diagonal a) A V (Matrix.diagonal b) B Yc
        hU hV hA hB
    rwa [hYexpand] at h
  have hOut :
      frobNorm (sylvesterOp n A B Y) =
        frobNorm (sylvesterOp n (Matrix.diagonal a)
          (Matrix.diagonal b) Yc) := by
    rw [<- sylvesterOpRect_square_eq_sylvesterOp n A B Y, htrans]
    calc
      frobNorm
          (rectMatMul U
            (rectMatMul
              (sylvesterOpRect n n (Matrix.diagonal a)
                (Matrix.diagonal b) Yc)
              (matTranspose V)))
          = frobNorm
              (rectMatMul
                (sylvesterOpRect n n (Matrix.diagonal a)
                  (Matrix.diagonal b) Yc)
                (matTranspose V)) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_left U
                (rectMatMul
                  (sylvesterOpRect n n (Matrix.diagonal a)
                    (Matrix.diagonal b) Yc)
                  (matTranspose V)) hU)
      _ = frobNorm
            (sylvesterOpRect n n (Matrix.diagonal a)
              (Matrix.diagonal b) Yc) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_right
                (sylvesterOpRect n n (Matrix.diagonal a)
                  (Matrix.diagonal b) Yc)
                (matTranspose V) hV.transpose)
      _ = frobNorm (sylvesterOp n (Matrix.diagonal a)
            (Matrix.diagonal b) Yc) := by
            rw [sylvesterOpRect_square_eq_sylvesterOp]
  have hdiag :=
    sylvesterOp_sigmaMin_diagonal_of_entrywise_abs_ge n
      a b sigma hsigma hgap Yc
  calc
    sigma * frobNorm Y = sigma * frobNorm Yc := by
      rw [hYnorm]
    _ <= frobNorm (sylvesterOp n (Matrix.diagonal a)
          (Matrix.diagonal b) Yc) := hdiag
    _ = frobNorm (sylvesterOp n A B Y) := hOut.symm

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    the corresponding product-index vec/Kronecker coefficient inherits the
    same sigma lower bound from the Schur-coordinate diagonal gap. -/
theorem sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  intro x
  let Y : Fin n -> Fin n -> Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have h :=
    sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap Y
  rw [<- hvecY]
  rw [sylvesterVecCoeff_mulVec_vec n n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y,
    sylvesterOpRect_square_eq_sylvesterOp n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n (sylvesterOp n A B Y)]
  exact h

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    a supplied Schur-coordinate gap gives a finite Gram-eigenvalue lower
    bound for the original vec/Kronecker Sylvester coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (sylvesterVecCoeff n n A B) (le_of_lt hsigma)
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    a uniform Schur-coordinate gap gives a `SepLowerBound` certificate for
    the original Sylvester operator. -/
theorem SepLowerBound_schurDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    SepLowerBound n A B sigma := by
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hsigma
      (sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    a uniform Schur-coordinate gap is below the exact infimum model of
    `sep(A,B)` whenever the feasible ratio set is nonempty. -/
theorem sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hne : (sylvesterSepRatios n A B).Nonempty) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n A B sigma
      (SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hne

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    in positive dimension, a uniform Schur-coordinate gap is below the exact
    infimum model of `sep(A,B)`. -/
theorem sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hn : 0 < n) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B sigma
      (SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hn

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    a uniform spectral-coordinate sum gap gives a `SepLowerBound` certificate
    for the Sylvester special case `sep(A,-A^T)`. -/
theorem SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    SepLowerBound n A (fun i j => -matTranspose A i j) sigma := by
  have hnegAT :
      (fun i j => -matTranspose A i j) =
        rectMatMul U
          (rectMatMul (Matrix.diagonal (fun i : Fin n => -a i))
            (matTranspose U)) := by
    rw [hA]
    ext i j
    simp [rectMatMul, matTranspose, Matrix.diagonal]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hgapSylv :
      forall i j, sigma <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hgap i j
  exact
    SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
      U A U (fun i j => -matTranspose A i j)
      a (fun i : Fin n => -a i) sigma hU hU hA hnegAT
      hsigma hgapSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    the spectral-coordinate sum gap is below the exact infimum model of
    `sep(A,-A^T)` whenever the feasible ratio set is nonempty. -/
theorem sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hne : (sylvesterSepRatios n A
      (fun i j => -matTranspose A i j)).Nonempty) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    in positive dimension, the spectral-coordinate sum gap is below the exact
    infimum model of `sep(A,-A^T)`. -/
theorem sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge_of_pos_dim
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hn : 0 < n) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hn

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

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives the Lyapunov operator sigma-min lower
    bound. -/
theorem lyapunovOp_sigmaMin_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    forall Y : Fin n -> Fin n -> Real,
      (1 / M) * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  exact
    lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A (1 / M)
      (lyapunovVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives a `SepLowerBound` certificate for
    `sep(A, -A^T)`. -/
theorem SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SepLowerBound n A (fun i j => -matTranspose A i j) (1 / M) := by
  have hOp :=
    lyapunovOp_sigmaMin_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A Pinv hM hLeft hPinv
  have hSylv : forall Y : Fin n -> Fin n -> Real,
      (1 / M) * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hOp Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A
      (fun i j => -matTranspose A i j) (1 / M)
      (one_div_pos.mpr hM) hSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient give an exact-infimum lower bound for
    `sep(A, -A^T)` in positive dimension. -/
theorem sylvesterSepInf_lyapunov_ge_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hn : 0 < n) (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    (1 / M) <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) (1 / M)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      hn

/-- A concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient gives the inverse-operator bound used by the
    Lyapunov condition-number surface. -/
theorem lyapunovInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A : Fin n -> Fin n -> Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real}
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    LyapunovInverseOpBound n A M := by
  intro Y
  have h :=
    finiteVecNorm2_le_mul_mulVec_of_left_inverse_finiteOpNorm2Le
      (lyapunovVecCoeff n A) Pinv hLeft hPinv (Matrix.vec Y)
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

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    a supplied Gram-eigenvalue lower bound for the concrete vectorized
    Lyapunov coefficient gives a `SepLowerBound` certificate for
    `sep(A, -A^T)`. -/
theorem SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues (n : Nat)
    (A : Fin n -> Fin n -> Real) {lam : Real}
    (hlam : 0 <= lam) (hsqrt : 0 < Real.sqrt lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    SepLowerBound n A (fun i j => -matTranspose A i j) (Real.sqrt lam) := by
  have hOp :=
    lyapunovOp_sigmaMin_of_vecCoeff_gram_eigenvalues n A hlam hEig
  have hSylv : forall Y : Fin n -> Fin n -> Real,
      Real.sqrt lam * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hOp Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A
      (fun i j => -matTranspose A i j) (Real.sqrt lam)
      hsqrt hSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    in positive dimension, a supplied Gram-eigenvalue lower bound for the
    concrete vectorized Lyapunov coefficient lower-bounds the exact
    `sep(A, -A^T)` infimum. -/
theorem sylvesterSepInf_lyapunov_ge_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A : Fin n -> Fin n -> Real) {lam : Real}
    (hn : 0 < n) (hlam : 0 <= lam) (hsqrt : 0 < Real.sqrt lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    Real.sqrt lam <=
      sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) (Real.sqrt lam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A hlam hsqrt hEig)
      hn

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

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    if `A = U diag(a) U^T`, then a uniform lower bound on
    `|a_i + a_j|` gives the same Frobenius lower bound for the original
    Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_spectralDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  have hnegAT :
      (fun i j => -matTranspose A i j) =
        rectMatMul U
          (rectMatMul (Matrix.diagonal (fun i : Fin n => -a i))
            (matTranspose U)) := by
    rw [hA]
    ext i j
    simp [rectMatMul, matTranspose, Matrix.diagonal]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hgapSylv :
      forall i j, sigma <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hgap i j
  intro Y
  have h :=
    sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
      U A U (fun i j => -matTranspose A i j)
      a (fun i : Fin n => -a i) sigma hU hU hA hnegAT
      hsigma hgapSylv Y
  rwa [<- lyapunovOp_eq_sylvesterOp n A Y] at h

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    the original-coordinate Lyapunov vec/Kronecker coefficient inherits the
    same sigma lower bound from the spectral-coordinate diagonal sums. -/
theorem lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  intro x
  let Y : Matrix (Fin n) (Fin n) Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have hOp :=
    lyapunovOp_sigmaMin_spectralDiagonal_of_entrywise_abs_ge n
      U A a sigma hU hA hsigma hgap Y
  let Amat : Matrix (Fin n) (Fin n) Real := A
  let Ymat : Matrix (Fin n) (Fin n) Real := Y
  have hLY :
      Amat * Ymat + Ymat * Matrix.transpose Amat = lyapunovOp n A Y := by
    ext i j
    simp [Amat, Ymat, Y, lyapunovOp, matMul, matTranspose, Matrix.mul_apply]
  rw [<- hvecY]
  rw [lyapunovVecCoeff_mulVec_vec n A Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y, hLY,
    finiteVecNorm2_vec_eq_frobNorm n n (lyapunovOp n A Y)]
  exact hOp

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    a spectral-coordinate gap gives a finite Gram-eigenvalue lower bound for
    the original Lyapunov vec/Kronecker coefficient. -/
theorem lyapunovVecCoeff_spectralDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (lyapunovVecCoeff n A) (le_of_lt hsigma)
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)

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
    a concrete left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient instantiates the structured `Psi` certificate
    directly, without first postulating a sigma-min lower bound. -/
theorem sylvesterPsi_of_vecCoeff_left_inverse_finiteOpNorm2Le_isPsiFirstOrderBound
    (n : Nat)
    (A B X : Fin n -> Fin n -> Real) (alpha beta gamma M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    SylvesterPsiFirstOrderBound n A B X alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma M) := by
  exact
    sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound n
      A B X alpha beta gamma M halpha hbeta hgamma hM hX
      (sylvesterInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A B Pinv hLeft hPinv)

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
    source-shaped first-order relative perturbation bound from a concrete
    left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma M * eps := by
  have hPsi :=
    sylvesterPsi_of_vecCoeff_left_inverse_finiteOpNorm2Le_isPsiFirstOrderBound
      n A B X alpha beta gamma M Pinv halpha hbeta hgamma hM hX hLeft hPinv
  have hPsi_nonneg :
      0 <= sylvesterPsi_of_inverseOpBound n X alpha beta gamma M := by
    unfold sylvesterPsi_of_inverseOpBound
    have hsum : 0 <= alpha + beta :=
      add_nonneg (le_of_lt halpha) (le_of_lt hbeta)
    have hprod : 0 <= (alpha + beta) * frobNorm X :=
      mul_nonneg hsum (le_of_lt hX)
    have hnum : 0 <= (alpha + beta) * frobNorm X + gamma :=
      add_nonneg hprod (le_of_lt hgamma)
    exact div_nonneg (mul_nonneg hM hnum) (le_of_lt hX)
  exact
    sylvester_relative_first_order_bound_of_psi n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma M) eps
      hPsi hX hPsi_nonneg halpha hbeta hgamma heps
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

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    supplied orthogonal diagonal Schur-coordinate case:
    source-shaped first-order relative perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_24_structured_condition_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
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
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
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
    Frobenius first-order Sylvester perturbation bound from a concrete left
    inverse and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
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
      M * ((alpha + beta) * frobNorm X + gamma) * eps := by
  have h :=
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    relative Sylvester perturbation bound from a concrete left inverse and
    operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
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
      condSylvester n A B X alpha beta gamma (1 / M) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
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

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    supplied orthogonal diagonal Schur-coordinate case:
    Frobenius first-order Sylvester perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
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
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    supplied orthogonal diagonal Schur-coordinate case:
    relative Sylvester perturbation bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
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
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
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
    a posteriori error-residual bound from a concrete left inverse and
    operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      M * frobNorm (sylvesterResidual n A B C Xhat) := by
  have h :=
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hExact hE_ne
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    relative a posteriori error-residual bound from a concrete left inverse
    and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_aposteriori_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A B C X Xhat : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      (M * frobNorm (sylvesterResidual n A B C Xhat)) / frobNorm X := by
  have h :=
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat (1 / M) (one_div_pos.mpr hM)
      (sylvesterVecCoeff_sigmaMin_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hExact hE_ne hX_pos
  simpa [one_div] using h

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

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    supplied orthogonal diagonal Schur-coordinate case:
    a posteriori error-residual bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    supplied orthogonal diagonal Schur-coordinate case:
    relative a posteriori error-residual bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_aposteriori_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_vecCoeff_sigmaMin n
      A B C X Xhat sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
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
    a finite Gram-eigenvalue lower bound for the printed Lyapunov vec/Kronecker
    coefficient instantiates the Lyapunov condition certificate with
    inverse-operator constant `1 / sqrt(lam)`. -/
theorem lyapunovCond_of_vecCoeff_gram_eigenvalues_isLyapunovConditionFirstOrderBound
    (n : Nat) (A X : Fin n -> Fin n -> Real) (alpha gamma lam : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hlam : 0 < lam)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma
        (1 / Real.sqrt lam)) := by
  exact
    lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
      n A X alpha gamma (Real.sqrt lam)
      halpha hgamma (Real.sqrt_pos.mpr hlam) hX
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A
        (le_of_lt hlam) hEig)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    a concrete left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient instantiates the Lyapunov condition certificate
    directly, without first postulating a sigma-min lower bound. -/
theorem lyapunovCond_of_vecCoeff_left_inverse_finiteOpNorm2Le_isLyapunovConditionFirstOrderBound
    (n : Nat) (A X : Fin n -> Fin n -> Real) (alpha gamma M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M) :
    LyapunovConditionFirstOrderBound n A X alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma M) := by
  exact
    lyapunovCond_of_inverseOpBound_isLyapunovConditionFirstOrderBound n
      A X alpha gamma M halpha hgamma hM hX
      (lyapunovInverseOpBound_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hLeft hPinv)

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
    Frobenius first-order Lyapunov perturbation bound from a concrete left
    inverse and operator-2 radius for the printed Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma M * frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_vecCoeff_left_inverse_finiteOpNorm2Le_isLyapunovConditionFirstOrderBound
      n A X alpha gamma M Pinv halpha hgamma hM hX hLeft hPinv)
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    relative Lyapunov first-order perturbation bound from a concrete left
    inverse and operator-2 radius for the printed Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma M * eps := by
  have hCond :=
    lyapunovCond_of_vecCoeff_left_inverse_finiteOpNorm2Le_isLyapunovConditionFirstOrderBound
      n A X alpha gamma M Pinv halpha hgamma hM hX hLeft hPinv
  have hCond_nonneg :
      0 <= lyapunovCond_of_inverseOpBound n X alpha gamma M := by
    unfold lyapunovCond_of_inverseOpBound
    have htwo_alpha : 0 <= 2 * alpha :=
      mul_nonneg (by norm_num) (le_of_lt halpha)
    have hprod : 0 <= 2 * alpha * frobNorm X :=
      mul_nonneg htwo_alpha (le_of_lt hX)
    have hnum : 0 <= 2 * alpha * frobNorm X + gamma :=
      add_nonneg hprod (le_of_lt hgamma)
    exact div_nonneg (mul_nonneg hM hnum) (le_of_lt hX)
  exact
    lyapunov_relative_first_order_bound_of_condition n
      A X DeltaA DeltaC DeltaX alpha gamma
      (lyapunovCond_of_inverseOpBound n X alpha gamma M) eps
      hCond hX hCond_nonneg halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a concrete
    left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma M * eps := by
  exact
    lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A X DeltaA DeltaC DeltaX alpha gamma M eps Pinv
      halpha hgamma hM heps hX hLeft hPinv
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a concrete left inverse and
    operator-2 radius for the printed Lyapunov vec/Kronecker coefficient. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      M * (2 * alpha * frobNorm X + gamma) * eps := by
  have h :=
    lyapunov_perturbation_bound n A X DeltaA DeltaC DeltaX
      (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hDeltaX_ne
  simpa [one_div] using h

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a concrete left inverse and
    operator-2 radius for the printed Lyapunov vec/Kronecker coefficient. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma (1 / M) * eps := by
  have hDeltaB : frobNorm (fun i j => -matTranspose DeltaA i j) <= eps * alpha := by
    rw [show (fun i j => -matTranspose DeltaA i j) =
        (fun i j => -(matTranspose DeltaA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hDeltaA
  exact
    sylvester_relative_perturbation n A
      (fun i j => -matTranspose A i j) X DeltaA
      (fun i j => -matTranspose DeltaA i j) DeltaC DeltaX
      (1 / M) (one_div_pos.mpr hM)
      (SepLowerBound_lyapunov_of_vecCoeff_left_inverse_finiteOpNorm2Le
        n A Pinv hM hLeft hPinv)
      alpha alpha gamma eps halpha halpha hgamma heps
      hDeltaA hDeltaB hDeltaC hLin hDeltaX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    Frobenius Lyapunov perturbation bound from a supplied finite
    Gram-eigenvalue lower bound for the concrete Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_perturbation_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0)) :
    frobNorm DeltaX <=
      (1 / Real.sqrt lam) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound n A X DeltaA DeltaC DeltaX
      (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hDeltaX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    relative Lyapunov perturbation bound from a supplied finite
    Gram-eigenvalue lower bound for the concrete Lyapunov vec/Kronecker
    coefficient. -/
theorem lyapunov_relative_perturbation_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hDeltaX_ne : Not (frobNormSq DeltaX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma (Real.sqrt lam) * eps := by
  have hDeltaB : frobNorm (fun i j => -matTranspose DeltaA i j) <= eps * alpha := by
    rw [show (fun i j => -matTranspose DeltaA i j) =
        (fun i j => -(matTranspose DeltaA) i j) from by ext i j; rfl]
    rw [frobNorm_neg, frobNorm_transpose]
    exact hDeltaA
  exact
    sylvester_relative_perturbation n A
      (fun i j => -matTranspose A i j) X DeltaA
      (fun i j => -matTranspose DeltaA i j) DeltaC DeltaX
      (Real.sqrt lam) (Real.sqrt_pos.mpr hLam)
      (SepLowerBound_lyapunov_of_vecCoeff_gram_eigenvalues
        n A (le_of_lt hLam) (Real.sqrt_pos.mpr hLam) hEig)
      alpha alpha gamma eps halpha halpha hgamma heps
      hDeltaA hDeltaB hDeltaC hLin hDeltaX_ne hX_ne hX_pos

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

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-shaped Lyapunov first-order perturbation bound from the concrete
    spectral-diagonal Lyapunov vec/Kronecker coefficient lower-bound
    certificate. -/
theorem H16_eq16_27_lyapunov_condition_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
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
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-shaped Lyapunov first-order perturbation bound from the
    spectral-coordinate `sep(A,-A^T)` lower-bound certificate. -/
theorem H16_eq16_27_lyapunov_condition_spectralDiagonal_of_sep_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
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
    H16_eq16_27_lyapunov_condition_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hDeltaA hDeltaC hLin

end LeanFpAnalysis.FP
